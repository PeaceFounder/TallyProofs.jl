using CryptoGroups: Group, order, octet
using CryptoGroups.Utils: int2octet!, octet2int, @check
using CryptoPRG: HashSpec
using CryptoPRG.Verificatum: PRG
using SigmaProofs: Proposition, Proof, Verifier, Simulator
using SigmaProofs.LogProofs: SchnorrProof, LogKnowledge
using SigmaProofs.Parser: Tree, encode
using SigmaProofs.Verificatum: generator_basis, GeneratorBasis
import SigmaProofs: prove, verify, proof_type

using .HMACWatermark: apply_watermark
import .HMACWatermark: verify_watermark

struct Signature{G <: Group}
    pbkey::G
    proof::SchnorrProof
end

function sign(message::Vector{UInt8}, g::G, key::BigInt) where G <: Group

    # This is temporary
    # we should however try to implement Scnorr signatures here according to specification
    verifier = ProtocolSpec(; g)
    
    pbkey = g^key
    
    proof = prove(LogKnowledge(g, pbkey), verifier, key; suffix = message)

    return Signature(pbkey, proof)
end

function verify(message::Vector{UInt8}, g::G, signature::Signature) where G <: Group

    verifier = ProtocolSpec(; g)

    return verify(LogKnowledge(g, signature.pbkey), signature.proof, verifier; suffix = message)
end

struct Signer{G <: Group}
    g::G
    key::BigInt
end

struct DecoyOppening
    θ::BigInt # Could be reused to mark revotes
    λ::BigInt
    selection::BigInt
end

DecoyOppening() = DecoyOppening(0, 0, 0)

function DecoyOppening(selection::Integer, range::UnitRange; roprg = gen_roprg())

    θ = rand(roprg(:θ), range)
    λ = rand(roprg(:λ), range)

    return DecoyOppening(θ, λ, selection)
end

Base.zero(::Type{DecoyOppening}) = DecoyOppening(0, 0, 0)
Base.zero(::DecoyOppening) = zero(DecoyOppening)

function VoteOppening(vote::DecoyOppening, range::UnitRange; roprg = gen_roprg())

    (; θ, λ, selection) = vote
    α = rand(roprg(:α), range)
    β = rand(roprg(:β), range)
    γ = 0

    tracker = TrackerOppening(α, λ, β, θ)
    return VoteOppening(tracker, selection, γ)
end


Base.:(==)(x::DecoyOppening, y::DecoyOppening) = x.θ == y.θ && x.λ == y.λ && x.selection == y.selection

struct Proposal{G <: Group} 
    spec::Vector{UInt8} # hash of other set of parameters
    g::G
    collector::G
    basis::GeneratorSetup{G} # new
    watermark_nbits::Int
    token_max::Int # 
    encrypt_spec::EncryptSpec
    hasher::HashSpec
end

function Proposal(g::G, collector::G, verifier::Verifier; spec = UInt8[], watermark_nbits::Int=4, token_max::Int=9999_9999, encrypt_spec::EncryptSpec=AES256_SHA256(), hasher = verifier.prghash) where G <: Group
    
    # For safety reasons we shall derive both generators independently and not reuse g
    h, d = generator_basis(verifier, G, 2)
    basis = GeneratorSetup(h, d)
    
    return Proposal(spec, g, collector, basis, watermark_nbits, token_max, encrypt_spec, hasher)
end

struct OverrideMask
    pin::Int
    tracker::BigInt # nothing is when not overriden
end

struct DecoyCredential
    pin::Int
    seed::Vector{UInt8} # in a sense it is also a credential
end

function compute_tracker_preimage(proposal::Proposal{G}, seed::Vector{UInt8}) where G <: Group
    
    prg = PRG(proposal.hasher, [seed; encode(Tree(proposal))])
    θ, λ = rand(prg, 2:order(G) - 1, 2)

    return θ, λ
end

function compute_tracker(proposal::Proposal, seed::Vector{UInt8}, token::Integer)

    θ, λ = compute_tracker_preimage(proposal, seed)

    T = tracker(θ, λ, token, order(proposal.g))

    return proposal.hasher(int2octet(T))[1:8] |> octet2int
end

function DecoyOppening(proposal::Proposal{G}, selection::Integer, seed::Vector{UInt8}) where G <: Group
    θ, λ = compute_tracker_preimage(proposal, seed)
    return DecoyOppening(θ, λ, selection)
end


struct VotingCalculator{G} # More preciselly it would be VotingCalculatorInstance
    id::Vector{UInt8}
    w::G
    # π_w

    proposal::Proposal{G}

    verifier::Verifier
    hasher::HashSpec # We shall also take it from the verifier

    supersession::SupersessionCalculator{G}

    pseudonym::G # computed from a generator
    key::BigInt

    # We shall keep the tracker constant for simplicity
    pin::Int # Pin code for authetification
    tracker::TrackerOppening

    current_selection::Ref{BigInt}
    trigger_token::Ref{Union{Int, Nothing}}
    
    override_mask::Vector{OverrideMask}
    decoys::Vector{DecoyCredential}
end

function VotingCalculator(id::AbstractVector{UInt8}, proposal::Proposal{G}, verifier::Verifier, key::Integer, pin::Int; roprg = gen_roprg(), history_width::Int = 5) where G <: Group

    id = convert(Vector{UInt8}, id) 
    hasher = verifier.prghash # the verifier could implement hasher method

    (; g) = proposal
    (; h) = proposal.basis

    pseudonym = g^key

    tracker = TrackerOppening(2:order(G)-1; roprg)

    (Q, R) = commitment(tracker, proposal.basis)
    h_QR = hasher([octet(Q); octet(R)])

    w0 = map2generator(pseudonym, hasher)
    w = w0^key

    I = hasher([octet(w); id])

    u = map2generator(pseudonym, h_QR, I, hasher)
    sup_calc = SupersessionCalculator(h, u, verifier; history_width, roprg)

    return VotingCalculator(id, w, proposal, verifier, hasher, sup_calc, pseudonym, key |> BigInt, pin, tracker, Ref{BigInt}(0), Ref{Union{Int, Nothing}}(nothing), OverrideMask[], DecoyCredential[])
end

# Installs override tracker for VotingCalculator for override_pin code. Leaves verification to verifier_pin
# Override mask is a vector and we simply need to find the last element from the list
# The pin at which it is authorized is where the tracker would be overriden
function install_decoy_tracker!(calc::VotingCalculator, tracker::BigInt, authorizing_pin::Int)

    if authorizing_pin == calc.pin || authorizing_pin in (i.pin for i in calc.decoys)
        push!(calc.override_mask, OverrideMask(authorizing_pin, tracker))
    else
        error("Incorrect pin code")
    end
end

# in case it fails it is possible to repeat the process
function create_decoy_credential!(calc::VotingCalculator, fake_pin::Int, authorizing_pin::Int; roprg = gen_roprg())
    
    if authorizing_pin == calc.pin || authorizing_pin in (i.pin for i in decoys)

        seed = roprg(:seed)[1:32]
        credential = DecoyCredential(fake_pin, seed)

        push!(calc.decoys, credential)

        return seed
    else
        error("Incorrect pin code")
    end
end

function tracker_challenge(ux::G, token::Integer, hasher::HashSpec) where G <: Group

    error("xfdsf")
    return token
end

function verify_watermark(proposal::Proposal{G}, ux::G, token::Integer, hasher::HashSpec) where G <: Group
    
    (; token_max, watermark_nbits) = proposal

    nbits = ndigits(token_max, base=2) - 1
    offset = token_max - 2^nbits
    return verify_watermark(token - offset, nbits, octet(ux), hasher; num_positions = watermark_nbits)    
end

function compute_tracker(voter::VotingCalculator, token::Integer, pin::Int; reset_trigger_token::Bool = false)

    (; hasher) = voter
    (Q, R) = commitment(voter.tracker, voter.proposal.basis)

    if (isnothing(voter.trigger_token[]) || reset_trigger_token) && verify_watermark(voter.proposal, Q, token, hasher)
        voter.trigger_token[] = token
    end

    # The computation is always present in spite if it is even to be superseeded by the mask
    if voter.pin == pin
        (; θ, λ) = voter.tracker
    else

        N = findlast(x -> x.pin == pin, voter.decoys)

        if isnothing(N)
            error("Incoreect PIN code")
        else
            (; seed) = voter.decoys[N]
            θ, λ = compute_tracker_preimage(voter.proposal, seed)
        end

    end

    t = tracker(θ, λ, token, order(voter.proposal.g))

    M = findlast(x -> x.pin == pin, voter.override_mask)

    if voter.trigger_token[] == token && !isnothing(M)
        return voter.override_mask[M].tracker 
    else
        return hasher(int2octet(t))[1:8] |> octet2int
    end
end

struct SignedVoteCommitment{G <: Group}
    proposal::Vector{UInt8} # hash
    ux::G
    commitment::VoteCommitment{G} # This one is derivable
    I::Vector{UInt8}
    pok::SchnorrProof{G}
    signature::Signature{G}
end

#function isconsistent(row::SignedVoteCommitment{G}, g::G, hasher::HashSpec, verifier::Verifier) where G <: Group
#end

struct CastOppening{G <: Group}
    β::BigInt # For supersession
    history::Vector{BigInt}
    commitment::SignedVoteCommitment{G}
    oppening::VoteOppening # Can be further encrypted in a threshold decryption ceremony if one wishes to have that for fairness
    decoy::DecoyOppening
end

function SignedVoteCommitment(proposal::Vector{UInt8}, ux::G, commitment::VoteCommitment{G}, I::Vector{UInt8}, pok::SchnorrProof, signer::Signer{G}) where G <: Group

    msg = (proposal, ux, commitment.V)
    internal_signature = sign(encode(Tree(msg)), signer.g, signer.key)

    return SignedVoteCommitment(proposal, ux, commitment, I, pok, internal_signature)
end

function verify(vote::SignedVoteCommitment{G}, g::G) where G <: Group

    (; proposal, commitment, ux) = vote
    msg = (proposal, ux, commitment.V)
    
    return verify(encode(Tree(msg)), g, vote.signature)
end


struct Vote{G}
    proposal::Vector{UInt8}
    C::G
    oppening::Encryption{CastOppening{G}, G}
    signature::Union{Signature{G}, Nothing}
end

function Vote(proposal::Vector{UInt8}, C::G, oppening::Encryption{CastOppening{G}, G}, signer::Signer{G}) where G <: Group

    unsigned_vote = Vote(proposal, C, oppening, nothing)
    signature = sign(encode(Tree(unsigned_vote)), signer.g, signer.key)

    return Vote(proposal, C, oppening, signature)
end

function verify(vote::Vote{G}, g::G) where G <: Group

    (; proposal, C, oppening, signature) = vote
    unsigned_vote = Vote(proposal, C, oppening, nothing)

    return verify(encode(Tree(unsigned_vote)), g, vote.signature)
end


struct VoteEnvelope{G} # auxilary data that enables delivery device to be sure that identity commitment will appear on the buletin board
    vote::Vote{G}
    # 
    A::G # unsigned
    h_QR::Vector{UInt8} # 
    id::Vector{UInt8}
    w::Vector{UInt8}
    #w::G # 
    #π_w::ChaumPedersenProof
end


function check_challenge(envelope::VoteEnvelope, τ::Integer, hasher::HashSpec)

    (; C) = envelope.vote
    (; pbkey) = envelope.vote.signature
    (; A, h_QR, id, w) = envelope

    I = hasher([w; id])

    u = map2generator(pbkey, h_QR, I, hasher)
    
    check_challenge(C, A, u, τ, hasher) || return false

    return true
end
    

function assemble_vote!(voter::VotingCalculator{G}, selection::Integer, chg::Integer, pin::Int; inherit_challenge=false, roprg = gen_roprg()) where G <: Group

    if pin == voter.pin
        
        encoded_selection = selection
        coerced_vote = DecoyOppening()

    elseif pin in (i.pin for i in voter.decoys)

        encoded_selection = voter.current_selection[]
        N = findlast(i -> i.pin == pin, voter.decoys)
        coerced_vote = DecoyOppening(voter.proposal, selection, voter.decoys[N].seed)

    else

        error("Invalid pin code")

    end
        
    C, A, sup_oppening = TallyProofs.recommit!(voter.supersession, chg; roprg = gen_roprg(roprg(:supersession))) 
    (; β, history, ux, pok) = sup_oppening

    vote_oppening = VoteOppening(voter.tracker, encoded_selection, 2:order(G)-1; roprg)
    vote_commitment = commitment(vote_oppening, voter.proposal.basis)

    signer = Signer(voter.proposal.g, voter.key)

    proposal_hash = voter.hasher(encode(Tree(voter.proposal)))

    #I = voter.id
    (; w, id) = voter
    (; hasher) = voter.proposal
    
    I = hasher([octet(w); id])

    signed_vote_commitment = SignedVoteCommitment(proposal_hash, ux, vote_commitment, I, pok, signer)

    cast_oppening = CastOppening(β, history, signed_vote_commitment, vote_oppening, coerced_vote)

    cast_oppening_enc = encrypt(cast_oppening, voter.proposal.g, voter.proposal.collector, voter.proposal.encrypt_spec)

    voter.current_selection[] = encoded_selection

    vote = Vote(proposal_hash, C, cast_oppening_enc, signer)

    (; Q, R) = vote_commitment
    h_QR = voter.proposal.hasher([octet(Q); octet(R)])

    #vote_envelope = VoteEnvelope(vote, A, h_QR, UInt8[], UInt8[])
    vote_envelope = VoteEnvelope(vote, A, h_QR, id, octet(w))

    return vote_envelope
end

struct DecoyCommitment{G <: Group}
    Q::G # tracker commitment
    R::G
    selection::BigInt
end

function DecoyCommitment(oppening::VoteOppening, setup::GeneratorSetup{<:Group})

    (; tracker, selection, γ) = oppening

    @check γ == 0 "vote must be unblinded"

    Q, R = commitment(tracker, setup)

    return DecoyCommitment(Q, R, selection) # Needs to have also R
end

function commitment(vote::DecoyCommitment{G}, setup::GeneratorSetup{G}) where G <: Group
    
     (; g) = setup

     (; Q, R, selection) = vote
    
     V = g^selection
    
     return VoteCommitment(Q, R, V)
end

struct TallyRecord
    T::BigInt # the source
    tracker::BigInt
    selection::BigInt
end

struct Tally{G <: Group} <: Proposition
    proposal::Proposal
    cast_commitments::Vector{G}
    vote_commitments::Vector{SignedVoteCommitment{G}}
    skip_list::Vector{G} # In case voter had cast a vote with other means
    dummy_votes::Vector{DecoyCommitment{G}}
    coercion_token::BigInt # decoy_tracker_challenge
    tokens::Vector{<:Integer} # tracker_challenges
    tally::Vector{TallyRecord} # tally_board 
end

struct TallyProof{G <: Group} <: Proof
    supersession::SupersessionProof{G}
    reveal::RevealShuffleProof{G}
end

proof_type(::Type{Tally{G}}) where G <: Group = TallyProof{G}

function map2generator(pseudonym::G, h_QR::Vector{UInt8}, I::Vector{UInt8}, hasher::HashSpec) where G <: Group

    prg = PRG(hasher, [octet(pseudonym); h_QR; I])
    u = GeneratorBasis.generator_basis(prg, G) 

    return u
end

function map2generator(g::G, hasher::HashSpec) where G <: Group

    prg = PRG(hasher, octet(g))
    u = GeneratorBasis.generator_basis(prg, G) 

    return u
end

function extract_supersession(cast_oppenings::Vector{<:CastOppening})

    pseudonyms = [i.commitment.signature.pbkey for i in cast_oppenings]
    width = [length(trim(i.history)) for i in cast_oppenings]
    
    mask = extract_maximum_mask(pseudonyms, width)

    return mask
end

function compute_tokens(seed::Vector{UInt8}, ux::Vector{G}, token_max::Int, watermark_nbits::Int, hasher::HashSpec) where G <: Group

    prg = PRG(hasher, seed)

    nbits = ndigits(token_max, base=2) - 1
    offset = token_max - 2^nbits

    token_seeds = rand(prg, 0:BigInt(2)^nbits - 1, length(ux))
    tokens = [apply_watermark(ti, nbits, octet(uxi), hasher; num_positions = watermark_nbits) + offset for (ti, uxi) in zip(token_seeds, ux)]
    
    return tokens
end

function token_seed(Q::Vector{G}, R::Vector{G}, hasher::HashSpec) where G <: Group
    Q_vec = (octet(i) for i in Q)
    R_vec = (octet(i) for i in R)
    return hasher(UInt8[Iterators.flatten(R_vec) |> collect; Iterators.flatten(Q_vec) |> collect])
end

function tally(proposal::Proposal, cast_commitments::Vector{G}, cast_oppenings::Vector{CastOppening{G}}, hasher::HashSpec; skip_list = G[], mask = extract_supersession(cast_oppenings), dummy_votes::Vector{VoteOppening} = VoteOppening[]) where G <: Group

    (; token_max, watermark_nbits) = proposal

    public_cast_oppenings = @view(cast_oppenings[mask])
    
    pseudonyms = (i.commitment.signature.pbkey for i in public_cast_oppenings)
    skip_mask = BitVector(!(x in skip_list) for x in pseudonyms)

    public_dummy_votes = DecoyCommitment{G}[DecoyCommitment(i, proposal.basis) for i in dummy_votes]
    Q = [i.Q for i in public_dummy_votes]


    Q_vec = [i.commitment.commitment.Q for i in public_cast_oppenings]
    R_vec = [i.commitment.commitment.R for i in public_cast_oppenings]
    
    seed = token_seed(Q_vec, R_vec, hasher)
    tokens = compute_tokens(seed, Q_vec, token_max, watermark_nbits, hasher)

    tracker_challenges = tokens[skip_mask] #.|> BigInt

    Q′_vec = [i.Q for i in public_dummy_votes]
    R′_vec = [i.R for i in public_dummy_votes]

    decoy_seed = [seed; token_seed(Q′_vec, R′_vec, hasher)]
    
    coercion_token = rand(PRG(hasher, decoy_seed), 2:order(G) - 1) 

    append!(tracker_challenges, (coercion_token for i in eachindex(dummy_votes)))
    total_tracker_challenges = tracker_challenges
    
    vote_oppenings = (i.oppening for i in @view(public_cast_oppenings[skip_mask])) # added here
    total_vote_oppenings = Iterators.flatten((vote_oppenings, dummy_votes))
    trackers = (tracker(oppening, chg, order(proposal.g)) for (chg, oppening) in zip(total_tracker_challenges, total_vote_oppenings))

    tally = TallyRecord[TallyRecord(Ti, octet2int(hasher(int2octet(Ti))[1:8]), oppening.selection) for (Ti, oppening) in zip(trackers, total_vote_oppenings)]

    vote_commitments = [i.commitment for i in public_cast_oppenings]

    return Tally(proposal, cast_commitments, vote_commitments, skip_list, public_dummy_votes, coercion_token, tokens, tally)
end

function reduce_representation(cast_oppenings::Vector{CastOppening{G}}, u::Vector{G}, ux::Vector{G}, history::Vector{Vector{BigInt}}, hasher::HashSpec) where G <: Group

    pseudonyms = (i.commitment.signature.pbkey for i in cast_oppenings)
    
    Q_vec = (i.commitment.commitment.Q for i in cast_oppenings)
    R_vec = (i.commitment.commitment.R for i in cast_oppenings)

    h_QR = (hasher([octet(Qi); octet(Ri)]) for (Qi, Ri) in zip(Q_vec, R_vec))

    I_vec = (i.commitment.I for i in cast_oppenings)

    _u = (map2generator(pi, hi, Ii, hasher) for (pi, hi, Ii) in zip(pseudonyms, h_QR, I_vec))
    _ux = (i.commitment.ux for i in cast_oppenings) 
    pok = (i.commitment.pok for i in cast_oppenings)
    _history = (i.history for i in cast_oppenings)
    β = (i.β for i in cast_oppenings)

    recommits = [ReCommit(βi, ui, uxi, historyi, poki) for (βi, ui, uxi, historyi, poki) in zip(β, _u, _ux, _history, pok)]

    return reduce_representation(recommits, u, ux, history)
end

function prove(proposition::Tally{G}, verifier::Verifier, cast_oppenings::Vector{CastOppening{G}}, 𝛙_reveal::Vector{Int}; mask = extract_supersession(cast_oppenings), roprg = gen_roprg(), dummy_votes::Vector{VoteOppening} = VoteOppening[]) where G <: Group

    hasher = verifier.prghash

    Q_vec = [i.commitment.commitment.Q for i in @view(cast_oppenings[mask])]
    R_vec = [i.commitment.commitment.R for i in @view(cast_oppenings[mask])]

    h_QR = (hasher([octet(Qi); octet(Ri)]) for (Qi, Ri) in zip(Q_vec, R_vec))

    I_vec = (i.commitment.I for i in @view(cast_oppenings[mask]))

    u = [map2generator(i.signature.pbkey, hi, Ii, hasher) for (i, hi, Ii) in zip(proposition.vote_commitments, h_QR, I_vec)]
    ux = [i.ux for i in proposition.vote_commitments]
    pok = [i.pok for i in proposition.vote_commitments]

    history = [copy(trim(i.history)) for i in @view(cast_oppenings[mask])]

    ψ, α = reduce_representation(cast_oppenings, u, ux, history, hasher)
    β = [i.β for i in cast_oppenings]

    supersession_proposition = Supersession(proposition.cast_commitments, proposition.proposal.basis.h, u, ux, pok)

    supersession_proof = prove(supersession_proposition, verifier, ψ, β, α; roprg = gen_roprg(roprg(:supersession))) 
    skip_mask = BitVector(!(x.signature.pbkey in proposition.skip_list) for x in proposition.vote_commitments)

    tracker_challenges = proposition.tokens[skip_mask]
    coercion_tracker_challenges = (proposition.coercion_token for i in eachindex(proposition.dummy_votes))
    total_tracker_challenges = collect(BigInt, Iterators.flatten((tracker_challenges, coercion_tracker_challenges)))
    
    vote_commitments = (i.commitment for i in @view(proposition.vote_commitments[skip_mask]))
    dummy_vote_commitments = (commitment(i, proposition.proposal.basis) for i in dummy_votes)
    total_vote_commitments = collect(VoteCommitment{G}, Iterators.flatten((vote_commitments, dummy_vote_commitments)))
    
    reveal_proposition = RevealShuffle(proposition.proposal.basis, total_tracker_challenges, total_vote_commitments, [VoteRecord(i.T, i.selection) for i in proposition.tally])

    vote_oppenings = (i.oppening for i in @view(cast_oppenings[mask][skip_mask]))

    total_vote_oppenings = collect(VoteOppening, Iterators.flatten((vote_oppenings, dummy_votes)))

    reveal_proof = prove(reveal_proposition, verifier, total_vote_oppenings, 𝛙_reveal; roprg = gen_roprg(roprg(:reveal)))    

    return TallyProof(supersession_proof, reveal_proof)
end

function extract_decoy_votes(cast_oppenings)

    indicies = unique(reverse(eachindex(cast_oppenings))) do i
        
        (; θ, λ) = cast_oppenings[i].decoy
        pseudonym = cast_oppenings[i].commitment.signature.pbkey

        return (octet(pseudonym), θ, λ) # need to add hash for CryptoGroups
    end

    decoys = [i.decoy for i in @view(cast_oppenings[indicies]) if !iszero(i.decoy)]

    return decoys
end

function compute_dummy_votes(votes, range; roprg = gen_roprg)
    return [VoteOppening(vi, range) for (i, vi) in enumerate(votes)] # need to add roprg here
end

function tally(proposal::Proposal, cast_commitments::Vector{G}, cast_oppenings::Vector{CastOppening{G}}, verifier::Verifier; skip_list = G[], decoy_votes::Vector{DecoyOppening} = DecoyOppening[], dummy_votes::Vector{VoteOppening} = compute_dummy_votes(Iterators.flatten((decoy_votes, extract_decoy_votes(cast_oppenings))), 2:order(G) - 1)) where G <: Group

    hasher = verifier.prghash

    filter_mask = extract_supersession(cast_oppenings)
    commit_perm = sortperm(@view(cast_oppenings[filter_mask]); by = x -> x.commitment.signature.pbkey)
    
    mask = findall(filter_mask)[commit_perm]

    proposition = tally(proposal, cast_commitments, cast_oppenings, hasher; skip_list, mask, dummy_votes)

    𝛙 = sortperm(proposition.tally, by = x -> x.tracker) # this may also work with the added dummy votes
    permute!(proposition.tally, 𝛙)

    proof = prove(proposition, verifier, cast_oppenings, 𝛙; mask, dummy_votes) 

    return Simulator(proposition, proof, verifier)    
end

function decoy_token(seed::Vector{UInt8}, decoy_votes::Vector{DecoyCommitment{G}}, hasher) where G <: Group

    Q′_vec = [i.Q for i in decoy_votes]
    R′_vec = [i.R for i in decoy_votes]

    decoy_seed = [seed; token_seed(Q′_vec, R′_vec, hasher)]

    return rand(PRG(hasher, decoy_seed), 2:order(G) - 1)
end


function verify(proposition::Tally{G}, proof::TallyProof{G}, verifier::Verifier) where G <: Group
    
    hasher = verifier.prghash

    (; h, g) = proposition.proposal.basis
    proposition.proposal.basis == GeneratorSetup(h, g) || return false
    
    (; token_max, watermark_nbits) = proposition.proposal
    (; vote_commitments, cast_commitments) = proposition

    for i in proposition.vote_commitments
        verify(i, proposition.proposal.g) || return false
    end

    Q_vec = [i.commitment.Q for i in vote_commitments]
    R_vec = [i.commitment.R for i in vote_commitments]

    h_QR = (hasher([octet(Qi); octet(Ri)]) for (Qi, Ri) in zip(Q_vec, R_vec))

    I_vec = (i.I for i in vote_commitments)

    u = [map2generator(i.signature.pbkey, hi, Ii, hasher) for (i, hi, Ii) in zip(vote_commitments, h_QR, I_vec)]
    ux = [i.ux for i in vote_commitments]
    pok = [i.pok for i in vote_commitments]
    
    supersession_proposition = Supersession(cast_commitments, h, u, ux, pok)
    verify(supersession_proposition, proof.supersession, verifier) || return false

    # Verifying tokens
    seed = token_seed(Q_vec, R_vec, hasher)
    tokens = compute_tokens(seed, Q_vec, token_max, watermark_nbits, hasher)

    proposition.tokens == tokens || return false
    proposition.coercion_token == decoy_token(seed, proposition.dummy_votes, hasher) || return false

    # Making revaal shuffle taking into account skip_list and decoy_votes
    skip_mask = BitVector(!(x.signature.pbkey in proposition.skip_list) for x in vote_commitments)

    tracker_challenges = tokens[skip_mask] 
    append!(tracker_challenges, Iterators.repeated(proposition.coercion_token, length(proposition.dummy_votes)))

    reveal_vote_commitments = [i.commitment for i in @view(vote_commitments[skip_mask])]
    append!(reveal_vote_commitments, (commitment(i, proposition.proposal.basis) for i in proposition.dummy_votes))

    reveal_proposition = RevealShuffle(proposition.proposal.basis, tracker_challenges, reveal_vote_commitments, [VoteRecord(i.T, i.selection) for i in proposition.tally])

    verify(reveal_proposition, proof.reveal, verifier) || return false

    return true
end
