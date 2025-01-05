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

struct CoercedVote
    θ::BigInt # Could be reused to mark revotes
    λ::BigInt
    selection::BigInt
end

CoercedVote() = CoercedVote(0, 0, 0)

function CoercedVote(selection::Integer, range::UnitRange; roprg = gen_roprg())

    θ = rand(roprg(:θ), range)
    λ = rand(roprg(:λ), range)

    return CoercedVote(θ, λ, selection)
end

Base.zero(::Type{CoercedVote}) = CoercedVote(0, 0, 0)
Base.zero(::CoercedVote) = zero(CoercedVote)


function VoteOppening(vote::CoercedVote, range::UnitRange; roprg = gen_roprg())

    (; θ, λ, selection) = vote
    α = rand(roprg(:α), range)
    #β = rand(roprg(:β), range)

    β = 0
    γ = 0

    #return VoteOppening(α, θ, λ, β, selection)
    #return VoteOppening(α, λ, β, θ, γ, selection)

    tracker = TrackerOppening(α, λ, β, θ)
    return VoteOppening(tracker, selection, γ)
end


Base.:(==)(x::CoercedVote, y::CoercedVote) = x.θ == y.θ && x.λ == y.λ && x.selection == y.selection

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

    h, d, o = generator_basis(verifier, G, 3)
    basis = GeneratorSetup(h, d, o)
    
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
    #(; d, t) = proposal.basis

    T = tracker(θ, λ, token, order(proposal.g))
    #T =  d^θ * t^(λ * token)
    #T =  mod(θ + λ * token, order(proposal.g))

    return proposal.hasher(int2octet(T))[1:8] |> octet2int
end

function CoercedVote(proposal::Proposal{G}, selection::Integer, seed::Vector{UInt8}) where G <: Group
    θ, λ = compute_tracker_preimage(proposal, seed)
    return CoercedVote(θ, λ, selection)
end

struct VotingCalculator{G} # More preciselly it would be VotingCalculatorInstance
    proposal::Proposal{G}

    verifier::Verifier
    hasher::HashSpec # We shall also take it from the verifier

    supersession::SupersessionCalculator{G}

    challenge::Vector{UInt8} # for the signed vote commitments

    pseudonym::G # computed from a generator
    key::BigInt

    # We shall keep the tracker constant for simplicity
    pin::Int # Pin code for authetification
    tracker::TrackerOppening
#    θ::BigInt
#    λ::BigInt

    current_selection::Ref{BigInt}
    trigger_token::Ref{Union{Int, Nothing}}
    
    override_mask::Vector{OverrideMask}
    decoys::Vector{DecoyCredential}
end

function VotingCalculator(proposal::Proposal{G}, verifier::Verifier, key::Integer, pin::Int; roprg = gen_roprg(), history_width::Int = 5) where G <: Group
    
    hasher = verifier.prghash # the verifier could implement hasher method

    (; g) = proposal
    (; h, d) = proposal.basis

    pseudonym = g^key

    u = map2generator(pseudonym, hasher)
    sup_calc = SupersessionCalculator(h, u, verifier; history_width, roprg)

    challenge = rand(UInt8, 32) # I could use roprg here perhaps

    tracker = TrackerOppening(2:order(G)-1; roprg)
    #θ = rand(roprg(:θ), 2:order(G) - 1)
    #λ = rand(roprg(:λ), 2:order(G) - 1)

    return VotingCalculator(proposal, verifier, hasher, sup_calc, challenge, pseudonym, key |> BigInt, pin, tracker, Ref{BigInt}(0), Ref{Union{Int, Nothing}}(nothing), OverrideMask[], DecoyCredential[])
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

function tracker_challenge(ux::G, chg::Vector{UInt8}, token::Integer, hasher::HashSpec) where G <: Group

    token_bytes = zeros(UInt8, 8)
    int2octet!(token_bytes, BigInt(token)) # ToDo: fix for CryptoGroups
    
    prg = PRG(hasher, [octet(ux); chg; token_bytes])

    return rand(prg, 2:order(G)-1)
end

function verify_watermark(proposal::Proposal{G}, ux::G, token::Integer, hasher::HashSpec) where G <: Group
    
    (; token_max, watermark_nbits) = proposal

    nbits = ndigits(token_max, base=2) - 1
    offset = token_max - 2^nbits
    return verify_watermark(token - offset, nbits, octet(ux), hasher; num_positions = watermark_nbits)    
end

function compute_tracker(voter::VotingCalculator, token::Integer, pin::Int; reset_trigger_token::Bool = false)

    (; hasher) = voter
    (; d) = voter.proposal.basis

    if (isnothing(voter.trigger_token[]) || reset_trigger_token) && verify_watermark(voter.proposal, voter.supersession.ux, token, hasher)
        voter.trigger_token[] = token
    end

    # The computation is always present in spite if it is even to be superseeded by the mask
    if voter.pin == pin
        (; θ, λ) = voter.tracker
        challenge = tracker_challenge(voter.supersession.ux, voter.challenge, token, voter.hasher)
    else

        N = findlast(x -> x.pin == pin, voter.decoys)

        if isnothing(N)
            error("Incoreect PIN code")
        else
            (; seed) = voter.decoys[N]
            #T = compute_tracker_element(voter.proposal, seed, token)
            θ, λ = compute_tracker_preimage(voter.proposal, seed)
            challenge = token
        end

    end

    T = tracker(θ, λ, challenge, order(voter.proposal.g))

    M = findlast(x -> x.pin == pin, voter.override_mask)

    if voter.trigger_token[] == token && !isnothing(M)
        return voter.override_mask[M].tracker 
    else
        return hasher(int2octet(T))[1:8] |> octet2int
    end
end

struct SignedVoteCommitment{G <: Group}
    proposal::Vector{UInt8} # hash
    commitment::VoteCommitment{G}
    ux::G
    pok::SchnorrProof{G}
    challenge::Vector{UInt8}
    signature::Union{Signature{G}, Nothing} # Perhaps here I just can define tree or digest function
end

struct CastOppening{G <: Group}
    β::BigInt # For supersession
    history::Vector{BigInt}
    commitment::SignedVoteCommitment{G}
    oppening::VoteOppening # Can be further encrypted in a threshold decryption ceremony if one wishes to have that for fairness
    decoy::CoercedVote
end

function SignedVoteCommitment(proposal::Vector{UInt8}, commitment::VoteCommitment{G}, ux::G, pok::SchnorrProof, challenge::Vector{UInt8}, signer::Signer{G}) where G <: Group

    unsigned_vote_commitment = SignedVoteCommitment(proposal, commitment, ux, pok, challenge, nothing)
    internal_signature = sign(encode(Tree(unsigned_vote_commitment)), signer.g, signer.key)

    return SignedVoteCommitment(proposal, commitment, ux, pok, challenge, internal_signature)
end

function verify(vote::SignedVoteCommitment{G}, g::G) where G <: Group

    (; proposal, commitment, ux, pok, challenge) = vote
    unsigned_vote_commitment = SignedVoteCommitment(proposal, commitment, ux, pok, challenge, nothing)
    
    return verify(encode(Tree(unsigned_vote_commitment)), g, vote.signature)
end

struct Vote{G}
    proposal::Vector{UInt8}
    C::G
    A::G
    oppening::Encryption{CastOppening{G}, G}
    signature::Union{Signature{G}, Nothing}
end

function Vote(proposal::Vector{UInt8}, C::G, A::G, oppening::Encryption{CastOppening{G}, G}, signer::Signer{G}) where G <: Group

    unsigned_vote = Vote(proposal, C, A, oppening, nothing)
    signature = sign(encode(Tree(unsigned_vote)), signer.g, signer.key)

    return Vote(proposal, C, A, oppening, signature)
end

function verify(vote::Vote{G}, g::G) where G <: Group

    (; proposal, C, A, oppening, signature) = vote
    unsigned_vote = Vote(proposal, C, A, oppening, nothing)

    return verify(encode(Tree(unsigned_vote)), g, vote.signature)
end

function check_challenge(vote::Vote{G}, chg::Integer, hasher::HashSpec) where G <: Group
    u = map2generator(vote.signature.pbkey, hasher)
    return check_challenge(vote.C, vote.A, u, chg, hasher) 
end

function assemble_vote!(voter::VotingCalculator{G}, selection::Integer, chg::Integer, pin::Int; inherit_challenge=false, roprg = gen_roprg()) where G <: Group

    if pin == voter.pin
        
        encoded_selection = selection
        coerced_vote = CoercedVote()

    elseif pin in (i.pin for i in voter.decoys)

        encoded_selection = voter.current_selection[]
        N = findlast(i -> i.pin == pin, voter.decoys)
        coerced_vote = CoercedVote(voter.proposal, selection, voter.decoys[N].seed)

    else

        error("Invalid pin code")

    end
        
    C, A, sup_oppening = TallyProofs.recommit!(voter.supersession, chg; roprg = gen_roprg(roprg(:supersession))) 
    (; β, history, ux, pok) = sup_oppening

    vote_oppening = VoteOppening(voter.tracker, encoded_selection, 2:order(G)-1; roprg)
    vote_commitment = commitment(vote_oppening, voter.proposal.basis)

    buffer = zeros(UInt8, 16)
    int2octet!(buffer, chg |> BigInt) # TODO: CryptoGroups bug!!!
    blinded_challenge = voter.hasher([buffer; octet(A)])

    copyto!(voter.challenge, blinded_challenge)

    signer = Signer(voter.proposal.g, voter.key)

    proposal_hash = voter.hasher(encode(Tree(voter.proposal)))

    signed_vote_commitment = SignedVoteCommitment(proposal_hash, vote_commitment, ux, pok, blinded_challenge, signer)

    cast_oppening = CastOppening(β, history, signed_vote_commitment, vote_oppening, coerced_vote)

    cast_oppening_enc = encrypt(cast_oppening, voter.proposal.g, voter.proposal.collector, voter.proposal.encrypt_spec)

    voter.current_selection[] = encoded_selection

    return Vote(proposal_hash, C, A, cast_oppening_enc, signer)
end

struct DummyVote{G <: Group}
    Q::G # tracker commitment
    θ::BigInt # for the tracker
    selection::BigInt
end

function dummy_vote(oppening::VoteOppening, setup::GeneratorSetup{<:Group})

    (; h, d) = setup
    #(; α, θ, λ, selection, β, γ) = oppening
    (; tracker, selection, γ) = oppening
    (; α, λ, θ) = tracker
    
    @check γ == 0 "vote must be unblinded"
    
    #Q = h^α * t^λ
    Q = h^α * d^λ
    
    return DummyVote(Q, θ, selection) # Needs to have also R
end

function commitment(vote::DummyVote{G}, d::G, o::G, e::BigInt) where G <: Group
    
    (; Q, θ, selection) = vote

    C = d^θ * o^selection
    
    return C * Q^e
end

function vote_commitment(vote::DummyVote{G}, setup::GeneratorSetup{G}) where G <: Group
    
    (; d, o, h) = setup
    (; Q, θ, selection) = vote

    #C = d^θ * o^selection
    
    R = d^θ # This is a hack

    V = o^selection
    
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
    dummy_votes::Vector{DummyVote{G}}
    coercion_token::BigInt # decoy_tracker_challenge
    tokens::Vector{<:Integer} # tracker_challenges
    tally::Vector{TallyRecord} # tally_board 
end

struct TallyProof{G <: Group} <: Proof
    supersession::SupersessionProof{G}
    #dummy_trackers::Vector{PedersenProof{G}}
    reveal::RevealShuffleProof{G}
end

proof_type(::Type{Tally{G}}) where G <: Group = TallyProof{G}

function map2generator(pseudonym::G, hasher::HashSpec) where G <: Group

    prg = PRG(hasher, octet(pseudonym))
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

    token_seeds = rand(prg, 0:2^nbits - 1, length(ux))
    tokens = [apply_watermark(ti, nbits, octet(uxi), hasher; num_positions = watermark_nbits) + offset for (ti, uxi) in zip(token_seeds, ux)]
    
    return tokens
end

function token_seed(ux::Vector{G}, challenges::Vector{UInt8}, Q::Vector{G}, hasher::HashSpec) where G <: Group
    Q_vec = (octet(i) for i in Q)
    return hasher(UInt8[octet(prod(ux)); challenges; Iterators.flatten(Q_vec) |> collect])
end

function tally(proposal::Proposal, cast_commitments::Vector{G}, cast_oppenings::Vector{CastOppening{G}}, hasher::HashSpec; skip_list = G[], mask = extract_supersession(cast_oppenings), dummy_votes::Vector{VoteOppening} = VoteOppening[]) where G <: Group

    (; token_max, watermark_nbits) = proposal

    public_cast_oppenings = @view(cast_oppenings[mask])
    
    pseudonyms = (i.commitment.signature.pbkey for i in public_cast_oppenings)
    u = [map2generator(pi, hasher) for pi in pseudonyms]
    ux = [i.commitment.ux for i in public_cast_oppenings] # will be significant

    skip_mask = BitVector(!(x in skip_list) for x in pseudonyms)

    public_dummy_votes = DummyVote{G}[dummy_vote(i, proposal.basis) for i in dummy_votes]
    Q = [i.Q for i in public_dummy_votes]

    challenges = (i.commitment.challenge for i in public_cast_oppenings)
    seed = token_seed(ux, Iterators.flatten(challenges) |> collect, Q, hasher)

    tokens = compute_tokens(seed, ux, token_max, watermark_nbits, hasher)
    tracker_challenges = (tracker_challenge(i.commitment.ux, i.commitment.challenge, ti, hasher) for (i, ti) in zip(@view(public_cast_oppenings[skip_mask]), @view(tokens[skip_mask])))
    coercion_token = rand(PRG(hasher, seed), 2:order(G) - 1) 
    coercion_tracker_challenges = (coercion_token for i in eachindex(dummy_votes))
    total_tracker_challenges = Iterators.flatten((tracker_challenges, coercion_tracker_challenges))

    vote_oppenings = (i.oppening for i in @view(public_cast_oppenings[skip_mask])) # added here
    total_vote_oppenings = Iterators.flatten((vote_oppenings, dummy_votes))

    #trackers = (tracker(oppening, chg, proposal.basis) for (chg, oppening) in zip(total_tracker_challenges, total_vote_oppenings))
    trackers = (tracker(oppening, chg, order(proposal.g)) for (chg, oppening) in zip(total_tracker_challenges, total_vote_oppenings))

    #tally = TallyRecord{G}[TallyRecord(Ti, octet2int(hasher(octet(Ti))[1:8]), oppening.selection) for (Ti, oppening) in zip(trackers, total_vote_oppenings)]
    tally = TallyRecord[TallyRecord(Ti, octet2int(hasher(int2octet(Ti))[1:8]), oppening.selection) for (Ti, oppening) in zip(trackers, total_vote_oppenings)]

    vote_commitments = [i.commitment for i in public_cast_oppenings]

    return Tally(proposal, cast_commitments, vote_commitments, skip_list, public_dummy_votes, coercion_token, tokens, tally)
end

function reduce_representation(cast_oppenings::Vector{CastOppening{G}}, u::Vector{G}, ux::Vector{G}, history::Vector{Vector{BigInt}}, hasher::HashSpec) where G <: Group

    pseudonyms = (i.commitment.signature.pbkey for i in cast_oppenings)
    _u = (map2generator(pi, hasher) for pi in pseudonyms)
    _ux = (i.commitment.ux for i in cast_oppenings) 
    pok = (i.commitment.pok for i in cast_oppenings)
    _history = (i.history for i in cast_oppenings)
    β = (i.β for i in cast_oppenings)

    recommits = [ReCommit(βi, ui, uxi, historyi, poki) for (βi, ui, uxi, historyi, poki) in zip(β, _u, _ux, _history, pok)]

    return reduce_representation(recommits, u, ux, history)
end

function prove(proposition::Tally{G}, verifier::Verifier, cast_oppenings::Vector{CastOppening{G}}, 𝛙_reveal::Vector{Int}; mask = extract_supersession(cast_oppenings), roprg = gen_roprg(), dummy_votes::Vector{VoteOppening} = VoteOppening[]) where G <: Group

    hasher = verifier.prghash

    u = [map2generator(i.signature.pbkey, hasher) for i in proposition.vote_commitments]
    ux = [i.ux for i in proposition.vote_commitments]
    pok = [i.pok for i in proposition.vote_commitments]

    history = [copy(trim(i.history)) for i in @view(cast_oppenings[mask])]

    ψ, α = reduce_representation(cast_oppenings, u, ux, history, hasher)
    β = [i.β for i in cast_oppenings]

    supersession_proposition = Supersession(proposition.cast_commitments, proposition.proposal.basis.h, u, ux, pok)

    supersession_proof = prove(supersession_proposition, verifier, ψ, β, α; roprg = gen_roprg(roprg(:supersession))) 
    skip_mask = BitVector(!(x.signature.pbkey in proposition.skip_list) for x in proposition.vote_commitments)

    tracker_challenges = (tracker_challenge(i.ux, i.challenge, ti, hasher) for (i, ti) in zip(@view(proposition.vote_commitments[skip_mask]), @view(proposition.tokens[skip_mask])))
    coercion_tracker_challenges = (proposition.coercion_token for i in eachindex(proposition.dummy_votes))
    total_tracker_challenges = collect(BigInt, Iterators.flatten((tracker_challenges, coercion_tracker_challenges)))
    
    vote_commitments = (i.commitment for i in @view(proposition.vote_commitments[skip_mask]))
    #dummy_vote_commitments = (vote_commitment(i, proposition.proposal.basis) for i in dummy_votes)
    #dummy_vote_commitments = (VoteCommitment(i, proposition.proposal.basis) for i in dummy_votes)
    dummy_vote_commitments = (commitment(i, proposition.proposal.basis) for i in dummy_votes)
    total_vote_commitments = collect(VoteCommitment{G}, Iterators.flatten((vote_commitments, dummy_vote_commitments)))
    
    reveal_proposition = RevealShuffle(proposition.proposal.basis, total_tracker_challenges, total_vote_commitments, [VoteRecord(i.T, i.selection) for i in proposition.tally])

    vote_oppenings = (i.oppening for i in @view(cast_oppenings[mask][skip_mask]))

    total_vote_oppenings = collect(VoteOppening, Iterators.flatten((vote_oppenings, dummy_votes)))

    reveal_proof = prove(reveal_proposition, verifier, total_vote_oppenings, 𝛙_reveal; roprg = gen_roprg(roprg(:reveal)))    

    # dummy_tracker_proofs = Vector{PedersenProof{G}}(undef, length(dummy_votes))

    # for (i, (v, oppening)) in enumerate(zip(proposition.dummy_votes, dummy_votes)) 

    #     pedersen_commitment = PedersenCommitment(proposition.proposal.basis.h, proposition.proposal.basis.d, v.Q)
    #     pedersen_proof = prove(pedersen_commitment, verifier, oppening.tracker.λ, oppening.tracker.α; roprg = gen_roprg(roprg("dummy_tracker_$i")))

    #     dummy_tracker_proofs[i] = pedersen_proof
    # end

    #return TallyProof(supersession_proof, dummy_tracker_proofs, reveal_proof)
    return TallyProof(supersession_proof, reveal_proof)
end

function extract_coerced_votes(cast_oppenings)

    indicies = unique(reverse(eachindex(cast_oppenings))) do i
        
        (; θ, λ) = cast_oppenings[i].decoy
        pseudonym = cast_oppenings[i].commitment.signature.pbkey

        #return (pseudonym, θ, λ)
        return (octet(pseudonym), θ, λ) # need to add hash for CryptoGroups
    end

    decoys = [i.decoy for i in @view(cast_oppenings[indicies]) if !iszero(i.decoy)]

    return decoys
end

function compute_dummy_votes(votes, range; roprg = gen_roprg)
    return [VoteOppening(vi, range) for (i, vi) in enumerate(votes)] # need to add roprg here
end

function tally(proposal::Proposal, cast_commitments::Vector{G}, cast_oppenings::Vector{CastOppening{G}}, verifier::Verifier; skip_list = G[], decoy_votes::Vector{CoercedVote} = CoercedVote[], dummy_votes::Vector{VoteOppening} = compute_dummy_votes(Iterators.flatten((decoy_votes, extract_coerced_votes(cast_oppenings))), 2:order(G) - 1)) where G <: Group

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

function verify(proposition::Tally{G}, proof::TallyProof{G}, verifier::Verifier) where G <: Group
    
    hasher = verifier.prghash

    (; h, d, o) = proposition.proposal.basis
    proposition.proposal.basis == GeneratorSetup(h, d, o) || return false
    
    (; token_max, watermark_nbits) = proposition.proposal
    (; vote_commitments, cast_commitments) = proposition

    for i in proposition.vote_commitments
        verify(i, proposition.proposal.g) || return false
    end

    u = [map2generator(i.signature.pbkey, hasher) for i in vote_commitments]
    ux = [i.ux for i in vote_commitments]
    pok = [i.pok for i in vote_commitments]
    
    supersession_proposition = Supersession(cast_commitments, h, u, ux, pok)
    verify(supersession_proposition, proof.supersession, verifier) || return false

    skip_mask = BitVector(!(x.signature.pbkey in proposition.skip_list) for x in vote_commitments)

    challenges = (i.challenge for i in vote_commitments)
    Q = [i.Q for i in proposition.dummy_votes]
    seed = token_seed(ux, Iterators.flatten(challenges) |> collect, Q, hasher)

    tokens = compute_tokens(seed, ux, token_max, watermark_nbits, hasher)
    proposition.tokens == tokens || return false
    proposition.coercion_token == rand(PRG(hasher, seed), 2:order(G) - 1) || return false

    tracker_challenges = (tracker_challenge(i.ux, i.challenge, ti, hasher) for (i, ti) in zip(@view(vote_commitments[skip_mask]), @view(tokens[skip_mask])))
    coercion_tracker_challenges = (proposition.coercion_token for i in eachindex(proposition.dummy_votes))
    total_tracker_challenges = collect(BigInt, Iterators.flatten((tracker_challenges, coercion_tracker_challenges)))

    reveal_vote_commitments = (i.commitment for i in @view(vote_commitments[skip_mask]))
    dummy_vote_commitments = (vote_commitment(i, proposition.proposal.basis) for i in proposition.dummy_votes)
    total_vote_commitments = collect(VoteCommitment{G}, Iterators.flatten((reveal_vote_commitments, dummy_vote_commitments)))

    reveal_proposition = RevealShuffle(proposition.proposal.basis, total_tracker_challenges, total_vote_commitments, [VoteRecord(i.T, i.selection) for i in proposition.tally])

    verify(reveal_proposition, proof.reveal, verifier) || return false

    # for (Qi, proofi) in zip(Q, proof.dummy_trackers)
    #     pedersen_commitment = PedersenCommitment(proposition.proposal.basis.h, proposition.proposal.basis.d, Qi)
    #     verify(pedersen_commitment, proofi, verifier) || return false
    # end
    
    return true
end
