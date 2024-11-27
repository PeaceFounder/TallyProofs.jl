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

struct CoercionTracker
    pin::Int
    tracker::BigInt
end

struct CoercedVote{G <: Group} # When coercion tracker is put in it can be reduced to CoercionInfo
    pin::Int
    θ::BigInt
    λ::BigInt
    T_d::G
    T_t::G
end

struct Proposal{G <: Group} 
    spec::Vector{UInt8} # hash of other set of parameters
    g::G
    collector::G
    basis::GeneratorSetup{G} # new
    watermark_nbits::Int
    token_max::Int # 
    encrypt_spec::EncryptSpec
end

function Proposal(g::G, collector::G, verifier::Verifier; spec = UInt8[], watermark_nbits::Int=4, token_max::Int=9999_9999, encrypt_spec::EncryptSpec=AES256_SHA256()) where G <: Group

    h, d, t, o = generator_basis(verifier, G, 4)
    basis = GeneratorSetup(h, d, t, o)
    
    return Proposal(spec, g, collector, basis, watermark_nbits, token_max, encrypt_spec)
end

struct VotingCalculator{G} # More preciselly it would be VotingCalculatorInstance
    proposal::Proposal{G}

    verifier::Verifier
    hasher::HashSpec # We shall also take it from the verifier
                  #setup::GeneratorSetup # we shall generate it from the Verifier. The blinding generator shall also be reused

    supersession::SupersessionCalculator{G}

    challenge::Vector{UInt8} # for the signed vote commitments

    pseudonym::G # computed from a generator
    key::BigInt

    # We shall keep the tracker constant for simplicity
    pin::Int # Pin code for authetification
    θ::BigInt
    λ::BigInt
    T_d::G 
    T_t::G # resutling tracker is Hash(T_d * T_t^e)

    # trigger_token
    last_token_trigger::Ref{Union{Int, Nothing}} # lest token which watermark have been correct

    unresolved_coercions::Vector{CoercedVote}
    coercion_trackers::Vector{CoercionTracker}
end

function VotingCalculator(proposal::Proposal{G}, verifier::Verifier, key::Integer, pin::Int; roprg = gen_roprg()) where G <: Group
    
    hasher = verifier.prghash # the verifier could implement hasher method

    (; g) = proposal
    (; h, d, t) = proposal.basis

    pseudonym = g^key

    u = map2generator(pseudonym, hasher)
    sup_calc = SupersessionCalculator(h, u, verifier)

    challenge = rand(UInt8, 32) # I could use roprg here perhaps

    θ = rand(roprg(:θ), 2:order(G) - 1)
    λ = rand(roprg(:λ), 2:order(G) - 1)

    T_d = d^θ
    T_t = t^λ
    
    return VotingCalculator(proposal, verifier, hasher, sup_calc, challenge, pseudonym, key |> BigInt, pin, θ, λ, T_d, T_t, Ref{Union{Int, Nothing}}(nothing), CoercedVote[], CoercionTracker[])
end

function install_coercion_tracker!(calc::VotingCalculator, fake_tracker::Integer, fake_pin::Int, pin::Int)
    
    @check fake_pin != pin "PIN codes can't be equal" # currently it is unclear if it should not be allowed

    if pin == calc.pin || pin in (i.pin for i in calc.coercion_trackers)
        
        entry = CoercionTracker(fake_pin, fake_tracker)
        push!(calc.coercion_trackers, entry)

    else
        error("Invalid PIN code")
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

    if (isnothing(voter.last_token_trigger[]) || reset_trigger_token) && verify_watermark(voter.proposal, voter.supersession.ux, token, voter.hasher)
        voter.last_token_trigger[] = token
    end

    if !(voter.pin == pin)

        N = findfirst(x -> x.pin == pin, voter.coercion_trackers)
        
        if isnothing(N)
            error("Incoreect PIN code")
        elseif voter.last_token_trigger[] == token
            return voter.coercion_trackers[N].tracker
        end            
    end
    
    challenge = tracker_challenge(voter.supersession.ux, voter.challenge, token, voter.hasher)

    (; T_d, T_t, hasher) = voter
    T = T_d * T_t^challenge

    return hasher(octet(T))[1:8] |> octet2int
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

    C, A, sup_oppening = TallyProofs.recommit!(voter.supersession, chg; roprg = gen_roprg(roprg(:supersession))) 
    (; β, history, ux, pok) = sup_oppening

    _α = rand(roprg(:α), 2:order(G) - 1)
    _β = rand(roprg(:β), 2:order(G) - 1)
    
    oppening = VoteOppening(_α, voter.θ, voter.λ, _β, selection)
    commitment = vote_commitment(oppening, voter.proposal.basis)

    buffer = zeros(UInt8, 16)
    int2octet!(buffer, chg |> BigInt) # TODO: CryptoGroups bug!!!
    blinded_challenge = voter.hasher([buffer; octet(A)])

    copyto!(voter.challenge, blinded_challenge)

    signer = Signer(voter.proposal.g, voter.key)

    proposal_hash = voter.hasher(encode(Tree(voter.proposal)))

    signed_vote_commitment = SignedVoteCommitment(proposal_hash, commitment, ux, pok, blinded_challenge, signer)

    cast_oppening = CastOppening(β, history, signed_vote_commitment, oppening)

    cast_oppening_enc = encrypt(cast_oppening, voter.proposal.g, voter.proposal.collector, voter.proposal.encrypt_spec)

    return Vote(proposal_hash, C, A, cast_oppening_enc, signer)
end

struct TallyRecord{G <: Group}
    T::G
    tracker::BigInt
    selection::BigInt
end

struct Tally{G <: Group} <: Proposition
    proposal::Proposal
    cast_commitments::Vector{G}
    vote_commitments::Vector{SignedVoteCommitment{G}}
    skip_list::Vector{G} # In case voter had cast a vote with other means
    tokens::Vector{<:Integer}
    tally::Vector{TallyRecord{G}}
end

struct TallyProof{G <: Group} <: Proof
    supersession::SupersessionProof{G}
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
    width = [length(i.history) for i in cast_oppenings]
    
    mask = extract_maximum_mask(pseudonyms, width)

    return mask
end

function compute_tokens(ux::Vector{G}, challenges::Vector{UInt8}, token_max::Int, watermark_nbits::Int, hasher::HashSpec) where G <: Group

    prg = PRG(hasher, [octet(prod(ux)); challenges])

    nbits = ndigits(token_max, base=2) - 1
    offset = token_max - 2^nbits

    token_seeds = rand(prg, 0:2^nbits - 1, length(ux))
    tokens = [apply_watermark(ti, nbits, octet(uxi), hasher; num_positions = watermark_nbits) + offset for (ti, uxi) in zip(token_seeds, ux)]
    
    return tokens
end

function tally(proposal::Proposal, cast_commitments::Vector{G}, cast_oppenings::Vector{CastOppening{G}}, hasher::HashSpec; skip_list = G[], mask = extract_supersession(cast_oppenings)) where G <: Group

    (; token_max, watermark_nbits) = proposal

    public_cast_oppenings = @view(cast_oppenings[mask])
    
    pseudonyms = (i.commitment.signature.pbkey for i in public_cast_oppenings)
    u = [map2generator(pi, hasher) for pi in pseudonyms]
    ux = [i.commitment.ux for i in public_cast_oppenings] # will be significant

    skip_mask = BitVector(!(x in skip_list) for x in pseudonyms)

    challenges = (i.commitment.challenge for i in public_cast_oppenings)
    tokens = compute_tokens(ux, Iterators.flatten(challenges) |> collect, token_max, watermark_nbits, hasher)

    tracker_challenges = [tracker_challenge(i.commitment.ux, i.commitment.challenge, ti, hasher) for (i, ti) in zip(@view(public_cast_oppenings[skip_mask]), @view(tokens[skip_mask]))]

    vote_oppenings = (i.oppening for i in @view(public_cast_oppenings[skip_mask])) # added here
    trackers = (tracker(oppening, chg, proposal.basis) for (chg, oppening) in zip(tracker_challenges, vote_oppenings))

    tally = TallyRecord{G}[TallyRecord(Ti, octet2int(hasher(octet(Ti))[1:8]), oppening.selection) for (Ti, oppening) in zip(trackers, vote_oppenings)]

    vote_commitments = [i.commitment for i in public_cast_oppenings]

    return Tally(proposal, cast_commitments, vote_commitments, skip_list, tokens, tally)
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

function prove(proposition::Tally{G}, verifier::Verifier, cast_oppenings::Vector{CastOppening{G}}, 𝛙_reveal::Vector{Int}; mask = extract_supersession(cast_oppenings), roprg = gen_roprg()) where G <: Group

    hasher = verifier.prghash

    u = [map2generator(i.signature.pbkey, hasher) for i in proposition.vote_commitments]
    ux = [i.ux for i in proposition.vote_commitments]
    pok = [i.pok for i in proposition.vote_commitments]

    history = [i.history for i in @view(cast_oppenings[mask])]

    ψ, α = reduce_representation(cast_oppenings, u, ux, history, hasher)
    β = [i.β for i in cast_oppenings]

    supersession_proposition = Supersession(proposition.cast_commitments, proposition.proposal.basis.h, u, ux, pok)

    supersession_proof = prove(supersession_proposition, verifier, ψ, β, α; roprg = gen_roprg(roprg(:supersession))) 
    skip_mask = BitVector(!(x.signature.pbkey in proposition.skip_list) for x in proposition.vote_commitments)

    tracker_challenges = [tracker_challenge(i.ux, i.challenge, ti, hasher) for (i, ti) in zip(@view(proposition.vote_commitments[skip_mask]), @view(proposition.tokens[skip_mask]))]

    vote_commitments = [i.commitment for i in proposition.vote_commitments]
    reveal_proposition = RevealShuffle(proposition.proposal.basis, tracker_challenges, vote_commitments[skip_mask], [VoteRecord(i.T, i.selection) for i in proposition.tally])

    vote_oppenings = [i.oppening for i in @view(cast_oppenings[mask][skip_mask])]

    reveal_proof = prove(reveal_proposition, verifier, vote_oppenings, 𝛙_reveal; roprg = gen_roprg(roprg(:reveal)))    

    return TallyProof(supersession_proof, reveal_proof)
end

function tally(proposal::Proposal, cast_commitments::Vector{G}, cast_oppenings::Vector{CastOppening{G}}, verifier::Verifier; skip_list = G[]) where G <: Group

    hasher = verifier.prghash

    filter_mask = extract_supersession(cast_oppenings)
    commit_perm = sortperm(@view(cast_oppenings[filter_mask]); by = x -> x.commitment.signature.pbkey)
    
    mask = findall(filter_mask)[commit_perm]

    proposition = tally(proposal, cast_commitments, cast_oppenings, hasher; skip_list, mask)

    𝛙 = sortperm(proposition.tally, by = x -> x.tracker)
    permute!(proposition.tally, 𝛙)

    proof = prove(proposition, verifier, cast_oppenings, 𝛙; mask) 

    return Simulator(proposition, proof, verifier)    
end

function verify(proposition::Tally{G}, proof::TallyProof{G}, verifier::Verifier) where G <: Group
    
    hasher = verifier.prghash

    (; h, d, t, o) = proposition.proposal.basis
    proposition.proposal.basis == GeneratorSetup(h, d, t, o) || return false
    
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
    tokens = compute_tokens(ux, Iterators.flatten(challenges) |> collect, token_max, watermark_nbits, hasher)
    proposition.tokens == tokens || return false

    tracker_challenges = [tracker_challenge(i.ux, i.challenge, ti, hasher) for (i, ti) in zip(@view(vote_commitments[skip_mask]), @view(tokens[skip_mask]))]

    reveal_vote_commitments = [i.commitment for i in @view(vote_commitments[skip_mask])]
    reveal_proposition = RevealShuffle(proposition.proposal.basis, tracker_challenges, reveal_vote_commitments, [VoteRecord(i.T, i.selection) for i in proposition.tally])

    verify(reveal_proposition, proof.reveal, verifier) || return false
    
    return true
end
