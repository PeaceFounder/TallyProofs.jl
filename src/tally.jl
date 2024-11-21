using CryptoGroups: Group, order, octet
using CryptoGroups.Utils: int2octet!, octet2int, @check
using CryptoPRG: HashSpec
using CryptoPRG.Verificatum: PRG
using SigmaProofs: Proposition, Proof, Verifier, Simulator
using SigmaProofs.LogProofs: SchnorrProof, LogKnowledge
using SigmaProofs.Parser: Tree, encode
using SigmaProofs.Verificatum: generator_basis, GeneratorBasis
import SigmaProofs: prove, verify, proof_type


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
    tracker::Vector{UInt8} # set up after the vote
end

struct CoercedVote{G <: Group} # When coercion tracker is put in it can be reduced to CoercionInfo
    pin::Int
    θ::BigInt
    λ::BigInt
    T_d::G
    T_t::G
end

struct Proposal{G <: Group}
    generator::G
    collector::G
    range::UnitRange
end

struct VotingCalculator{G} # More preciselly it would be VotingCalculatorInstance
    proposal::Proposal{G}

    verifier::Verifier
    hasher::HashSpec # We shall also take it from the verifier
    setup::GeneratorSetup # we shall generate it from the Verifier. The blinding generator shall also be reused

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

    unresolved_coercions::Vector{CoercedVote}
    coercion_trackers::Vector{CoercionTracker}
end

function VotingCalculator(proposal::Proposal{G}, verifier::Verifier, key::Integer, pin::Int; roprg = gen_roprg()) where G <: Group
    
    hasher = verifier.prghash # the verifier could implement hasher method

    h, d, t, o = generator_basis(verifier, G, 4)

    setup = GeneratorSetup(h, d, t, o)

    pseudonym = proposal.generator^key

    u = map2generator(pseudonym, hasher)
    sup_calc = SupersessionCalculator(h, u, verifier)

    challenge = rand(UInt8, 32) # I could use roprg here perhaps

    θ = rand(roprg(:θ), 2:order(G) - 1)
    λ = rand(roprg(:λ), 2:order(G) - 1)

    T_d = d^θ
    T_t = t^λ
    
    return VotingCalculator(proposal, verifier, hasher, setup, sup_calc, challenge, pseudonym, key |> BigInt, pin, θ, λ, T_d, T_t, CoercedVote[], CoercionTracker[])
end


function compute_tracker(voter::VotingCalculator, challenge::Integer, pin::Int)

    if voter.pin == pin
        
        (; T_d, T_t, hasher) = voter
        
        T = T_d * T_t^challenge
        return hasher(octet(T))[1:8] |> octet2int
    else
        error("Incoreect PIN code")
    end
end

struct SignedVoteCommitment{G <: Group}
    proposal::Vector{UInt8}
    commitment::VoteCommitment
    ux::G
    pok::SchnorrProof
    challenge::Vector{UInt8}
    signature::Signature # Perhaps here I just can define tree or digest function
end

struct CastOppening{G <: Group}
    #recommit::ReCommit{G}
    β::BigInt # For supersession
    history::Vector{BigInt}
    
    commitment::SignedVoteCommitment{G}
    oppening::VoteOppening # Can be further encrypted in a threshold decryption ceremony if one wishes to have that for fairness
end

struct Vote{G}
    proposal::Vector{UInt8}
    C::G
    A::G
    # A key stuff can also be here
    oppening::CastOppening # this will be encrypted
    signature::Signature
end

function Vote(proposal::Vector{UInt8}, C::G, A::G, oppening::CastOppening, signer::Signer{G}) where G <: Group

    # tree = Tree((proposal, C, A, oppening, signature))
    signature = sign(UInt8[], signer.g, signer.key)
    return Vote(proposal, C, A, oppening, signature)
end

function verify(vote::Vote{G}, g::G) where G <: Group

    return verify(UInt8[], g, vote.signature)
end

function check_challenge(vote::Vote{G}, chg::Integer, hasher::HashSpec) where G <: Group
    u = map2generator(vote.signature.pbkey, hasher)
    return check_challenge(vote.C, vote.A, u, chg, hasher) 
end

function SignedVoteCommitment(proposal::Vector{UInt8}, commitment::VoteCommitment{G}, ux::G, pok::SchnorrProof, challenge::Vector{UInt8}, signer::Signer{G}) where G <: Group

    # tree = Tree((commitment, ux, pok, blinded_challenge
    internal_signature = sign(UInt8[], signer.g, signer.key)

    return SignedVoteCommitment(proposal, commitment, ux, pok, challenge, internal_signature)
end


function assemble_vote!(voter::VotingCalculator{G}, selection::Integer, chg::Integer, pin::Int; inherit_challenge=false, roprg = gen_roprg()) where G <: Group

    C, A, sup_oppening = TallyProofs.recommit!(voter.supersession, chg) 
    (; β, history, ux, pok) = sup_oppening

    _α = rand(roprg(:α), 2:order(G) - 1)
    _β = rand(roprg(:β), 2:order(G) - 1)
    
    oppening = VoteOppening(_α, voter.θ, voter.λ, _β, selection)
    commitment = vote_commitment(oppening, voter.setup)

    buffer = zeros(UInt8, 16)
    int2octet!(buffer, chg |> BigInt) # TODO: CryptoGroups bug!!!
    blinded_challenge = voter.hasher([buffer; octet(A)])

    copyto!(voter.challenge, blinded_challenge)

    signer = Signer(voter.proposal.generator, voter.key)

    proposal_hash = UInt8[]

    signed_vote_commitment = SignedVoteCommitment(proposal_hash, commitment, ux, pok, blinded_challenge, signer)

    cast_oppening = CastOppening(β, history, signed_vote_commitment, oppening)

    return Vote(proposal_hash, C, A, cast_oppening, signer)
end


struct TallyRecord{G <: Group}
    T::G
    tracker::BigInt
    selection::BigInt
end

struct Tally{G <: Group} <: Proposition
    setup::GeneratorSetup # we shall instantiate generators from a verifier
    tracker_range::UnitRange
    cast_commitments::Vector{G}
    vote_commitments::Vector{SignedVoteCommitment{G}}
    skip_list::Vector{G} # In case voter had cast a vote with other means
    tracker_challenges::Vector{<:Integer} # we do need a prghash for calculation which we can pass to a tally function argument
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

function tally(setup::GeneratorSetup{G}, cast_commitments::Vector{G}, cast_oppenings::Vector{CastOppening{G}}, hasher::HashSpec; skip_list = G[], mask = extract_supersession(cast_oppenings), tracker_range = 1:9999_9999) where G <: Group

    public_cast_oppenings = @view(cast_oppenings[mask])

    pseudonyms = [i.commitment.signature.pbkey for i in cast_oppenings]
    u = [map2generator(pi, hasher) for pi in @view(pseudonyms[mask])]
    ux = [i.commitment.ux for i in public_cast_oppenings] # will be significant
    
    buffer = IOBuffer()
    for i in public_cast_oppenings
        write(buffer, i.commitment.challenge)
    end

    prg = PRG(hasher, [octet(prod(ux)); take!(buffer)])
    tracker_challenges = rand(prg, tracker_range, length(ux))

    # Here we would need to follow up with tracker challenge invalidation
    _tracker_challenges = tracker_challenges .|> BigInt

    vote_oppenings = (i.oppening for i in public_cast_oppenings)
    trackers = (tracker(oppening, chg, setup) for (chg, oppening) in zip(_tracker_challenges, vote_oppenings))

    tally = TallyRecord{G}[TallyRecord(Ti, octet2int(hasher(octet(Ti))[1:8]), oppening.selection) for (Ti, oppening) in zip(trackers, vote_oppenings)]

    vote_commitments = [i.commitment for i in public_cast_oppenings]

    return Tally(setup, tracker_range, cast_commitments, vote_commitments, skip_list, _tracker_challenges, tally)
end


function reduce_representation(cast_oppenings::Vector{CastOppening{G}}, u::Vector{G}, ux::Vector{G}, history::Vector{Vector{BigInt}}, hasher::HashSpec) where G <: Group

    pseudonyms = (i.commitment.signature.pbkey for i in cast_oppenings)
    _u = (map2generator(pi, hasher) for pi in pseudonyms)
    _ux = (i.commitment.ux for i in cast_oppenings) # will be significant
    pok = (i.commitment.pok for i in cast_oppenings) # will be significant
    _history = (i.history for i in cast_oppenings)
    β = (i.β for i in cast_oppenings)

    recommits = [ReCommit(βi, ui, uxi, historyi, poki) for (βi, ui, uxi, historyi, poki) in zip(β, _u, _ux, _history, pok)]

    return reduce_representation(recommits, u, ux, history)
end

function prove(proposition::Tally{G}, verifier::Verifier, cast_oppenings::Vector{CastOppening{G}}; mask = extract_supersession(cast_oppenings), roprg = gen_roprg()) where G <: Group

    hasher = verifier.prghash

    u = [map2generator(i.signature.pbkey, hasher) for i in proposition.vote_commitments]
    ux = [i.ux for i in proposition.vote_commitments]
    pok = [i.pok for i in proposition.vote_commitments]
    history = [i.history for i in @view(cast_oppenings[mask])]

    ψ, α = reduce_representation(cast_oppenings, u, ux, history, hasher)
    β = [i.β for i in cast_oppenings]

    supersession_proposition = Supersession(proposition.cast_commitments, proposition.setup.h, u, ux, pok)

    supersession_proof = prove(supersession_proposition, verifier, ψ, β, α) # pok are dublicated. Perhaps I could move pok into proposition

    # tracker_challenges can be different here will need to be recomputed 
    tracker_challenges = proposition.tracker_challenges .|> BigInt

    vote_commitments = [i.commitment for i in proposition.vote_commitments]
    reveal_proposition = RevealShuffle(proposition.setup, tracker_challenges, vote_commitments, [VoteRecord(i.T, i.selection) for i in proposition.tally])

    𝛙 = collect(1:length(reveal_proposition)) # Could be extracted from sortperm
    𝐫′ = rand(roprg(:𝐫′), 2:order(G)-1, length(vote_commitments)) # 𝐫′ is not used in reveal

    vote_oppenings = [i.oppening for i in @view(cast_oppenings[mask])]
    reveal_proof = prove(reveal_proposition, verifier, vote_oppenings, 𝐫′, 𝛙; roprg)    

    return TallyProof(supersession_proof, reveal_proof)
end

### Adding permutation will be a challenge! Evaluating a mask perhaps may be an option
function tally(cast_commitments::Vector{G}, cast_oppenings::Vector{CastOppening{G}}, verifier::Verifier; skip_list = G[]) where G <: Group

    hasher = verifier.prghash
    
    h, d, t, o = generator_basis(verifier, G, 4)
    setup = GeneratorSetup(h, d, t, o)

    mask = extract_supersession(cast_oppenings)

    proposition = tally(setup, cast_commitments, cast_oppenings, hasher; skip_list, mask)
    proof = prove(proposition, verifier, cast_oppenings; mask)

    return Simulator(proposition, proof, verifier)    
end


function verify(proposition::Tally{G}, proof::TallyProof{G}, verifier::Verifier) where G <: Group
    
    hasher = verifier.prghash

    u = [map2generator(i.signature.pbkey, hasher) for i in proposition.vote_commitments]
    ux = [i.ux for i in proposition.vote_commitments]
    pok = [i.pok for i in proposition.vote_commitments]
    
    supersession_proposition = Supersession(proposition.cast_commitments, proposition.setup.h, u, ux, pok)
    verify(supersession_proposition, proof.supersession, verifier) || return false

    tracker_challenges = proposition.tracker_challenges .|> BigInt
    vote_commitments = [i.commitment for i in proposition.vote_commitments]

    reveal_proposition = RevealShuffle(proposition.setup, tracker_challenges, vote_commitments, [VoteRecord(i.T, i.selection) for i in proposition.tally])
    verify(reveal_proposition, proof.reveal, verifier) || return false
    
    return true
end

# any pin code is sufficient 
struct CastReceipt
    alias::Int
    cast_index::Int
    chg::BigInt
end

function tracker_challenge(tally::Tally{G}, cast_proofs::Vector{G}, members::Vector{G}, receipt::CastReceipt, hasher::HashSpec; skip_checks=false, commitment_challenge = receipt.chg) where G <: Group

    (; cast_index, alias, chg) = receipt

    C = tally.cast_commitments[cast_index]
    A = cast_proofs[cast_index]

    pseudonym = members[alias]

    N = findfirst(x -> x.signature.pbkey == pseudonym, tally.vote_commitments)
    vote_commitment = tally.vote_commitments[N]

    u = map2generator(pseudonym, hasher)

    @check !check_challenge(C, A, u, chg, hasher) "Cast challenge is not correct. Vote may not have been delivered to the ballotbox by a malicious voters device or there is an error in either challenge, cast_index or alias. Update history tree consistency proofs to ensure that the commitment had been retained on the buletin board."
    
    if isnothing(commitment_challenge)

        @warn "Skipping vote commitment challenge. It is not possible to assert exclusive ownership of the pseudonym without putting trust into voting calculator or (tallying authorithy and voting device (to not leak secrets to addversary))."
        
    else

        buffer = zeros(UInt8, 16)
        int2octet!(buffer, chg)
        blinded_challenge = hasher([buffer; octet(A)])

        @check blinded_challenge == vote_commitment.challenge "Vote commitment challenge incorrect"

    end
        
    return tally.tracker_challenges[N]
end
