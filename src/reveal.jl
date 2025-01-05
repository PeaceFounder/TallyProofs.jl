using CryptoGroups: Group, order, octet
using SigmaProofs: Proposition, Proof, Verifier, Simulator
using SigmaProofs.ElGamal: ElGamalRow
using ShuffleProofs: Shuffle, PoSProof
import SigmaProofs: prove, verify, proof_type

struct GeneratorSetup{G <: Group}
    h::G # blinding generator
    d::G # tracker generator
    o::G
end

Base.:(==)(x::T, y::T) where T <: GeneratorSetup = x.h == y.h && x.d == y.d && x.o == y.o

struct VoteCommitment{G <: Group}
    Q::G # tracker commitment
    R::G # vote commitment with tracker blinding generator
    V::G
end

function tracker_commitment(vote::VoteCommitment, e::BigInt)
    (; Q, R) = vote
    return Q^e * R
end

vote_commitment(vote::VoteCommitment) = vote.V

struct TrackerOppening
    # Q
    α::BigInt # blinding factors for tracker
    λ::BigInt

    # R
    β::BigInt # blinding factor for vote and tracker blinding factor
    θ::BigInt # blinding factor for the generator
end

function TrackerOppening(range::UnitRange{<:Integer}; roprg = gen_roprg())

    α = rand(roprg(:α), range)
    λ = rand(roprg(:λ), range)

    β = rand(roprg(:β), range)
    θ = rand(roprg(:θ), range)

    return TrackerOppening(α, λ, β, θ)
end


struct VoteOppening # order changed
    tracker::TrackerOppening
    selection::BigInt #NTuple{N, BigInt}
    γ::BigInt
end

function VoteOppening(tracker::TrackerOppening, selection::Integer, range::UnitRange{<:Integer}; roprg = gen_roprg()) 
    γ = rand(roprg(:β), range)
    return VoteOppening(tracker, selection, γ)
end

function commitment(oppening::TrackerOppening, setup::GeneratorSetup{G}) where G <: Group

    (; h, d) = setup
    (; α, β, λ, θ) = oppening
    
    Q = h^α * d^λ
    R = iszero(β) ? d^θ : h^β * d^θ # A temporary fix

    return (Q, R)
end

function commitment(oppening::VoteOppening, setup::GeneratorSetup{G}) where G <: Group 
    
    (; h, o) = setup
    (; γ, selection) = oppening

    Q, R = commitment(oppening.tracker, setup)

    if iszero(γ) 
        V = iszero(selection) ? one(G) : o^selection
    else
        V = iszero(selection) ? h^γ : h^γ * o^selection
    end
    
    return VoteCommitment(Q, R, V)
end

function isbinding(C::VoteCommitment{G}, oppening::VoteOppening, setup::GeneratorSetup{G}) where {G <: Group}
    return C == commitment(oppening, setup)
end

struct VoteRecord
    tracker::BigInt
    selection::BigInt
end

function tracker_commitment(record::VoteRecord, setup::GeneratorSetup{G}) where G <: Group

    (; tracker) = record
    (; d) = setup

    T = d^tracker

    return T
end

function vote_commitment(record::VoteRecord, setup::GeneratorSetup{G}) where {G <: Group} 

    (; tracker, selection) = record
    (; o) = setup

    V = iszero(selection) ? one(G) : o^selection

    return V
end

struct RevealShuffle{G <: Group} <: Proposition
    setup::GeneratorSetup{G}
    tracker_challenges::Vector{BigInt}
    vote_commitments::Vector{VoteCommitment{G}} 
    tally::Vector{VoteRecord} 
end

Base.length(proposition::RevealShuffle) = length(proposition.vote_commitments)

Base.permute!(proposition::RevealShuffle, ψ::Vector{Int}) = permute!(proposition.tally, ψ)

struct RevealShuffleProof{G <: Group} <: Proof
    shuffle::PoSProof{G, 2} # I will need to upgrade this to 2
    trackers::Vector{LambdaProof{G}}
end

proof_type(::Type{RevealShuffle{G}}) where {G <: Group} = RevealShuffleProof{G}

function tracker(θ::Integer, λ::Integer, chg::Integer, order::Integer)
    t = θ + λ * chg
    return mod(t, order)
end

function tracker(tracker_oppening::TrackerOppening, chg::Integer, order::Integer) #, setup::GeneratorSetup)
    (; θ, λ) = tracker_oppening
    return tracker(θ, λ, chg, order)
end

function tracker(vote_oppening::VoteOppening, chg::Integer, order::Integer) #, setup::GeneratorSetup)
    return tracker(vote_oppening.tracker, chg, order)
end

function reveal(setup::GeneratorSetup{G}, tracker_challenges::Vector{BigInt}, vote_commitments::Vector{VoteCommitment{G}}, vote_oppenings::Vector{<:VoteOppening}) where {G <: Group}
    
    tally = VoteRecord[VoteRecord(tracker(oppening, chg, order(setup.d)), oppening.selection) for (chg, oppening) in zip(tracker_challenges, vote_oppenings)]

    return RevealShuffle(setup, tracker_challenges, vote_commitments, tally)
end

function reveal(setup::GeneratorSetup{G}, tracker_challenges::Vector{BigInt}, vote_commitments::Vector{VoteCommitment{G}}, vote_oppenings::Vector{<:VoteOppening}, verifier::Verifier; roprg = gen_roprg()) where G <: Group

    proposition = reveal(setup, tracker_challenges, vote_commitments, vote_oppenings)
    
    𝛙 = sortperm(proposition.tally, by = x -> x.tracker)
    permute!(proposition, 𝛙)

    proof = prove(proposition, verifier, vote_oppenings, 𝛙; roprg)

    return Simulator(proposition, proof, verifier)
end

function prove(proposition::RevealShuffle{G}, verifier::Verifier, vote_oppenings::AbstractVector{<:VoteOppening}, 𝛙::Vector{<:Integer}; roprg = gen_roprg()) where G <: Group

    (; setup, tally, tracker_challenges, vote_commitments) = proposition
    (; h, d) = proposition.setup

    𝐫T = [- i.tracker.β - i.tracker.α * ei for (i, ei) in zip(vote_oppenings, tracker_challenges)]
    𝐫V = [-i.γ for i in vote_oppenings]
    𝐫′ = [𝐫T 𝐫V] # 

    T_vec = (tracker_commitment(com, chg) for (com, chg) in zip(vote_commitments, tracker_challenges))
    V_vec = (vote_commitment(com) for com in vote_commitments)
    𝐞 = [ElGamalRow((Ti, Vi), (Ti, Vi)) for (Ti, Vi) in zip(T_vec, V_vec)]

    T′_vec = (tracker_commitment(votei, setup) for votei in tally)
    V′_vec = (vote_commitment(votei, setup) for votei in tally)
    𝐞′ = [ElGamalRow((Ti, Vi), (Ti, Vi)) for (Ti, Vi) in zip(T′_vec, V′_vec)]
    
    shuffle_proposition = Shuffle(h, h, 𝐞, 𝐞′)

    shuffle_proof = prove(shuffle_proposition, verifier, 𝐫′, 𝛙; roprg)

    Q_vec = (i.Q for i in vote_commitments)

    α = (i.tracker.α for i in vote_oppenings)
    λ = (i.tracker.λ for i in vote_oppenings)

    lambda_proofs = [prove(LambdaCommitment(h, d, Qi), verifier, λi, αi; roprg = gen_roprg(roprg("$Qi"))) for (Qi, λi, αi) in zip(Q_vec, λ, α)]
    
    return RevealShuffleProof(shuffle_proof, lambda_proofs)
end


function verify(proposition::RevealShuffle{G}, proof::RevealShuffleProof{G}, verifier::Verifier) where G <: Group

    (; setup, tally, tracker_challenges, vote_commitments) = proposition
    (; h, d, o) = proposition.setup

    T_vec = (tracker_commitment(com, chg) for (com, chg) in zip(vote_commitments, tracker_challenges))
    V_vec = (vote_commitment(com) for com in vote_commitments)
    𝐞 = [ElGamalRow((Ti, Vi), (Ti, Vi)) for (Ti, Vi) in zip(T_vec, V_vec)]

    T′_vec = (tracker_commitment(votei, setup) for votei in tally)
    V′_vec = (vote_commitment(votei, setup) for votei in tally)
    𝐞′ = [ElGamalRow((Ti, Vi), (Ti, Vi)) for (Ti, Vi) in zip(T′_vec, V′_vec)]

    shuffle_proposition = Shuffle(h, h, 𝐞, 𝐞′)

    verify(shuffle_proposition, proof.shuffle, verifier) || return false

    Q_vec = (i.Q for i in proposition.vote_commitments)

    for (Qi, pok) in zip(Q_vec, proof.trackers)

        verify(LambdaCommitment(h, d, Qi), pok, verifier) || return false

    end

    return true
end
