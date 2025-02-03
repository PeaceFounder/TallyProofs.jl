using CryptoGroups: Group, order, octet
using SigmaProofs: Proposition, Proof, Verifier, Simulator
using SigmaProofs.ElGamal: ElGamalRow
using ShuffleProofs: Shuffle, PoSProof
import SigmaProofs: prove, verify, proof_type

struct GeneratorSetup{G <: Group}
    h::G # blinding generator
    g::G
end

Base.:(==)(x::T, y::T) where T <: GeneratorSetup = x.h == y.h && x.g == y.g

struct VoteCommitment{G <: Group}
    Q::G
    R::G
    V::G
end

Base.:(==)(x::T, y::T) where T <: VoteCommitment = x.Q == y.Q && x.R == y.R && x.V == y.V

function tracker_commitment(vote::VoteCommitment, e::BigInt)
    (; Q, R) = vote
    return Q^e * R
end

vote_commitment(vote::VoteCommitment) = vote.V

struct TrackerOpening
    # Q
    α::BigInt # blinding factors for tracker
    λ::BigInt

    # R
    β::BigInt # blinding factor for vote and tracker blinding factor
    θ::BigInt # blinding factor for the generator
end

function TrackerOpening(range::UnitRange{<:Integer}; roprg = gen_roprg())

    α = rand(roprg(:α), range)
    λ = rand(roprg(:λ), range)

    β = rand(roprg(:β), range)
    θ = rand(roprg(:θ), range)

    return TrackerOpening(α, λ, β, θ)
end

Base.:(==)(x::T, y::T) where T <: TrackerOpening = x.α == y.α && x.λ == y.λ && x.β == y.β && x.θ == y.θ

struct VoteOpening # order changed
    tracker::TrackerOpening
    selection::BigInt #NTuple{N, BigInt}
    γ::BigInt
end

function VoteOpening(tracker::TrackerOpening, selection::Integer, range::UnitRange{<:Integer}; roprg = gen_roprg()) 
    γ = rand(roprg(:β), range)
    return VoteOpening(tracker, selection, γ)
end

function commitment(opening::TrackerOpening, setup::GeneratorSetup{G}) where G <: Group

    (; h, g) = setup
    (; α, β, λ, θ) = opening
    
    Q = h^α * g^λ
    R = h^β * g^θ

    return (Q, R)
end

function commitment(opening::VoteOpening, setup::GeneratorSetup{G}) where G <: Group 
    
    #(; h, o) = setup
    (; h, g) = setup
    (; γ, selection) = opening

    Q, R = commitment(opening.tracker, setup)

    if iszero(γ) 
        V = iszero(selection) ? one(G) : g^selection
    else
        V = iszero(selection) ? h^γ : h^γ * g^selection
    end
    
    return VoteCommitment(Q, R, V)
end

function isbinding(C::VoteCommitment{G}, opening::VoteOpening, setup::GeneratorSetup{G}) where {G <: Group}
    return C == commitment(opening, setup)
end

struct VoteRecord
    tracker::BigInt
    selection::BigInt
end

function tracker_commitment(record::VoteRecord, setup::GeneratorSetup{G}) where G <: Group

    (; tracker) = record
    (; g) = setup

    T = g^tracker

    return T
end

function vote_commitment(record::VoteRecord, setup::GeneratorSetup{G}) where {G <: Group} 

    (; tracker, selection) = record
    (; g) = setup

    V = iszero(selection) ? one(G) : g^selection

    return V
end

struct TallyBoard{G <: Group} <: Proposition
    setup::GeneratorSetup{G}
    tracker_challenges::Vector{BigInt}
    vote_commitments::Vector{VoteCommitment{G}} 
    tally_board::Vector{VoteRecord} 
end

Base.length(proposition::TallyBoard) = length(proposition.vote_commitments)

Base.permute!(proposition::TallyBoard, ψ::Vector{Int}) = permute!(proposition.tally_board, ψ)

struct TallyBoardProof{G <: Group} <: Proof
    shuffle::PoSProof{G, 2} # I will need to upgrade this to 2
    trackers::Vector{LambdaProof{G}}
end

proof_type(::Type{TallyBoard{G}}) where {G <: Group} = TallyBoardProof{G}

function tracker(θ::Integer, λ::Integer, chg::Integer, order::Integer)
    t = θ + λ * chg
    return mod(t, order)
end

function tracker(tracker_opening::TrackerOpening, chg::Integer, order::Integer) #, setup::GeneratorSetup)
    (; θ, λ) = tracker_opening
    return tracker(θ, λ, chg, order)
end

function tracker(vote_opening::VoteOpening, chg::Integer, order::Integer) #, setup::GeneratorSetup)
    return tracker(vote_opening.tracker, chg, order)
end

function reveal(setup::GeneratorSetup{G}, tracker_challenges::Vector{BigInt}, vote_commitments::Vector{VoteCommitment{G}}, vote_openings::Vector{<:VoteOpening}) where {G <: Group}
    
    tally = VoteRecord[VoteRecord(tracker(opening, chg, order(G)), opening.selection) for (chg, opening) in zip(tracker_challenges, vote_openings)]

    return TallyBoard(setup, tracker_challenges, vote_commitments, tally)
end

function reveal(setup::GeneratorSetup{G}, tracker_challenges::Vector{BigInt}, vote_commitments::Vector{VoteCommitment{G}}, vote_openings::Vector{<:VoteOpening}, verifier::Verifier; roprg = gen_roprg()) where G <: Group

    proposition = reveal(setup, tracker_challenges, vote_commitments, vote_openings)
    
    𝛙 = sortperm(proposition.tally_board, by = x -> x.tracker)
    permute!(proposition, 𝛙)

    proof = prove(proposition, verifier, vote_openings, 𝛙; roprg)

    return Simulator(proposition, proof, verifier)
end

function prove(proposition::TallyBoard{G}, verifier::Verifier, vote_openings::AbstractVector{<:VoteOpening}, 𝛙::Vector{<:Integer}; roprg = gen_roprg()) where G <: Group

    (; setup, tally_board, tracker_challenges, vote_commitments) = proposition
    (; h, g) = proposition.setup

    𝐫T = [- i.tracker.β - i.tracker.α * ei for (i, ei) in zip(vote_openings, tracker_challenges)]
    𝐫V = [-i.γ for i in vote_openings]
    𝐫′ = [𝐫T 𝐫V] # 

    T_vec = (tracker_commitment(com, chg) for (com, chg) in zip(vote_commitments, tracker_challenges))
    V_vec = (vote_commitment(com) for com in vote_commitments)
    𝐞 = [ElGamalRow((Ti, Vi), (Ti, Vi)) for (Ti, Vi) in zip(T_vec, V_vec)]

    T′_vec = (tracker_commitment(votei, setup) for votei in tally_board)
    V′_vec = (vote_commitment(votei, setup) for votei in tally_board)
    𝐞′ = [ElGamalRow((Ti, Vi), (Ti, Vi)) for (Ti, Vi) in zip(T′_vec, V′_vec)]
    
    shuffle_proposition = Shuffle(h, h, 𝐞, 𝐞′)

    shuffle_proof = prove(shuffle_proposition, verifier, 𝐫′, 𝛙; roprg)

    Q_vec = (i.Q for i in vote_commitments)

    α = (i.tracker.α for i in vote_openings)
    λ = (i.tracker.λ for i in vote_openings)

    lambda_proofs = [prove(LambdaCommitment(h, g, Qi), verifier, λi, αi; roprg = gen_roprg(roprg("$Qi"))) for (Qi, λi, αi) in zip(Q_vec, λ, α)]
    
    return TallyBoardProof(shuffle_proof, lambda_proofs)
end


function verify(proposition::TallyBoard{G}, proof::TallyBoardProof{G}, verifier::Verifier) where G <: Group

    (; setup, tally_board, tracker_challenges, vote_commitments) = proposition
    (; h, g) = proposition.setup

    T_vec = (tracker_commitment(com, chg) for (com, chg) in zip(vote_commitments, tracker_challenges))
    V_vec = (vote_commitment(com) for com in vote_commitments)
    𝐞 = [ElGamalRow((Ti, Vi), (Ti, Vi)) for (Ti, Vi) in zip(T_vec, V_vec)]

    T′_vec = (tracker_commitment(votei, setup) for votei in tally_board)
    V′_vec = (vote_commitment(votei, setup) for votei in tally_board)
    𝐞′ = [ElGamalRow((Ti, Vi), (Ti, Vi)) for (Ti, Vi) in zip(T′_vec, V′_vec)]

    shuffle_proposition = Shuffle(h, h, 𝐞, 𝐞′)

    verify(shuffle_proposition, proof.shuffle, verifier) || return false

    Q_vec = (i.Q for i in proposition.vote_commitments)

    for (Qi, pok) in zip(Q_vec, proof.trackers)

        verify(LambdaCommitment(h, g, Qi), pok, verifier) || return false

    end

    return true
end
