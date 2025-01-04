using CryptoGroups: Group, order, octet
using SigmaProofs: Proposition, Proof, Verifier, Simulator
using SigmaProofs.ElGamal: ElGamalRow
using ShuffleProofs: Shuffle, PoSProof
import SigmaProofs: prove, verify, proof_type

struct GeneratorSetup{G <: Group}
    h::G # blinding generator
    d::G # tracker generator
#    t::G # tracker generator
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

struct VoteOppening # order changed
    # Q
    α::BigInt # blinding factors for tracker
    λ::BigInt

    # R
    β::BigInt # blinding factor for vote and tracker blinding factor
    θ::BigInt # blinding factor for the generator
    
    # V
    γ::BigInt
    selection::BigInt #NTuple{N, BigInt}
end

# Why is β a keyword paremeter here
function vote_oppening(selection::Integer, range::UnitRange{<:Integer}; roprg = gen_roprg(), β = rand(roprg(:β), range)) 

    α = rand(roprg(:α), range)
    λ = rand(roprg(:λ), range)

    θ = rand(roprg(:θ), range)

    γ = rand(roprg(:γ), range)

    #return VoteOppening(α, θ, λ, β, selection)
    return VoteOppening(α, λ, β, θ, γ, selection)
end

#function vote_commitment(oppening::VoteOppening, setup::GeneratorSetup{<:Group})

function VoteCommitment(oppening::VoteOppening, setup::GeneratorSetup{G}) where G <: Group

    (; h, d, o) = setup
    #(; α, β, λ, θ, selection) = oppening
    (; α, β, γ, λ, θ, selection) = oppening

    #Q = h^α * t^λ
    Q = h^α * d^λ

    
    #R = h^β * d^θ
    R = iszero(β) ? d^θ : h^β * d^θ # A temporary fix

    if iszero(γ) 
        V = iszero(selection) ? one(G) : o^selection
    else
        V = iszero(selection) ? h^γ : h^γ * o^selection
    end

    return VoteCommitment(Q, R, V)
end

function isbinding(commitment::VoteCommitment{G}, oppening::VoteOppening, setup::GeneratorSetup{G}) where {G <: Group}
    return commitment == vote_commitment(oppening, setup)
end

struct VoteRecord
    #tracker::G
    tracker::BigInt
    selection::BigInt
end

# function commitment(record::VoteRecord, s::BigInt, setup::GeneratorSetup{G}) where {G <: Group}

#     (; tracker, selection) = record
#     (; h, d, o) = setup

#     C = iszero(selection) ? h^s * d^tracker : h^s * d^tracker * o^selection

#     return C
# end


# I will need tracker_commitment and vote_commitment

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


# function commitment(record::VoteRecord, setup::GeneratorSetup{G}) where {G <: Group} 

#     (; tracker, selection) = record
#     (; d, o) = setup

#     C = iszero(selection) ? d^tracker : d^tracker * o^selection

#     return C
# end



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
    #s::Vector{BigInt}
    trackers::Vector{LambdaProof{G}}
end

proof_type(::Type{RevealShuffle{G}}) where {G <: Group} = RevealShuffleProof{G}

function tracker(θ::Integer, λ::Integer, chg::Integer, order::Integer)
    t = θ + λ * chg
    return mod(t, order)
end

function tracker(vote_oppening::VoteOppening, chg::Integer, order::Integer) #, setup::GeneratorSetup)
    (; θ, λ) = vote_oppening
    return tracker(θ, λ, chg, order)
end

function reveal(setup::GeneratorSetup{G}, tracker_challenges::Vector{BigInt}, vote_commitments::Vector{VoteCommitment{G}}, vote_oppenings::Vector{<:VoteOppening}) where {G <: Group}
    
    #(; d, o) = setup

    #tally = VoteRecord{G}[VoteRecord(tracker(oppening, chg, setup), oppening.selection) for (chg, oppening) in zip(tracker_challenges, vote_oppenings)]
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

    #𝐫′ = rand(roprg(:𝐫′), 2:order(G)-1, length(vote_commitments))

    # α = (i.α for i in vote_oppenings)
    # β = (i.β for i in vote_oppenings)

    #s = α .* tracker_challenges .+ β + 𝐫′
    #permute!(s, 𝛙)

    #𝐫′ = mod.( .- β .- α .* tracker_challenges, order(G))
    #𝐫T = .- β .- α .* tracker_challenges
    𝐫T = [- i.β - i.α * ei for (i, ei) in zip(vote_oppenings, tracker_challenges)]
    𝐫V = [-i.γ for i in vote_oppenings]
    
    #𝐫′ = [𝐫T 𝐫V]
    𝐫′ = [𝐫T 𝐫V] # 

    #C_vec = (commitment(com, chg) for (com, chg) in zip(vote_commitments, tracker_challenges))
    T_vec = (tracker_commitment(com, chg) for (com, chg) in zip(vote_commitments, tracker_challenges))
    V_vec = (vote_commitment(com) for com in vote_commitments)
    𝐞 = [ElGamalRow((Ti, Vi), (Ti, Vi)) for (Ti, Vi) in zip(T_vec, V_vec)]

    #C′_vec = (commitment(votei, si, setup) for (votei, si) in zip(tally, s))
    #C′_vec = (commitment(votei, setup) for votei in tally)
    T′_vec = (tracker_commitment(votei, setup) for votei in tally)
    V′_vec = (vote_commitment(votei, setup) for votei in tally)
    𝐞′ = [ElGamalRow((Ti, Vi), (Ti, Vi)) for (Ti, Vi) in zip(T′_vec, V′_vec)]
    

    shuffle_proposition = Shuffle(h, h, 𝐞, 𝐞′)

    shuffle_proof = prove(shuffle_proposition, verifier, 𝐫′, 𝛙; roprg)

    #trackers = (i.tracker for i in tally)

    Q_vec = (i.Q for i in vote_commitments)

    #θ = (i.θ for i in @view(vote_oppenings[𝛙]))
    #λ = (i.λ for i in @view(vote_oppenings[𝛙]))

    α = (i.α for i in vote_oppenings)
    λ = (i.λ for i in vote_oppenings)

    lambda_proofs = [prove(LambdaCommitment(h, d, Qi), verifier, λi, αi; roprg = gen_roprg(roprg("$Qi"))) for (Qi, λi, αi) in zip(Q_vec, λ, α)]
    
    
    #return RevealShuffleProof(shuffle_proof, s, lambda_proofs)
    return RevealShuffleProof(shuffle_proof, lambda_proofs)
end


function verify(proposition::RevealShuffle{G}, proof::RevealShuffleProof{G}, verifier::Verifier) where G <: Group

    (; setup, tally, tracker_challenges, vote_commitments) = proposition
    (; h, d, o) = proposition.setup

    T_vec = (tracker_commitment(com, chg) for (com, chg) in zip(vote_commitments, tracker_challenges))
    V_vec = (vote_commitment(com) for com in vote_commitments)
    𝐞 = [ElGamalRow((Ti, Vi), (Ti, Vi)) for (Ti, Vi) in zip(T_vec, V_vec)]
    #𝐞 = [ElGamalRow(Ti, Ti) for Ti in T_vec]

    #C′_vec = (commitment(votei, si, setup) for (votei, si) in zip(tally, proof.s))
    T′_vec = (tracker_commitment(votei, setup) for votei in tally)
    V′_vec = (vote_commitment(votei, setup) for votei in tally)
    𝐞′ = [ElGamalRow((Ti, Vi), (Ti, Vi)) for (Ti, Vi) in zip(T′_vec, V′_vec)]

    #𝐞′ = [ElGamalRow(Ti, Ti) for Ti in T′_vec]

    shuffle_proposition = Shuffle(h, h, 𝐞, 𝐞′)

    verify(shuffle_proposition, proof.shuffle, verifier) || return false

    Q_vec = (i.Q for i in proposition.vote_commitments)

    for (Qi, pok) in zip(Q_vec, proof.trackers)

        verify(LambdaCommitment(h, d, Qi), pok, verifier) || return false

    end

    return true
end
