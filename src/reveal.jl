using CryptoGroups: Group, order, octet
using SigmaProofs: Proposition, Proof, Verifier, Simulator
using SigmaProofs.ElGamal: ElGamalRow
using ShuffleProofs: Shuffle, PoSProof
import SigmaProofs: prove, verify, proof_type

struct GeneratorSetup{G <: Group}
    h::G # blinding generator
    d::G # tracker blinding generator
    t::G # tracker generator
    o::G
end

struct VoteCommitment{G <: Group}
    Q::G # tracker commitment
    C::G # vote commitment with tracker blinding generator
end

function commitment(vote::VoteCommitment, e::BigInt)
    (; Q, C) = vote
    return Q^e * C
end

struct VoteOppening
    # Tracker
    α::BigInt # blinding factors for tracker
    θ::BigInt # blinding factor for the generator
    λ::BigInt

    # Vote
    β::BigInt # blinding factor for vote and tracker blinding factor
    selection::BigInt #NTuple{N, BigInt}
end

function vote_oppening(selection::Integer, range::UnitRange{<:Integer}; roprg = gen_roprg()) 

    α = rand(roprg(:α), range)
    θ = rand(roprg(:θ), range)
    λ = rand(roprg(:λ), range)
    β = rand(roprg(:β), range)

    return VoteOppening(α, θ, λ, β, selection)
end

function vote_commitment(oppening::VoteOppening, setup::GeneratorSetup{<:Group})

    (; h, d, t, o) = setup
    (; α, β, λ, θ, selection) = oppening

    Q = h^α * t^λ
    C = h^β * d^θ * o^selection

    return VoteCommitment(Q, C)
end

function isbinding(commitment::VoteCommitment{G}, oppening::VoteOppening, setup::GeneratorSetup{G}) where {G <: Group}
    return commitment == vote_commitment(oppening, setup)
end

struct VoteRecord{G <: Group}
    tracker::G
    selection::BigInt
end

function commitment(record::VoteRecord{G}, s::BigInt, setup::GeneratorSetup{G}) where {G <: Group}

    (; tracker, selection) = record
    (; h, o) = setup

    C = h^s * tracker * o^selection

    return C
end

struct RevealShuffle{G <: Group} <: Proposition
    setup::GeneratorSetup{G}
    tracker_challenges::Vector{BigInt}
    vote_commitments::Vector{VoteCommitment{G}} 
    tally::Vector{VoteRecord{G}} 
end

Base.length(proposition::RevealShuffle) = length(proposition.vote_commitments)

Base.permute!(proposition::RevealShuffle, ψ::Vector{Int}) = permute!(proposition.tally, ψ)

struct RevealShuffleProof{G <: Group} <: Proof
    shuffle::PoSProof{G, 1}
    s::Vector{BigInt}
    trackers::Vector{PedersenProof{G}}
end

proof_type(::Type{RevealShuffle{G}}) where {G <: Group} = RevealShuffleProof{G}

function tracker(vote_oppening::VoteOppening, chg::BigInt, setup::GeneratorSetup)

    (; d, t) = setup
    (; θ, λ) = vote_oppening

    T = d^θ * t^(λ * chg)

    return T
end

function reveal(setup::GeneratorSetup{G}, tracker_challenges::Vector{BigInt}, vote_commitments::Vector{VoteCommitment{G}}, vote_oppenings::Vector{<:VoteOppening}) where {G <: Group}
    
    (; d, t, o) = setup

    tally = VoteRecord{G}[VoteRecord(tracker(oppening, chg, setup), oppening.selection) for (chg, oppening) in zip(tracker_challenges, vote_oppenings)]

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
    (; h, d, t) = proposition.setup

    𝐫′ = rand(roprg(:𝐫′), 2:order(G)-1, length(vote_commitments))

    α = (i.α for i in vote_oppenings)
    β = (i.β for i in vote_oppenings)

    s = α .* tracker_challenges .+ β + 𝐫′
    permute!(s, 𝛙)

    C_vec = (commitment(com, chg) for (com, chg) in zip(vote_commitments, tracker_challenges))
    𝐞 = [ElGamalRow(Ci, Ci) for Ci in C_vec]

    C′_vec = (commitment(votei, si, setup) for (votei, si) in zip(tally, s))
    𝐞′ = [ElGamalRow(Ci, Ci) for Ci in C′_vec]

    shuffle_proposition = Shuffle(h, h, 𝐞, 𝐞′)

    shuffle_proof = prove(shuffle_proposition, verifier, 𝐫′, 𝛙; roprg)

    trackers = (i.tracker for i in tally)
    
    θ = (i.θ for i in @view(vote_oppenings[𝛙]))
    λ = (i.λ for i in @view(vote_oppenings[𝛙]))

    tracker_proofs = [prove(PedersenCommitment(d, t, Ti), verifier, λi * ei, θi; roprg = gen_roprg(roprg("$Ti"))) for (Ti, ei, λi, θi) in zip(trackers, @view(tracker_challenges[𝛙]), λ, θ)]

    return RevealShuffleProof(shuffle_proof, s, tracker_proofs)
end

function verify(proposition::RevealShuffle{G}, proof::RevealShuffleProof{G}, verifier::Verifier) where G <: Group

    (; setup, tally, tracker_challenges, vote_commitments) = proposition
    (; h, d, t) = proposition.setup

    C_vec = (commitment(com, chg) for (com, chg) in zip(vote_commitments, tracker_challenges))
    𝐞 = [ElGamalRow(Ci, Ci) for Ci in C_vec]

    C′_vec = (commitment(votei, si, setup) for (votei, si) in zip(tally, proof.s))
    𝐞′ = [ElGamalRow(Ci, Ci) for Ci in C′_vec]

    shuffle_proposition = Shuffle(h, h, 𝐞, 𝐞′)

    verify(shuffle_proposition, proof.shuffle, verifier) || return false

    trackers = (i.tracker for i in tally)

    for (Ti, pok) in zip(trackers, proof.trackers)

        verify(PedersenCommitment(d, t, Ti), pok, verifier) || return false

    end

    return true
end
