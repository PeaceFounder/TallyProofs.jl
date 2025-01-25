using CryptoGroups: Group, order, octet
using CryptoGroups.Utils: int2octet, int2octet!, octet2int
using CryptoPRG: HashSpec
using CryptoPRG.Verificatum: PRG
using SigmaProofs.LogProofs: SchnorrProof, LogKnowledge
using SigmaProofs.Parser: Tree, encode
using SigmaProofs.Verificatum: generator_basis, GeneratorBasis
using SigmaProofs: prove, verify

import .HMACWatermark: verify_watermark

struct Signature{G <: Group}
    pbkey::G
    proof::SchnorrProof{G}
end

function sign(message::Vector{UInt8}, g::G, key::BigInt; r = nothing) where G <: Group
    # This is temporary
    # we should however try to implement Scnorr signatures here according to specification
    verifier = ProtocolSpec(; g)
    
    pbkey = g^key
    
    if isnothing(r)
        proof = prove(LogKnowledge(g, pbkey), verifier, key; suffix = message)
    else
        proof = prove(LogKnowledge(g, pbkey), verifier, key; suffix = message, r)
    end

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

struct DecoyOpening
    θ::BigInt # Could be reused to mark revotes
    λ::BigInt
    selection::BigInt
end

DecoyOpening() = DecoyOpening(0, 0, 0)

function DecoyOpening(selection::Integer, range::UnitRange; roprg = gen_roprg())

    θ = rand(roprg(:θ), range)
    λ = rand(roprg(:λ), range)

    return DecoyOpening(θ, λ, selection)
end

Base.zero(::Type{DecoyOpening}) = DecoyOpening(0, 0, 0)
Base.zero(::DecoyOpening) = zero(DecoyOpening)

function VoteOpening(vote::DecoyOpening, range::UnitRange; roprg = gen_roprg())

    (; θ, λ, selection) = vote
    α = rand(roprg(:α), range)
    β = rand(roprg(:β), range)
    γ = 0

    tracker = TrackerOpening(α, λ, β, θ)
    return VoteOpening(tracker, selection, γ)
end

Base.:(==)(x::DecoyOpening, y::DecoyOpening) = x.θ == y.θ && x.λ == y.λ && x.selection == y.selection

struct Proposal{G <: Group} 
    pid::Int # A simple reference
    spec::Vector{UInt8} # hash of other set of parameters
    g::G
    collector::G
    basis::GeneratorSetup{G} # new
    watermark_nbits::Int
    token_max::Int # 
    encrypt_spec::EncryptSpec
    hasher::HashSpec
end

function Proposal(pid::Integer, g::G, collector::G, verifier::Verifier; spec = UInt8[], watermark_nbits::Int=4, token_max::Int=9999_9999, encrypt_spec::EncryptSpec=AES256_SHA256(), hasher = verifier.prghash) where G <: Group
    
    # For safety reasons we shall derive both generators independently and not reuse g
    h, d = generator_basis(verifier, G, 2)
    basis = GeneratorSetup(h, d)
    
    return Proposal(pid, spec, g, collector, basis, watermark_nbits, token_max, encrypt_spec, hasher)
end

Base.:(==)(x::T, y::T) where T <: Proposal = x.pid == y.pid && x.spec == y.spec && x.g == y.g && x.collector == y.collector && x.basis == y.basis && x.watermark_nbits == y.watermark_nbits && x.token_max == y.token_max && x.encrypt_spec == y.encrypt_spec && x.hasher == y.hasher

function compute_decoy_tracker_seed(proposal::Proposal{G}, seed::Vector{UInt8}) where G <: Group

    prg = PRG(proposal.hasher, [seed; encode(Tree(proposal))])
    z = rand(prg, 2:order(G) - 1)

    return z
end

function compute_tracker_preimage(decoy_seed::G, hasher::HashSpec) where G <: Group
    
    θ, λ = rand(PRG(hasher, octet(decoy_seed)), 2:order(G) - 1, 2)

    return θ, λ
end

function compute_tracker_preimage(proposal::Proposal{G}, seed::Vector{UInt8}) where G <: Group
    
    z = compute_decoy_tracker_seed(proposal, seed)
    decoy_seed = proposal.collector ^ z

    return compute_tracker_preimage(decoy_seed, proposal.hasher)
end

function compute_tracker(proposal::Proposal, seed::Vector{UInt8}, token::Integer)

    θ, λ = compute_tracker_preimage(proposal, seed)

    T = tracker(θ, λ, token, order(proposal.g))

    return proposal.hasher(int2octet(T))[1:8] |> octet2int
end

function verify_watermark(proposal::Proposal{G}, ux::G, token::Integer, hasher::HashSpec) where G <: Group
    
    (; token_max, watermark_nbits) = proposal

    nbits = ndigits(token_max, base=2) - 1
    offset = token_max - 2^nbits
    return verify_watermark(token - offset, nbits, octet(ux), hasher; num_positions = watermark_nbits)    
end

function DecoyOpening(hasher::HashSpec, selection::Integer, decoy_seed::G) where G <: Group
    θ, λ = compute_tracker_preimage(decoy_seed, hasher)
    return DecoyOpening(θ, λ, selection)
end

struct CastRecord{G <: Group}
    proposal::Vector{UInt8} # hash
    ux::G
    commitment::VoteCommitment{G} # This one is derivable
    I::Vector{UInt8}
    pok::SchnorrProof{G}
    signature::Signature{G}
end

function CastRecord(proposal::Vector{UInt8}, ux::G, commitment::VoteCommitment{G}, I::Vector{UInt8}, pok::SchnorrProof, signer::Signer{G}; r = nothing) where G <: Group

    msg = (proposal, ux, commitment)
    internal_signature = sign(encode(Tree(msg)), signer.g, signer.key; r)

    return CastRecord(proposal, ux, commitment, I, pok, internal_signature)
end

function verify(vote::CastRecord{G}, g::G) where G <: Group

    (; proposal, commitment, ux) = vote
    msg = (proposal, ux, commitment)
    
    return verify(encode(Tree(msg)), g, vote.signature)
end

function isconsistent(row::CastRecord{G}, g::G, hasher::HashSpec, verifier::Verifier) where G <: Group
    
    verify(row, g) || return false
    (; ux, pok) = row
    
    u = sup_generator(row, hasher)

    verify(LogKnowledge(u, ux), pok, verifier) || return false

    return true
end

# Can be further encrypted in a threshold decryption ceremony if one wishes to have that for fairness
struct CastOpening{G <: Group}
    β::BigInt # For supersession
    history::Vector{BigInt}
    record::CastRecord{G}
    opening::VoteOpening # opening -> vote
    decoy::DecoyOpening
end

# verifiable_seed
function seed(π::SchnorrProof{G}) where G <: Group
    
    buffer = zeros(UInt8, ndigits(order(G), base=256))
    int2octet!(buffer, π.s)

    return buffer
end

function isconsistent(cast::CastOpening{G}, proposal::Proposal{G}, verifier::Verifier) where G <: Group
    
    commitment(cast.opening, proposal.basis) == cast.record.commitment || return false
    
    return isconsistent(cast.record, proposal.g, proposal.hasher, verifier) 
end

function isconsistent(a::T, b::T) where T <: CastOpening

    a.record.signature.pbkey == b.record.signature.pbkey || return false
    a.record.commitment.Q == b.record.commitment.Q || return false
    a.record.commitment.R == b.record.commitment.R || return false
    a.record.I == b.record.I || return false

    n = min(length(trim(a.history)), length(trim(b.history)))
    @view(a.history[1:n]) == @view(b.history[1:n]) || return false

    return true
end

function isbinding(C::G, opening::CastOpening, h::G) where G <: Group

    (; β) = opening
    (; ux) = opening.record
    
    return C == h^β * ux
end

function sup_generator(pseudonym::G, I::Vector{UInt8}, hasher::HashSpec) where G <: Group

    prg = PRG(hasher, [octet(pseudonym); I])
    u = GeneratorBasis.generator_basis(prg, G) 

    return u
end

function sup_generator(commitment::CastRecord, hasher::HashSpec)

    (; pbkey) = commitment.signature
    (; I) = commitment

    return sup_generator(pbkey, I, hasher)    
end

sup_generator(cast::CastOpening, hasher::HashSpec) = sup_generator(cast.record, hasher)
