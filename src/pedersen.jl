using CryptoGroups: Group, order, octet
using SigmaProofs: Proposition, Proof, Verifier, Simulator
using SigmaProofs.Verificatum: ProtocolSpec, ro_prefix
using SigmaProofs.Parser: Tree, encode
import SigmaProofs: prove, verify, proof_type

struct PedersenCommitment{G <: Group} <: Proposition
    h::G
    g::G
    C::G
end

struct PedersenProof{G <: Group} <: Proof
    A::G
    s::BigInt
    p::BigInt
end

proof_type(::Type{PedersenCommitment{G}}) where G <: Group = PedersenProof{G}

function commit(g::G, h::G, m::Integer, r::Integer) where G <: Group
    
    C = h^r * g^m

    return PedersenCommitment(h, g, C)
end

function commit(g::G, h::G, m::Integer, r::Integer, verifier::Verifier; roprg = gen_roprg()) where G <: Group

    proposition = commit(g, h, m, r)
    proof = prove(proposition, verifier, m, r; roprg)

    return Simulator(proposition, proof, verifier)
end

function challenge(verifier::ProtocolSpec{G}, proposition::PedersenCommitment{G}, A::G) where G <: Group
    
    (; h, g, C) = proposition

    ρ = ro_prefix(verifier)

    tree = Tree((h, g, C, A))

    prg = PRG(verifier.prghash, [ρ..., encode(tree)...])

    return rand(prg, 2:order(G) - 1)
end

function prove(proposition::PedersenCommitment{G}, verifier::Verifier, m::Integer, r::Integer; roprg = gen_roprg()) where G <: Group

    (; h, g, C) = proposition

    w = rand(roprg(:w), 2:order(G)-1)
    z = rand(roprg(:z), 2:order(G)-1)

    A = h^w * g^z

    c = challenge(verifier, proposition, A)

    s = w + c * r
    p = z + c * m

    return PedersenProof(A, s, p)
end

function verify(proposition::PedersenCommitment{G}, proof::PedersenProof{G}, verifier::Verifier) where G <: Group

    (; h, g, C) = proposition
    (; A, s, p) = proof

    c = challenge(verifier, proposition, A)

    return A * C^c == h^s * g^p
end

struct LambdaCommitment{G<:Group} <: Proposition
    h::G
    d::G
    Q::G
end

#LambdaCommitment(h::G, d::G, λ::BigInt) = 

struct LambdaProof{G<:Group} <: Proof
    A::G
    w::BigInt
    z::BigInt
end

proof_type(::Type{LambdaCommitment{G}}) where G <: Group = LambdaProof{G}

function lambda_commit(h::G, d::G, λ::Integer, α::Integer) where G <: Group
    Q = h^α * d^λ
    return LambdaCommitment(Q, h, d)
end

function lambda_commit(h::G, d::G, λ::Integer, α::Integer, verifier::Verifier; roprg = gen_roprg()) where G <: Group

    proposition = lambda_commit(h, d, λ, α)
    proof = prove(proposition, verifier, λ, α; roprg)

    return Simulator(proposition, proof, verifier)
end

function challenge(verifier::ProtocolSpec{G}, proposition::LambdaCommitment{G}, A::G) where G <: Group
    
    (; h, d, Q) = proposition

    ρ = ro_prefix(verifier)

    tree = Tree((h, d, Q, A))

    prg = PRG(verifier.prghash, [ρ..., encode(tree)...])

    return rand(prg, 2:order(G) - 1, 2)
end

function prove(proposition::LambdaCommitment{G}, verifier::Verifier, λ::Integer, α::Integer; roprg = gen_roprg()) where G <: Group

    (; Q, h, d) = proposition

    μ = rand(roprg(:μ), 2:order(G)-1)
    ν = rand(roprg(:ν), 2:order(G)-1)

    A = h^μ * d^ν

    e₁, e₂ = challenge(verifier, proposition, A)

    invλ = invmod(λ, order(G))
    w = mod(e₁ - μ - α * (e₂ - ν) * invλ, order(G))
    z = mod((e₂ - ν) * invλ, order(G))

    return LambdaProof(A, w, z)
    #@show verify(proposition, proof, verifier)
    #return proof
end

function verify(proposition::LambdaCommitment{G}, proof::LambdaProof{G}, verifier::Verifier) where G <: Group

    (; Q, h, d) = proposition
    (; A, w, z) = proof

    e₁, e₂ = challenge(verifier, proposition, A)

    return h^e₁ * d^e₂ / A == h^w * Q^z
end
