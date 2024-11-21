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

function verify(proposition::PedersenCommitment, proof::PedersenProof, verifier::Verifier)

    (; h, g, C) = proposition
    (; A, s, p) = proof

    c = challenge(verifier, proposition, A)

    return A * C^c == h^s * g^p
end
