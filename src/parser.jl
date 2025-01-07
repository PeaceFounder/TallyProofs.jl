import SigmaProofs.Parser # Tree
using SigmaProofs.Parser: Tree, Leaf

Parser.Tree(encryption::Encryption) = Tree((encryption.encapsulation, Leaf(encryption.ciphertext)))

function Base.convert(::Type{Encryption{T, G}}, tree::Tree) where {T, G <: Group}
    encapsulation, ciphertext_leaf = convert(Tuple{G, Leaf}, tree)
    return Encryption{T, G}(encapsulation, ciphertext_leaf.x)
end


Parser.Tree(proof::SchnorrProof{G}) where G <: Group = Tree((proof.R, Leaf(proof.s, ndigits(order(G), base=256))))

function Base.convert(::Type{SchnorrProof{G}}, tree::Tree) where G <: Group
    R, s = convert(Tuple{G, BigInt}, tree)
    return SchnorrProof(R, s)
end

Parser.Tree(setup::GeneratorSetup{G}) where G <: Group = Tree((setup.h, setup.g))

function Base.convert(::Type{GeneratorSetup{G}}, tree::Tree) where G <: Group
    h, g = convert(Tuple{G, G}, tree)
    return GeneratorSetup(h, g)
end

Parser.Tree(commitment::VoteCommitment) = Tree((commitment.Q, commitment.R, commitment.V))

function Base.convert(::Type{VoteCommitment{G}}, tree::Tree) where G <: Group
    Q, R, V = convert(Tuple{G, G, G}, tree)
    return VoteCommitment(Q, R, V)
end

Parser.Tree(opening::TrackerOpening, L::Int) = Tree((Leaf(opening.α, L), Leaf(opening.λ, L), Leaf(opening.β, L), Leaf(opening.θ, L)))

function Base.convert(::Type{TrackerOpening}, tree::Tree)
    α, λ, β, θ = convert(Tuple{BigInt, BigInt, BigInt, BigInt}, tree)
    return TrackerOpening(α, λ, β, θ)
end

Parser.Tree(opening::VoteOpening, L::Int) = Tree((Tree(opening.tracker, L), Leaf(opening.selection, L), Leaf(opening.γ, L)))

function Base.convert(::Type{VoteOpening}, tree::Tree)
    tracker, selection, γ = convert(Tuple{TrackerOpening, BigInt, BigInt}, tree)
    return VoteOpening(tracker, selection, γ)
end

Parser.Tree(signature::Signature) = Tree((signature.pbkey, signature.proof))

function Base.convert(::Type{Signature{G}}, tree::Tree) where G <: Group
    pbkey, proof = convert(Tuple{G, SchnorrProof{G}}, tree)
    return Signature(pbkey, proof)
end

Parser.Tree(proposal::Proposal) = Tree((proposal.spec, proposal.g, proposal.collector, proposal.basis, proposal.watermark_nbits, proposal.token_max, string(nameof(typeof(proposal.encrypt_spec))), proposal.hasher.spec))


function Base.convert(::Type{Proposal{G}}, tree::Tree) where G <: Group
    spec_leaf, g, collector, basis, watermark_nbits, token_max, encrypt_spec, hash_spec = convert(Tuple{Leaf, G, G, GeneratorSetup{G}, Int, Int, String, String}, tree)

     return Proposal(spec_leaf.x, g, collector, basis, watermark_nbits, token_max, EncryptSpec(Symbol(encrypt_spec)), HashSpec(hash_spec))
end

function Parser.Tree(c::SignedVoteCommitment)
    if isnothing(c.signature)
        return Tree((c.proposal, c.ux, c.commitment, c.I, c.pok))
    else
        return Tree((c.proposal, c.ux, c.commitment, c.I, c.pok, c.signature))
    end
end

function Base.convert(::Type{SignedVoteCommitment{G}}, tree::Tree) where G <: Group
    proposal_leaf, ux, commitment, I_leaf, pok, signature = convert(Tuple{Leaf, G, VoteCommitment{G}, Leaf, SchnorrProof{G}, Signature{G}}, tree)
    return SignedVoteCommitment(proposal_leaf.x, ux, commitment, I_leaf.x, pok, signature)
end

Parser.Tree(decoy::DecoyOpening, L::Int) = Tree((Leaf(decoy.θ, L), Leaf(decoy.λ, L), Leaf(decoy.selection, L)))

function Base.convert(::Type{DecoyOpening}, tree::Tree)
    θ, λ, selection = convert(Tuple{BigInt, BigInt, BigInt}, tree)
    return DecoyOpening(θ, λ, selection)
end

Parser.Tree(c::CastOpening, L::Int) = Tree((Leaf(c.β, L), Tree(c.history; L), c.commitment, Tree(c.opening, L), Tree(c.decoy, L), c.π_t))
Parser.Tree(c::CastOpening{G}) where G <: Group = Tree(c, ndigits(order(G), base=256))

function Base.convert(::Type{CastOpening{G}}, tree::Tree) where G <: Group
    β, history, commitment, opening, decoy, π_t = convert(Tuple{BigInt, Vector{BigInt}, SignedVoteCommitment{G}, VoteOpening, DecoyOpening, SchnorrProof{G}}, tree)
    return CastOpening(β, history, commitment, opening, decoy, π_t)
end

function Parser.Tree(v::Vote{G}) where G <: Group
    if isnothing(v.signature)
        return Tree((v.proposal, v.C, v.opening))
    else
        return Tree((v.proposal, v.C, v.opening, v.signature))
    end
end

function Base.convert(::Type{Vote{G}}, tree::Tree) where G <: Group
    proposal_leaf, C, opening, signature = convert(Tuple{Leaf, G, Encryption{CastOpening{G}, G}, Signature{G}}, tree)
    return Vote(proposal_leaf.x, C, opening, signature)
end
