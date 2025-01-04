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

Parser.Tree(setup::GeneratorSetup{G}) where G <: Group = Tree((setup.h, setup.d, setup.o))

function Base.convert(::Type{GeneratorSetup{G}}, tree::Tree) where G <: Group
    h, d, o = convert(Tuple{G, G, G}, tree)
    return GeneratorSetup(h, d, o)
end

Parser.Tree(commitment::VoteCommitment) = Tree((commitment.Q, commitment.R, commitment.V))

function Base.convert(::Type{VoteCommitment{G}}, tree::Tree) where G <: Group
    Q, R, V = convert(Tuple{G, G, G}, tree)
    return VoteCommitment(Q, R, V)
end

#Parser.Tree(oppening::VoteOppening, L::Int) = Tree((Leaf(oppening.α, L), Leaf(oppening.θ, L), Leaf(oppening.λ, L), Leaf(oppening.β, L), Leaf(oppening.selection, L))) # Need to enforce padding here

Parser.Tree(oppening::VoteOppening, L::Int) = Tree((Leaf(oppening.α, L), Leaf(oppening.λ, L), Leaf(oppening.β, L), Leaf(oppening.θ, L), Leaf(oppening.γ, L), Leaf(oppening.selection, L)))

function Base.convert(::Type{VoteOppening}, tree::Tree)
    #α, θ, λ, β, selection = convert(Tuple{BigInt, BigInt, BigInt, BigInt, BigInt}, tree)
    α, λ, β, θ, γ, selection = convert(Tuple{BigInt, BigInt, BigInt, BigInt, BigInt, BigInt}, tree)
    return VoteOppening(α, λ, β, θ, γ, selection)
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
        return Tree((c.proposal, c.commitment, c.ux, c.pok, c.challenge))
    else
        return Tree((c.proposal, c.commitment, c.ux, c.pok, c.challenge, c.signature))
    end
end

function Base.convert(::Type{SignedVoteCommitment{G}}, tree::Tree) where G <: Group
    proposal_leaf, commitment, ux, pok, challenge_leaf, signature = convert(Tuple{Leaf, VoteCommitment{G}, G, SchnorrProof{G}, Leaf, Signature{G}}, tree)
    return SignedVoteCommitment(proposal_leaf.x, commitment, ux, pok, challenge_leaf.x, signature)
end

Parser.Tree(decoy::CoercedVote, L::Int) = Tree((Leaf(decoy.θ, L), Leaf(decoy.λ, L), Leaf(decoy.selection, L)))

function Base.convert(::Type{CoercedVote}, tree::Tree)
    θ, λ, selection = convert(Tuple{BigInt, BigInt, BigInt}, tree)
    return CoercedVote(θ, λ, selection)
end

Parser.Tree(c::CastOppening, L::Int) = Tree((Leaf(c.β, L), Tree(c.history; L), c.commitment, Tree(c.oppening, L), Tree(c.decoy, L)))
Parser.Tree(c::CastOppening{G}) where G <: Group = Tree(c, ndigits(order(G), base=256))

function Base.convert(::Type{CastOppening{G}}, tree::Tree) where G <: Group
    β, history, commitment, oppening, decoy = convert(Tuple{BigInt, Vector{BigInt}, SignedVoteCommitment{G}, VoteOppening, CoercedVote}, tree)
    return CastOppening(β, history, commitment, oppening, decoy)
end

function Parser.Tree(v::Vote{G}) where G <: Group
    if isnothing(v.signature)
        return Tree((v.proposal, v.C, v.A, v.oppening))
    else
        return Tree((v.proposal, v.C, v.A, v.oppening, v.signature))
    end
end

function Base.convert(::Type{Vote{G}}, tree::Tree) where G <: Group
    proposal_leaf, C, A, oppening, signature = convert(Tuple{Leaf, G, G, Encryption{CastOppening{G}, G}, Signature{G}}, tree)
    return Vote(proposal_leaf.x, C, A, oppening, signature)
end
