import SigmaProofs.Parser # Tree
using SigmaProofs.Parser: Tree, Leaf

Parser.Tree(proof::SchnorrProof{G}) where G <: Group = Tree((proof.R, Leaf(proof.s, ndigits(order(G), base=256))))

function Base.convert(::Type{SchnorrProof{G}}, tree::Tree) where G <: Group
    R, s = convert(Tuple{G, BigInt}, tree)
    return SchnorrProof(R, s)
end

Parser.Tree(setup::GeneratorSetup{G}) where G <: Group = Tree((setup.h, setup.d, setup.t, setup.o))

function Base.convert(::Type{GeneratorSetup{G}}, tree::Tree) where G <: Group
    h, d, t, o = covert(Tuple{G, G, G, G}, tree)
    return GeneratorSetup(h, d, t, o)
end

Parser.Tree(commitment::VoteCommitment) = Tree((commitment.Q, commitment.C))

function Base.convert(::Type{VoteCommitment{G}}, tree::Tree) where G <: Group
    Q, C = convert(Tuple{G, G}, tree)
    return VoteCommitment(Q, C)
end

Parser.Tree(oppening::VoteOppening, L::Int) = Tree((Leaf(oppening.α, L), Leaf(oppening.θ, L), Leaf(oppening.λ, L), Leaf(oppening.β, L), Leaf(oppening.selection, L))) # Need to enforce padding here

function Base.convert(::Type{VoteOppening}, tree::Tree)
    α, θ, λ, β, selection = convert(Tuple{BigInt, BigInt, BigInt, BigInt, BigInt}, tree)
    return VoteOppening(α, θ, λ, β, selection)
end

Parser.Tree(signature::Signature) = Tree((signature.pbkey, signature.proof))

function Base.convert(::Type{Signature{G}}, tree::Tree) where G <: Group
    pbkey, proof = convert(Tuple{G, SchnorrProof{G}}, tree)
    return Signature(pbkey, proof)
end

Parser.Tree(proposal::Proposal) = Tree((proposal.spec, proposal.g, proposal.collector, proposal.basis, proposal.watermark_nbits, proposal.token_max))

# ToDo
# function Base.convert(::Type{Proposal{G}}, tree::Tree) where G <: Group
#     generator, collector, watermark_nbits, range_start, range_stop = convert(Tuple{G, G, Int, BigInt, BigInt}, tree)
#     return Proposal(generator, collector, watermark_nbits, range_start:range_stop)
# end

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

Parser.Tree(c::CastOppening, L::Int) = Tree((Leaf(c.β, L), Tree(c.history; L), c.commitment, Tree(c.oppening, L)))

function Base.convert(::Type{CastOppening{G}}, tree::Tree) where G <: Group
    β, history, commitment, oppening = convert(Tuple{BigInt, Vector{BigInt}, SignedVoteCommitment{G}, VoteOppening}, tree)
    return CastOppening(β, history, commitment, oppening)
end

function Parser.Tree(v::Vote{G}) where G <: Group
    if isnothing(v.signature)
        return Tree((v.proposal, v.C, v.A, Tree(v.oppening, ndigits(order(G), base=256))))
    else
        Tree((v.proposal, v.C, v.A, Tree(v.oppening, ndigits(order(G), base=256)), v.signature))
    end
end

function Base.convert(::Type{Vote{G}}, tree::Tree) where G <: Group
    proposal_leaf, C, A, oppening, signature = convert(Tuple{Leaf, G, G, CastOppening{G}, Signature{G}}, tree)
    return Vote(proposal_leaf.x, C, A, oppening, signature)
end
