using CryptoGroups: Group, order, octet
using CryptoGroups.Fields: FP
using CryptoGroups.Utils: static, int2octet
using SigmaProofs: Proposition, Proof, Verifier, Simulator
using SigmaProofs.Verificatum: ProtocolSpec, ro_prefix
using SigmaProofs.LogProofs: SchnorrProof, LogKnowledge
using SigmaProofs.Parser: Tree, encode
using CryptoPRG: HashSpec
using CryptoPRG.Verificatum: PRG
import SigmaProofs: prove, verify, proof_type

struct ReCommit{G <: Group}
    β::BigInt
    u::G
    ux::G
    history::Vector{BigInt} # Note that there could be repetition and etc
    pok::SchnorrProof{G}
end

mutable struct SupersessionCalculator{G <: Group}
    const h::G # blinding generator
    const u::G
    history::Vector{BigInt} # qs, this needs to be carried over
    x::BigInt # The current value
    ux::G # also the current value
    verifier::Verifier
    prghash::HashSpec

    function SupersessionCalculator(h::G, u::G, verifier::Verifier, prghash::HashSpec; roprg = gen_roprg()) where G <: Group
        x = rand(roprg(:x), 2:order(G)-1)
        new{G}(h, u, BigInt[], x, u^x, verifier, prghash)
    end
end

SupersessionCalculator(h::G, u::G, verifier::ProtocolSpec) where G <: Group = SupersessionCalculator(h, u, verifier, verifier.prghash)

function compute_p(A::G, chg::Integer, spec::HashSpec) where G <: Group

    prg = PRG(spec, UInt8[octet(A); int2octet(chg)]) # the bitlenght can be enforced
    p = rand(prg, 2:order(G) - 1)

    return p
end

function check_challenge(C::G, A::G, u::G, chg::Integer, spec::HashSpec) where G <: Group

    p = compute_p(A, chg, spec)
    
    return C/A == u^p
end

exponent_field(::Type{G}) where G <: Group = FP{static(order(G))}


function recommit!(calc::SupersessionCalculator{G}, chg::Integer; roprg = gen_roprg()) where G <: Group

    (; u, h, x, prghash, verifier) = calc

    β = rand(roprg(:β), 2:order(G)-1)
    A = h^β * u^x
    
    p = compute_p(A, chg, prghash) 
    
    x′ = x + p % order(G)
    q = x * invmod(x′, order(G)) % order(G)
    
    ux = u^x′
    C = h^β * ux
    
    pok = prove(LogKnowledge(u, ux), verifier, x′)
    
    push!(calc.history, q)
    calc.x = x′
    calc.ux = ux
    
    # Return the history without the first element
    recommit = ReCommit(β, u, ux, calc.history[2:end], pok)
    
    return C, A, recommit
end

struct Supersession{G <: Group} <: Proposition
    C::Vector{G}
    h::G # blinding generator 
    u::Vector{G}
    ux::Vector{G} # superseeded session identifiers
    pok::Vector{SchnorrProof{G}}
end

function Base.permute!(proposition::Supersession, ψ::Vector{Int})

    permute!(proposition.u, ψ)
    permute!(proposition.ux, ψ)
    permute!(proposition.pok, ψ)

    return
end

struct SupersessionProof{G <: Group} <: Proof
    A::G 
    s::BigInt
    𝐭::Vector{BigInt}
end

proof_type(::Type{Supersession{G}}) where G <: Group = SupersessionProof{G}

function challenge(verifier::ProtocolSpec{G}, proposition::Supersession{G}, A::G) where G <: Group

    (; h, ux, C) = proposition
    
    ρ = ro_prefix(verifier)

    tree = Tree((h, ux, C, A))

    prg = PRG(verifier.prghash, [ρ..., encode(tree)...])

    return rand(prg, 2:order(G) - 1, length(C))
end

function prove(proposition::Supersession{G}, verifier::Verifier, ψ::Vector{<:Integer}, β::Vector{<:Integer}, α::Vector{<:Integer}; roprg = gen_roprg()) where G <: Group

    (; ux, h, C) = proposition

    z = rand(roprg(:z), 2:order(G)-1)
    𝐫 = rand(roprg(:𝐫), 2:order(G)-1, length(ux))

    A = h^z * prod(ux .^ 𝐫)

    𝐞 = challenge(verifier, proposition, A)

    s = z + sum(𝐞 .* β) % order(G)
    
    𝐭 = 𝐫 # 𝐫 is not used anymore and hence we can use already it's allocation

    for (i, (ei, αi)) in enumerate(zip(𝐞, α))
        
        𝐭[ψ[i]] += ei * αi

    end
    
    𝐭 .= mod.(𝐭, order(G))
    
    return SupersessionProof(A, s, 𝐭)
end

function verify(proposition::Supersession{G}, proof::SupersessionProof{G}, verifier::Verifier) where G <: Group

    (; u, ux, pok, h, C) = proposition
    (; A, s, 𝐭) = proof

    for (ui, uxi, poki) in zip(u, ux, pok)

        verify(LogKnowledge(ui, uxi), poki, verifier) || return false

    end
    
    𝐞 = challenge(verifier, proposition, A)

    return A * prod(C .^ 𝐞) == h^s * prod(ux .^ 𝐭)
end


function extract_maximum_mask(identifiers::Vector{<:Any}, values::Vector{Int})
    n = length(identifiers)
    
    # Get sorted permutation based on identifiers (ascending) and values (descending)
    perm = sortperm(1:n; by=i -> (identifiers[i], -values[i]))
    
    mask = falses(n)
    
    # Take first occurrence of each identifier
    i = 1
    while i <= n
        current_id = identifiers[perm[i]]
        mask[perm[i]] = true
        
        # Skip all other occurrences of the same identifier
        while i < n && identifiers[perm[i+1]] == current_id
            i += 1
        end
        i += 1
    end
    
    return mask
end

function extract_supersession(recommits::Vector{ReCommit{G}}) where G <: Group

    u_vec = [r.u for r in recommits]
    width_vec = [length(r.history) for r in recommits]
    
    return extract_maximum_mask(u_vec, width_vec)
end

function reduce_representation(recommits::Vector{ReCommit{G}}, u_vec::Vector{G}, ux_vec::Vector{G}, history::Vector{Vector{BigInt}}) where G <: Group
    ψ_vec = Vector{Int}(undef, length(recommits))
    α_vec = Vector{BigInt}(undef, length(recommits))

    for (n, r) in enumerate(recommits)

        ψi = findfirst(isequal(r.u), u_vec)
        
        if r.ux == ux_vec[ψi]
            α::BigInt = 1
        else
            m = length(r.history)
            α = mod(prod(history[ψi][m+1:end]), order(G)) # 
        end

        ψ_vec[n] = ψi
        α_vec[n] = α

        #@show r.ux == ux_vec[ψi] ^ α
    end

    return ψ_vec, α_vec
end

# The function supersess performs the critical operation of identifying and filtering superseded elements within a collection, 
# analogous to how cryptographic voting systems process multiple votes from the same voter. Just as "shuffle" describes the 
# action of permuting elements and "decrypt" denotes the process of revealing encrypted content, "supersess" encapsulates 
# the specific action of examining a set of elements with temporal ordering and identifying which elements have been 
# replaced by newer ones. This operation is distinct from the relationship described by "supersede" - while one vote may supersede
# another, the systematic process of identifying and handling all such relationships within a collection is what we term
# "supersessing", filling a lexical gap in the technical vocabulary of cryptographic voting systems.
function supersess(C::Vector{G}, h::G, recommits::Vector{ReCommit{G}}; mask = extract_supersession(recommits)) where G <: Group

    u = [r.u for r in @view(recommits[mask])]
    ux = [r.ux for r in @view(recommits[mask])]
    pok = [r.pok for r in @view(recommits[mask])]

    return Supersession(C, h, u, ux, pok)
end

function supersess(C::Vector{G}, h::G, recommits::Vector{ReCommit{G}}, verifier::Verifier) where G <: Group

    mask = extract_supersession(recommits)
    proposition = supersess(C, h, recommits; mask)

    perm = sortperm(proposition.u)
    permute!(proposition, perm)

    history = [r.history for r in @view(recommits[mask])]
    permute!(history, perm)

    ψ, α = reduce_representation(recommits, proposition.u, proposition.ux, history)

    β = [r.β for r in recommits]
    proof = prove(proposition, verifier, ψ, β, α)

    return Simulator(proposition, proof, verifier)
end
