# This file contains code that will be upstreamed to ShuffleProofs and CryptoGroups
# Currently implemented here to maintain development velocity

# import Random

# # To be put in CryptoGroups
# function Random.rand!(rng::PRG, a::AbstractArray{T}, sp) where T <: Integer

#     values = rand(rng, BigInt, length(a); n = bitlength(maximum(sp))) 

#     a_flat = reshape(a, length(a))
#     a_flat .= minimum(sp) .+ mod.(values, maximum(sp) - minimum(sp) + 1) # ToDo: fix bias (a simple skipping strategy should work)

#     return a
# end


struct ShuffleSecret
    𝛙::Vector{<:Integer}
    𝐫′::Matrix{<:Integer}
end


struct Shuffle{G <: Group} <: Proposition
    g::G
    pk::G
    𝐞::Vector{<:ElGamalRow{G}} # ElGamalRow?
    𝐞′::Vector{<:ElGamalRow{G}} # ElGamalRow?

    function Shuffle{G}(g::G, pk::G, 𝐞::Vector{<:ElGamalRow{G, N}}, 𝐞′::Vector{<:ElGamalRow{G, N}}) where {G <: Group, N}
        @assert length(𝐞) == length(𝐞′)
        new(g, pk, 𝐞, 𝐞′)
    end

    Shuffle(g::G, pk::G, 𝐞::Vector{<:ElGamalRow{G}}, 𝐞′::Vector{<:ElGamalRow{G}}) where G <: Group = Shuffle{G}(g, pk, 𝐞, 𝐞′)
end

input_elgamal(shuffle::Shuffle) = shuffle.𝐞
output_elgamal(shuffle::Shuffle) = shuffle.𝐞′


function gen_roprg(ρ::AbstractVector{UInt8})

    rohash = HashSpec("sha256")
    prghash = HashSpec("sha256")
    roprg = ROPRG(ρ, rohash, prghash)

    return roprg
end

gen_roprg() = gen_roprg(rand(RandomDevice(), UInt8, 32))


function gen_shuffle(enc::Enc, e::AbstractVector{<:ElGamalRow{<:Group}}, r::Matrix{<:Integer}) 

    e_enc = enc(e, r)
    ψ = sortperm(e_enc)

    sort!(e_enc)

    (; g, pk) = enc

    proposition = Shuffle(g, pk, e, e_enc)
    secret = ShuffleSecret(ψ, r)
    
    return proposition, secret
end


function shuffle(𝐞::AbstractVector{<:ElGamalRow{G, N}}, g::G, pk::G; roprg = gen_roprg()) where {N, G <: Group}

    𝐫′ = rand(roprg(:𝐫′), 2:order(g) - 1, (N, length(𝐞))) 
    enc = Enc(pk, g)
    
    return gen_shuffle(enc, 𝐞, 𝐫′)[1] # I may also refactor it as shuffle. 
end



