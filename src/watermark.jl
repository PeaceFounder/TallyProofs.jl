module HMACWatermark

using CryptoPRG: HashSpec, bitlength
using CryptoPRG.Verificatum: PRGIterator, PRG
using CryptoGroups.Utils: bits2octet, octet2bits 

int2bits(x::Integer, nbits::Int) = BitVector((x >> i) & 1 == 1 for i in nbits:-1:0)
bits2int(::Type{T}, bits::BitVector) where T <: Integer = reduce((x, b) -> (x << 1) | b, bits, init=zero(T))

# The rejection sampling uses full bytes here
# The implemntation may need to be revised to make it more efficient for small numbers
# This should be also part of CryptoPRG
function randperm(prg::PRG, n::Int; m::Int = n)

    nbits = bitlength(n) 

    perm = Vector{Int}(undef, m)

    i = 0

    for ti in PRGIterator{Int}(prg, nbits)

        if 0 <= ti < n && !((ti + 1) in @view(perm[1:i]))
            i += 1
            perm[i] = ti + 1
        end

        if i == m
            break
        end
    end
    
    return perm
end

# We will have apply_watermark! and verify_watermark
"""
    apply_watermark!(token::BitVector, key::Integer, hasher::HashSpec; num_positions::Integer=8) -> BitVector

Embed truncated HMAC bits at positions determined by key.
Returns modified token with embedded HMAC watermark.
"""
function apply_watermark!(token::BitVector, key::Vector{UInt8}, hasher::HashSpec; num_positions::Int=2)

    prg = PRG(hasher, key)
    positions = sort(randperm(prg, length(token); m = num_positions))
    
    # Clear positions in token for HMAC computation
    for pos in positions
        token[pos] = false
    end

    bytes = bits2octet(token)
    hmac = hasher([key; bytes])
    hmac_bits = octet2bits(hmac)[1:num_positions]
    
    # Embed HMAC bits at selected positions
    for (i, pos) in enumerate(positions)
        token[pos] = hmac_bits[i]
    end
    
    return token
end

apply_watermark(token::BitVector, key::Vector{UInt8}, hasher::HashSpec; num_positions::Int=2) = apply_watermark!(copy(token), key, hasher; num_positions)

function apply_watermark(token::T, nbits::Int, key::Vector{UInt8}, hasher::HashSpec; num_positions::Int=2) where T <: Integer

    token_bits = int2bits(token, nbits)
    apply_watermark!(token_bits, key, hasher; num_positions)
    
    return bits2int(T, token_bits)
end


"""
    verify_hmac_watermark(token::BitVector, key::Integer, num_positions::Integer=8) -> Bool

Verify if token contains correct HMAC bits at key-determined positions.
"""
function verify_watermark(token::BitVector, key::Vector{UInt8}, hasher::HashSpec; num_positions::Integer=2)
    
    # Generate same deterministic bit positions
    prg = PRG(hasher, key)
    positions = sort(randperm(prg, length(token); m = num_positions))
    
    # Create base token with cleared verification bits
    result = copy(token)
    for pos in positions
        result[pos] = false
    end

    bytes = bits2octet(result)
    hmac = hasher([key; bytes])
    expected_bits = octet2bits(hmac)[1:num_positions]
    
    # Extract actual bits from token
    actual_bits = BitVector(undef, num_positions)
    for (i, pos) in enumerate(positions)
        actual_bits[i] = token[pos]
    end
    
    # Compare expected and actual bits
    return actual_bits == expected_bits
end

verify_watermark(token::Integer, nbits::Int, key::Vector{UInt8}, hasher::HashSpec; num_positions::Int=2) = verify_watermark(int2bits(token, nbits), key, hasher; num_positions)


end # module
