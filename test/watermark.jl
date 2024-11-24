using Test 
import TallyProofs.HMACWatermark: apply_watermark, verify_watermark, int2bits, bits2int
using CryptoPRG: HashSpec

token = BitVector([0, 1, 0, 1, 1, 0])
key = UInt8[1, 2, 4, 6, 7]

hasher = HashSpec("sha256")

num_positions = 2 # This equals to a probability P = 1/2^2 * 1/C(6, 2)

result = apply_watermark(copy(token), key, hasher; num_positions)
@test verify_watermark(result, key, hasher; num_positions)

result[5] = !result[5]
@test !verify_watermark(result, key, hasher; num_positions)

nbits = 17
token = 1451

@test token == bits2int(Int, int2bits(token, 20))

token = 2455
nbits = ndigits(9999, base=2) - 1

watermarked_token = apply_watermark(token, nbits, key, hasher; num_positions)
@test verify_watermark(watermarked_token, nbits, key, hasher; num_positions)
@test !verify_watermark(token, nbits, key, hasher; num_positions)


# example on how to generate token a max range
N = 99
nbits = ndigits(N, base=2) - 1
offset = N - 2^nbits

for i in 1:1000
    token_seed = rand(0:2^nbits - 1)
    ti = apply_watermark(token_seed, nbits, key, hasher; num_positions) + offset
    @test verify_watermark(ti - offset, nbits, key, hasher; num_positions)
end
