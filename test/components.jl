using Test
import TallyProofs: shuffle, retrack_shuffle, decrypt, Enc, output_elgamal, input_trackers, output_trackers, braid
using CryptoGroups
import CryptoGroups: PGroup, ECGroup

# g = @ECGroup{P_192}()
_curve = curve("P_192")
G = specialize(ECGroup, _curve)
g = G(generator(_curve))

x = 232
pk = g^x
enc = Enc(pk, g)

y = [2, 3, 4] 
Y = g .^ y

messages = [
    (g, g^2),
    (g^2, g^3),
    (g^3, g^4)
]

messages_enc = enc(messages, [2, 3, 7])

# Testing ordinary shuffle with multiple elements

_shuffle = shuffle(messages_enc, g, pk)
decryption = decrypt(output_elgamal(_shuffle), g, x) # g, pk, cyphertexts, plaintexts
@test sort(messages) == sort(decryption.plaintexts)

# Testing retrack shuffle

rtshuffle = retrack_shuffle(Y, messages, g, x)

@test input_trackers(rtshuffle) == Y
@test output_trackers(rtshuffle) |> sort == sort(pk .^ y)

decryption = decrypt(output_elgamal(rtshuffle), g, x) # g, pk, cyphertexts, plaintexts

@test sort(messages) == sort(decryption.plaintexts)

# Testing the braid

_braid = braid(Y, g, x)

@test sort(output_trackers(_braid)) == sort(pk .^ y)
