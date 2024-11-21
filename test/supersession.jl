using Test
using TallyProofs
using CryptoGroups
using SigmaProofs
using SigmaProofs.Verificatum: generator_basis
import TallyProofs: ReCommit, SupersessionCalculator, check_challenge, supersess, verify


G = @ECGroup{P_192}
g = G()

verifier = SigmaProofs.Verificatum.ProtocolSpec(; g)
prghash = verifier.prghash

# Our BuletinBoard implementation

C_vec = G[]
A_vec = G[]

recommits = ReCommit{G}[]


function recommit!(calc, chg)

    C, A, oppening = TallyProofs.recommit!(calc, chg)
    @test check_challenge(C, A, calc.u, chg, prghash)

    push!(C_vec, C)
    push!(A_vec, A)
    push!(recommits, oppening)

    return length(C_vec) # The cast index
end

h_vec = generator_basis(verifier, G, 4)
h = h_vec[1]
u₁, u₂, u₃ = h_vec[2:end] # The generators are generated verifiably random with each individual seed

alice = SupersessionCalculator(h, u₁, verifier)
bob = SupersessionCalculator(h, u₂, verifier)
eve = SupersessionCalculator(h, u₃, verifier)

recommit!(alice, 123)
recommit!(alice, 2345)
recommit!(bob, 241)
recommit!(eve, 451)
recommit!(alice, 4452)
recommit!(bob, 4551)

alice_first = recommits[1]
alice_last = recommits[5]

@test alice_first.ux == alice_last.ux ^ prod(alice_last.history)

simulator = supersess(C_vec, h, recommits, verifier)
@test verify(simulator)
