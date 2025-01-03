using Test
using TallyProofs
using CryptoGroups
using SigmaProofs
using SigmaProofs.Verificatum: generator_basis
using CryptoPRG.Verificatum: PRG
import TallyProofs: GeneratorSetup, vote_oppening, vote_commitment, reveal, verify, tracker, VoteCommitment, VoteOppening

G = @ECGroup{P_192}
g = G()

verifier = SigmaProofs.Verificatum.ProtocolSpec(; g)

h, d, o = generator_basis(verifier, G, 3)

setup = GeneratorSetup(h, d, o)

# Now I need to make vote_oppenings and vote_commitments

commitments = VoteCommitment{G}[] # public
oppenings = VoteOppening[] # secret

function cast_vote!(selection)

    oppening = vote_oppening(selection, 2:order(G) - 1)
    commitment = vote_commitment(oppening, setup)

    push!(oppenings, oppening)    
    push!(commitments, commitment)

    return oppening
end

alice = cast_vote!(2)
bob = cast_vote!(3)
eve = cast_vote!(4)

# tracker challenges are evaluated verifiably random after the vote
prg = PRG(verifier.prghash, Vector{UInt8}("SEED"))
tracker_challenges = rand(prg, 2:order(G) - 1, 3)

simulator = reveal(setup, tracker_challenges, commitments, oppenings, verifier)
@test verify(simulator)

# voter verifies their tracker
#alice_tracker = tracker(alice, tracker_challenges[1], setup)
alice_tracker = tracker(alice, tracker_challenges[1], order(setup.d))
N = findfirst(x -> x.tracker == alice_tracker, simulator.proposition.tally)
@test simulator.proposition.tally[N].selection == 2
