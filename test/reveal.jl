using Test
using TallyProofs
using CryptoGroups
using SigmaProofs
using SigmaProofs.Verificatum: generator_basis
using CryptoPRG.Verificatum: PRG
import TallyProofs: GeneratorSetup, commitment, reveal, verify, tracker, VoteCommitment, VoteOpening, TrackerOpening

G = @ECGroup{P_192}
g = G()

verifier = SigmaProofs.Verificatum.ProtocolSpec(; g)

#h, d, o = generator_basis(verifier, G, 3)
h, d = generator_basis(verifier, G, 2)

#setup = GeneratorSetup(h, d, o)
setup = GeneratorSetup(h, d)

# Now I need to make vote_openings and vote_commitments

commitments = VoteCommitment{G}[] # public
openings = VoteOpening[] # secret

function cast_vote!(selection)

    tracker_opening = TrackerOpening(2:order(G) - 1)
    vote_opening = VoteOpening(tracker_opening, selection, 2:order(G) - 1)

    vote_commitment = commitment(vote_opening, setup)

    push!(openings, vote_opening)    
    push!(commitments, vote_commitment)

    return vote_opening
end

alice = cast_vote!(2)
bob = cast_vote!(3)
eve = cast_vote!(4)

# tracker challenges are evaluated verifiably random after the vote
prg = PRG(verifier.prghash, Vector{UInt8}("SEED"))
tracker_challenges = rand(prg, 2:order(G) - 1, 3)

simulator = reveal(setup, tracker_challenges, commitments, openings, verifier)
@test verify(simulator)

# voter verifies their tracker
alice_tracker = tracker(alice, tracker_challenges[1], order(setup.g))
N = findfirst(x -> x.tracker == alice_tracker, simulator.proposition.tally)
@test simulator.proposition.tally[N].selection == 2
