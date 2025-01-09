using Test
using CryptoGroups
using SigmaProofs.Verificatum: ProtocolSpec
using TallyProofs

G = @ECGroup{P_192}
g = G()

verifier = ProtocolSpec(; g)

# Tallier Secrets
tallier_key = 453
cast_openings = CastOpening{G}[]

# Public Buletin Board
proposal = Proposal(g, g^tallier_key, verifier; token_max=999)
members = G[]
cast_commitments = G[]

# Tallier Controller
function record_vote!(vote)

    alias = findfirst(isequal(vote.signature.pbkey), members)
    @test !isnothing(alias) #"Voter is not a registered member"

    cast_opening = decrypt(vote.opening, tallier_key, proposal.encrypt_spec)
    @test isbinding(vote.C, cast_opening, proposal.basis.h)
    @test isconsistent(cast_opening, proposal, verifier)

    @test isconsistent(cast_openings, cast_opening)

    push!(cast_commitments, vote.C)
    push!(cast_openings, cast_opening)

    cast_index = length(cast_commitments)
    
    return alias, cast_index
end

# Voting Device Controller
function cast_vote!(voter, selection, pin)

    chg = rand(2:order(G)-1)
    context = assemble_vote!(voter, selection, chg, pin; inherit_challenge=false)
    @test isconsistent(context, chg, g, voter.hasher, voter.verifier)
    alias, cast_index = record_vote!(context.vote)
    # cast_index is kept by the voting device for locting cast commitment on the buletin board
    
    return CastReceipt(alias, context.id, seed(context.π_w))
end

# Registration
alice = VotingCalculator(b"Alice", proposal, verifier, 1234) 
bob = VotingCalculator(b"Bob", proposal, verifier, 5678)
eve = VotingCalculator(b"Eve", proposal, verifier, 4321)

append!(members, [alice.pseudonym, bob.pseudonym, eve.pseudonym]) # registration

# Vote Casting
alice_receipt = cast_vote!(alice, 3, alice.pin)
bob_receipt = cast_vote!(bob, 4, bob.pin)
eve_receipt = cast_vote!(eve, 6, eve.pin)
bob_receipt = cast_vote!(bob, 0, bob.pin) # anyone can revote

# Universal Verifiability
simulator = tally(proposal, cast_commitments, cast_openings, verifier)
@test verify(simulator)

# Individual Verifiability
@test alice_receipt.id == b"Alice" 
alice_token = get_token(simulator.proposition, members, alice_receipt, proposal.hasher)
alice_tracker = compute_tracker(alice, alice_token, alice.pin) # this is a hash of the tracker
N = findfirst(x -> x.tracker == alice_tracker, simulator.proposition.tally)
@test simulator.proposition.tally[N].selection == 3

# Counting of the votes
count_votes(simulator.proposition)
