using CryptoGroups
using SigmaProofs.Verificatum: ProtocolSpec
using TallyProofs

G = @ECGroup{P_192}
g = G()

verifier = ProtocolSpec(; g)

# Tallier Secrets
tallier_key = 453
cast_openings = CastOpening{G}[]

# Public Bulletin Board
pid = 1 # proposal identifier
proposal = Proposal(pid, g, g^tallier_key, verifier; token_max=999)
members = G[]
cast_commitments = G[]

# Tallier Controller
function record_vote!(vote)
    alias = findfirst(isequal(vote.signature.pbkey), members)
    @assert !isnothing(alias) "Voter is not a registered member"
    @assert verify(vote, proposal.g) "Signature on the vote envelope invalid"

    cast_opening = extract_opening(vote, proposal, verifier, tallier_key)
    @assert isconsistent(cast_openings, cast_opening) "Cast opening inconsistent with previous cast"

    push!(cast_commitments, vote.C)
    push!(cast_openings, cast_opening)

    return alias, length(cast_commitments)
end

# Registration
alice = VotingCalculator(b"Alice", g, verifier, 1234) 
bob = VotingCalculator(b"Bob", g, verifier, 5678)
eve = VotingCalculator(b"Eve", g, verifier, 4321)

append!(members, [g^i.key for i in [alice, bob, eve]]) # registration

# Voting Device Controller
function cast_vote!(voter, proposal, selection, pin)
    chg = rand(2:order(G)-1)
    context = assemble_vote!(voter, proposal, selection, chg, pin)
    @assert isconsistent(context, chg, g, voter.hasher, voter.verifier) "Vote is not correctly formed"
    alias, cast_index = record_vote!(context.vote)
    
    return CastReceipt(alias, context.id, seed(context.π_w))
end

# Vote Casting
alice_receipt = cast_vote!(alice, proposal, 3, alice.pin)
bob_receipt = cast_vote!(bob, proposal, 4, bob.pin)
eve_receipt = cast_vote!(eve, proposal, 6, eve.pin)
bob_receipt = cast_vote!(bob, proposal, 1, bob.pin) # anyone can revote


# Universal Verifiability
simulator = tally(proposal, cast_commitments, cast_openings, verifier)
@assert verify(simulator) "Integrity audit has failed"

# Individual Verifiability
@assert alice_receipt.id == b"Alice" "Cast receipt is not owned"
alice_token = get_token(simulator.proposition, members, alice_receipt, proposal.hasher)
alice_tracker = compute_tracker(alice, pid, alice_token, alice.pin)
N = findfirst(x -> x.display_tracker == alice_tracker, simulator.proposition.tally_board)
@assert simulator.proposition.tally_board[N].selection == 3 "Vote is not cast as intended"

# Counting of the votes
count_votes(simulator.proposition)
