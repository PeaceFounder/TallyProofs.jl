using Test
using TallyProofs
using CryptoGroups
using SigmaProofs
import TallyProofs: Proposal, CastOppening, VotingCalculator, assemble_vote!, verify, check_challenge, CastReceipt, tally, get_token, compute_tracker, Vote

import SigmaProofs.Parser: Tree, encode

G = @ECGroup{P_192}
g = G()

verifier = SigmaProofs.Verificatum.ProtocolSpec(; g)
hasher = verifier.prghash

alice_key = 535
bob_key = 4234
eve_key = 21
ted_key = 56

tallying_authorithy_key = 453

# Buletin Board
proposal = Proposal(g, g^tallying_authorithy_key, verifier) 

members = sort([g^x for x in [alice_key, bob_key, eve_key, ted_key]]) # In practice the list is obtained in braiding 

cast_commitments = G[]
cast_proofs = G[]

# Secrets for tallying authorithy
cast_oppenings = CastOppening{G}[]

function deliver_vote!(vote)

    @test vote.proposal == hasher(encode(Tree(proposal))) # "Incorrect proposal"

    alias = findfirst(isequal(vote.signature.pbkey), members)
    @test !isnothing(alias) #"Voter is not a registered member"

    @test verify(vote, g) # "The signature is not valid"
    # recommit and consistency with oppening should be also performed

    push!(cast_commitments, vote.C)
    push!(cast_proofs, vote.A)
    
    push!(cast_oppenings, vote.oppening)
    
    cast_index = length(cast_commitments)
    
    return alias, cast_index
end

function cast_vote!(voter, selection, chg, pin)
   
    vote = assemble_vote!(voter, selection, chg, pin; inherit_challenge=false)

    tree = Tree(vote)
    @test Tree(convert(Vote{G}, tree)) == tree
    #@show length(encode(tree))

    @test check_challenge(vote, chg, voter.hasher) # "Challenge is not correct. The calculator may be corrupted."
    @test verify(vote, g) # "The signature is not valid" # g, hasher

    alias, cast_index = deliver_vote!(vote)
    
    return CastReceipt(alias, cast_index, chg)
end


pin = 4321 # The same pin code for all calculators

# verifier and the pin code would be inherited as well as the key, 
# whereas proposal defines the instance!
alice = VotingCalculator(proposal, verifier, alice_key, pin) 
bob = VotingCalculator(proposal, verifier, bob_key, pin)
eve = VotingCalculator(proposal, verifier, eve_key, pin)
ted = VotingCalculator(proposal, verifier, ted_key, pin)

alice_receipt = cast_vote!(alice, 3, 45534, pin)
bob_receipt = cast_vote!(bob, 4, 34534, pin)
eve_receipt = cast_vote!(eve, 7, 9992, pin)
bob_receipt = cast_vote!(bob, 2, 3454, pin)
ted_receipt = cast_vote!(ted, 4, 1245, pin)

simulator = tally(proposal, cast_commitments, cast_oppenings, verifier; skip_list = [g^ted_key])
@test verify(simulator)

# now comes the verifications

alice_token = get_token(simulator.proposition, cast_proofs, members, alice_receipt, hasher)
alice_tracker = compute_tracker(alice, alice_token, pin) # this is a hash of the tracker

N = findfirst(x -> x.tracker == alice_tracker, simulator.proposition.tally)
@test simulator.proposition.tally[N].selection == 3

ted_token = get_token(simulator.proposition, cast_proofs, members, ted_receipt, hasher)
ted_tracker = compute_tracker(ted, ted_token, pin) # this is a hash of the tracker

N = findfirst(x -> x.tracker == ted_tracker, simulator.proposition.tally)
@test isnothing(N)


for i in simulator.proposition.tally
    (; tracker, selection) = i
    short_tracker = div(tracker, 10^12)
    println("$(lpad(short_tracker, 9)) : $selection")
end
