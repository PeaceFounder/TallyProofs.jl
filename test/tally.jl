using Test
using TallyProofs
using CryptoGroups
using SigmaProofs
import TallyProofs: Proposal, CastOpening, VotingCalculator, assemble_vote!, verify, CastReceipt, tally, get_token, compute_tracker, VoteEnvelope, extract_opening, install_decoy_tracker!, create_decoy_credential!, DecoyOpening, count_votes, isconsistent, isbinding, seed, extract_decoy_votes

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
#proposal = Proposal(g, g^tallying_authorithy_key, verifier; encrypt_spec=TallyProofs.PlaintextMode(), token_max=999) 
pid = 1 # proposal identifier
proposal = Proposal(pid, g, g^tallying_authorithy_key, verifier; token_max=999)
@test Tree(convert(Proposal{G}, Tree(proposal))) == Tree(proposal)

members = sort([g^x for x in [alice_key, bob_key, eve_key, ted_key]]) # In practice the list is obtained in braiding 

cast_commitments = G[]

# Secrets for tallying authorithy
cast_openings = CastOpening{G}[]

function record_vote!(vote)

    @test vote.proposal == hasher(encode(Tree(proposal))) # "Incorrect proposal"

    alias = findfirst(isequal(vote.signature.pbkey), members)
    @test !isnothing(alias) #"Voter is not a registered member"
    @test verify(vote, proposal.g) # signature check

    # extracts cast opening and verifies it's consistency
    cast_opening = extract_opening(vote, proposal, verifier, tallying_authorithy_key)
    
    @test isconsistent(cast_openings, cast_opening)

    push!(cast_commitments, vote.C)
    push!(cast_openings, cast_opening)

    cast_index = length(cast_commitments)
    
    return alias, cast_index
end

function cast_vote!(voter, proposal, selection, pin)
   
    chg = rand(2:order(G)-1)

    context = assemble_vote!(voter, proposal, selection, chg, pin)

    tree = Tree(context.vote)
    @test Tree(convert(VoteEnvelope{G}, tree)) == tree
    #@show length(encode(tree))

    @test isconsistent(context, chg, g, voter.hasher, voter.verifier)

    alias, cast_index = record_vote!(context.vote)
    # cast_index is kept by the voting device for locting cast commitment on the buletin board
    
    return CastReceipt(alias, context.id, seed(context.π_w))
end

pin = 4321 # The same pin code for all calculators

alice = VotingCalculator(b"Alice", g, verifier, pin; history_width = 2, key = alice_key) 
bob = VotingCalculator(b"Bob", g, verifier, pin; history_width = 2, key = bob_key)
eve = VotingCalculator(b"Eve", g, verifier, pin; history_width = 2, key = eve_key)
ted = VotingCalculator(b"Ted", g, verifier, pin; key = ted_key)

alice_receipt = cast_vote!(alice, proposal, 3, pin)
bob_receipt = cast_vote!(bob, proposal, 4, pin)
eve_receipt = cast_vote!(eve, proposal, 6, pin)
bob_receipt = cast_vote!(bob, proposal, 0, pin)
ted_receipt = cast_vote!(ted, proposal, 4, pin)

fake_pin = 2341 # pin code that is shown to a coercer
eve_seed = create_decoy_credential!(eve, fake_pin, pin)

eve_receipt = cast_vote!(eve, proposal, 5, fake_pin)
eve_receipt = cast_vote!(eve, proposal, 11, fake_pin)

# By default decoy_votes = extract_decoy_votes(cast_openings)
decoy_votes = append!(extract_decoy_votes(cast_openings), [DecoyOpening(8, 2:order(G) - 1), DecoyOpening(9, 2:order(G) - 1)])
simulator = tally(proposal, cast_commitments, cast_openings, verifier; skip_list = [g^ted_key], decoy_votes)
@test verify(simulator)

# now comes the verifications

alice_token = get_token(simulator.proposition, members, alice_receipt, hasher)
alice_tracker = compute_tracker(alice, pid, alice_token, pin) # this is a hash of the tracker

N = findfirst(x -> x.display_tracker == alice_tracker, simulator.proposition.tally_board)
@test simulator.proposition.tally_board[N].selection == 3

ted_token = get_token(simulator.proposition, members, ted_receipt, hasher)
ted_tracker = compute_tracker(ted, pid, ted_token, pin) # this is a hash of the tracker

N = findfirst(x -> x.display_tracker == ted_tracker, simulator.proposition.tally_board)
@test isnothing(N)

coercion_tracker = compute_tracker(proposal, eve_seed, simulator.proposition.decoy_challenge)
N = findfirst(x -> x.display_tracker == coercion_tracker, simulator.proposition.tally_board)
@test !isnothing(N)
@test simulator.proposition.tally_board[N].selection == 11

# eve installs decoy tracker before the tokens are anounced
install_decoy_tracker!(eve, pid, coercion_tracker, fake_pin)

eve_token = get_token(simulator.proposition, members, eve_receipt, hasher)

@test get(eve, pid).trigger_token[] == nothing
fake_eve_tracker = compute_tracker(eve, pid, eve_token, fake_pin)
@test get(eve, pid).trigger_token[] == eve_token

@test fake_eve_tracker == coercion_tracker

real_eve_tracker = compute_tracker(eve, pid, eve_token, pin)
@test fake_eve_tracker != real_eve_tracker

# pin codes must be indistinguishable to coercer hence:
second_fake_pin = 4566 

eve_seed2 = create_decoy_credential!(eve, second_fake_pin, pin)
install_decoy_tracker!(eve, pid, coercion_tracker, second_fake_pin)

second_eve_tracker = compute_tracker(eve, pid, eve_token, second_fake_pin)
@test second_eve_tracker == coercion_tracker

# computing untriggered token

nbits = ndigits(proposal.token_max; base=2) - 1

reversed_eve_token = ~eve_token & ((1 << nbits) - 1)
fake_eve_tracker = compute_tracker(eve, pid, reversed_eve_token, fake_pin)
real_eve_tracker = compute_tracker(eve, pid, reversed_eve_token, pin)

@test fake_eve_tracker != real_eve_tracker

# Testing probability for a coercer to guess the tracker

let 
    hits = 0

    nbits = ndigits(proposal.token_max; base=2) - 1
    start = proposal.token_max - 2^nbits
    stop = proposal.token_max

    for trial_token in start:stop

        compute_tracker(eve, pid, trial_token, fake_pin; reset_trigger_token = true) # trigger_token
        
        if get(eve, pid).trigger_token[] == trial_token
            hits += 1
        end
    end

    @test hits <= 64
end

println("\nTally Board:\n")

for i in simulator.proposition.tally_board
    (; display_tracker, selection) = i
    short_tracker = div(display_tracker, 10^12)
    println("$(lpad(short_tracker, 9)) : $selection")
end

println("\nTally Count:\n")

for (key, count) in count_votes(simulator.proposition)
    println("$(lpad(key, 4)) : $count")
end
