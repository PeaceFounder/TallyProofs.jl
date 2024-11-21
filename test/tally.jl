using Test
using TallyProofs
using CryptoGroups
using SigmaProofs
import TallyProofs: Proposal, CastOppening, VotingCalculator, assemble_vote!, verify, check_challenge, CastReceipt, tally, tracker_challenge, compute_tracker

#using SigmaProofs.Verificatum: generator_basis
#using CryptoPRG.Verificatum: PRG
#import TallyProofs: GeneratorSetup, vote_oppening, vote_commitment, reveal, verify, tracker, VoteCommitment, VoteOppening

G = @ECGroup{P_192}
g = G()

verifier = SigmaProofs.Verificatum.ProtocolSpec(; g)
hasher = verifier.prghash

alice_key = 535
bob_key = 4234
eve_key = 21

tallying_authorithy_key = 453

# Buletin Board
proposal = Proposal(g, g^tallying_authorithy_key, 1:10) 

members = sort([g^x for x in [alice_key, bob_key, eve_key]]) # In practice the list is obtained in braiding 

cast_commitments = G[]
cast_proofs = G[]

# Secrets for tallying authorithy
cast_oppenings = CastOppening{G}[]

function deliver_vote!(vote)

    #@test vote.proposal == digest(proposal) # "Incorrect proposal"

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

    @test check_challenge(vote, chg, voter.hasher) # "Challenge is not correct. The calculator may be corrupted."
    @test verify(vote, g) # "The signature is not valid" # g, hasher

    alias, cast_index = deliver_vote!(vote)
    
    return CastReceipt(alias, cast_index, chg)
end


pin = 4321 # The same pin code for all calculators

alice = VotingCalculator(proposal, verifier, alice_key, pin) # verifier and the pin code would be inherited as well as the key, whereas proposal defines the instance!
bob = VotingCalculator(proposal, verifier, bob_key, pin)
eve = VotingCalculator(proposal, verifier, eve_key, pin)

alice_receipt = cast_vote!(alice, 3, 45534, pin)
bob_receipt = cast_vote!(bob, 4, 34534, pin)
eve_receipt = cast_vote!(eve, 7, 9992, pin)

simulator = tally(cast_commitments, cast_oppenings, verifier)
@test verify(simulator)

# now comes the verifications

tchg = tracker_challenge(simulator.proposition, cast_proofs, members, alice_receipt, hasher)
alice_tracker = compute_tracker(alice, tchg, pin) # this is a hash of the tracker

N = findfirst(x -> x.tracker == alice_tracker, simulator.proposition.tally)
@test simulator.proposition.tally[N].selection == 3


for i in simulator.proposition.tally
    (; tracker, selection) = i
    short_tracker = div(tracker, 10^12)
    println("$(lpad(short_tracker, 9)) : $selection")
end
