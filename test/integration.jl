using Tests
#using TallyProofs
import TallyProofs: setup_braid_sequence, CastVotes
import CryptoGroups: curve, ECGroup, generator, specialize

_curve = curve("P_192")
G = specialize(ECGroup, _curve)
g = G(generator(_curve))

x = 232
pk = g^x

y = [2, 3, 4, 5, 6, 7, 8] 
Y = g .^ y # the public keys

braid_sequence = setup_braid_sequence(Y, g, 4, x)


function vote(tracker, option; coerced=false)

    enc = Enc(pk, g) # global scope

    r = rand(1:1000)

    coercion_tag = enc(g^(coerced+1), r)

    selection_serialization = (g^option,)
    selection_encryption = enc((g^option,), r)

    return CastVote(tracker, coercion_tag, selection_encryption)
end


function cast_vote!(bbox::CastVotes, key::Integer, option; coerced=false)

    tracker = bbox.g^key
    v = vote(tracker, option; coerced)

    push!(bbox.votes, v)

    return v
end


function create_bbox(braid_sequence, n)

    g = generator(braid_sequence, n)
    q = coercion_generator(braid_sequence, n)
    
    return CastVote(g, q, votes)
end


bbox0 = create_bbox(braid_sequence, 0)
cast_vote!(bbox0, y[2], 2; coerced=true)
cast_vote!(bbox0, y[3], 1)
cast_vote!(bbox0, y[5], 3)

bbox1 = create_bbox(braid_sequence, 1)
cast_vote!(bbox1, y[2], 3)
cast_vote!(bbox1, y[5], 2)
cast_vote!(bbox1, y[1], 3)

bbox2 = create_bbox(braid_sequence, 2)
cast_vote!(bbox1, y[6], 1)
cast_vote!(bbox1, y[7], 2)
cast_vote!(bbox1, y[1], 1; coerced=true)

bbox3 = create_bbox(braid_sequence, 3)
cast_vote!(bbox1, y[1], 3)
cast_vote!(bbox1, y[5], 3)
cast_vote!(bbox1, y[2], 2; coerced=true)

# The bbox4 is for skiplist and decryption of coercion tags

collected_votes = collect_votes([bbox0, bbox1, bbox2, bbox3], x)

coerced_vote_trackers = get_coerced_votes(collected_votes)
encrypted_valid_votes = get_valid_votes(collected_votes)

g4 = generator(braid_sequence, 4)

@test length(coerced_vote_trackers) == 1
@test g4^y[2] in coerced_vote_trackers

@test length(encrypted_valid_votes) == 6
@test g4^y[1] in encrypted_valid_votes.trackers
@test g4^y[3] in encrypted_valid_votes.trackers
@test g4^y[4] in encrypted_valid_votes.trackers
@test g4^y[5] in encrypted_valid_votes.trackers
@test g4^y[6] in encrypted_valid_votes.trackers
@test g4^y[7] in encrypted_valid_votes.trackers

shuffled_votes = retrack_shuffle(encrypted_valid_votes, x)
public_votes_tally = tally(shuffled_votes, x)

# Checking that every vote is in desired collection
