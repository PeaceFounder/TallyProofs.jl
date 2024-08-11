module TallyProofs

using Random: RandomDevice
using CryptoGroups
using CryptoGroups: Group
using ShuffleProofs
using ShuffleProofs: Proposition, Simulator, Braid

braid(trackers::Vector{G}, g::G, x::Integer) where G <: Group = ShuffleProofs.braid(g, trackers; x)[1] # now for simplicity

# 
input_trackers(braid::Braid) = ShuffleProofs.input_members(braid)
output_trackers(braid::Braid) = ShuffleProofs.output_members(braid)

# Theese will be upstreamed to CryptoGroups and ShuffleProofs
include("elgamal.jl") 
include("shuffle.jl")


struct Exponentiation{G<:Group} <: Proposition
    g::G
    pk::G
    base::Vector{G}
    power::Vector{G}
end


struct Decryption{G<:Group, N} <: Proposition
    g::G
    pk::G
    cyphertexts::Vector{ElGamalRow{G, N}}
    plaintexts::Vector{NTuple{N, G}}
end

function decrypt(cyphertexts::Vector{<:ElGamalRow{G}}, g::G, x::Integer) where G <: Group

    dec = Dec(x)
    plaintexts = dec(cyphertexts)

    return Decryption(g, g^x, cyphertexts, plaintexts)
end

decrypt(cyphertexts::Vector{ElGamalElement{G}}, g::G, x::Integer) where G <: Group = decrypt(convert(Vector{ElGamalRow{G, 1}}, cyphertexts), g, x)

# Constructor shall ensure that pk and g are equal
struct RetrackShuffle{G<:Group} <: Proposition
    shuffle::Shuffle{G}
    decryption::Decryption{G, 1} 
    trackers::Vector{G} # output_trackers
end

#output_trackers(proposition::RetrackShuffle) = proposition.trackers
output_trackers(proposition::RetrackShuffle) = proposition.trackers #[i for (i,) in proposition.decryption.plaintexts]
input_trackers(proposition::RetrackShuffle) = [i[1].a for i in proposition.shuffle.𝐞]

public_key(proposition::RetrackShuffle) = proposition.decryption.pk
generator(proposition::RetrackShuffle) = proposition.decryption.g

input_elgamal(proposition::RetrackShuffle) = [i[2:end] for i in proposition.shuffle.𝐞]
output_elgamal(proposition::RetrackShuffle) = [i[2:end] for i in proposition.shuffle.𝐞′]


# This function belongs here because usually decryption is done in a threshold ceremony
# In what it matters this prcedure is the same as used in Selene system when shuffling and decryption of trackers 
# is done on a single host. In retracked_shuffle the messages are not decrypted as thoose can go down in a further pipeline
function retrack_shuffle(trackers::AbstractVector{G}, messages::AbstractVector{<:ElGamalRow{G}}, g::G, x::Integer) where G <: Group
    
    pk = g^x
    
    input_elgamal = [ElGamalRow([ElGamalElement(t, one(G)), m.row...]) for (t, m) in zip(trackers, messages)]

    _shuffle = shuffle(input_elgamal, g, pk)

    enc_trackers = [i[1] for i in output_elgamal(_shuffle)]
    decryption = decrypt(enc_trackers, g, x)
    output_trackers = inv.([i for (i,) in decryption.plaintexts])

    return RetrackShuffle(_shuffle, decryption, output_trackers)
end

function retrack_shuffle(trackers::AbstractVector{G}, messages::AbstractVector, g::G, x::Integer) where G <: Group

    N = length(messages[1])
    elgamal_messages = convert(Vector{ElGamalRow{G, N}}, messages)
    
    return retrack_shuffle(trackers, elgamal_messages, g, x)
end


# generators with respective zero knowledge proofs are created here
struct BraidSequence{G<:Group}
    braids::Vector{Braid{G}}
    coercion_generators::Vector{G}
    #generator_proofs # For coercion generators
end

generator(sequence::BraidSequence, n::Integer) = n == 0 ? input_generator(sequence.braids[1]) : output_generator(sequence.braids[n])
members(sequence::BraidSequence, n::Integer) = n == 0 ? input_members(sequence.braids[1]) : output_members(sequence.braids[n])

Base.length(sequence::BraidSequence) = length(sequence.braids)


function setup_braid_sequence(pseudonyms::Vector{G}, g::G, n::Integer, x::BigInt) where G <: Group
    
    braid_sequence = Braid{G}[]

    local trackers = pseudonyms

    for i in 1:n
        _braid = braid(trackers, g, x)
        push!(braid_sequence, _braid)
        trackers = output_members(_braid)
    end

    # coercion generators

    M = n + 4

    c = g^powermod(x, M, order(g))
    coercion_geenrators = []
    push!(coercion_generators, c)

    for i in 2:n
        c = c^powermod(x, 3, order(g))
        push!(coercion_generators, c)
    end
    
    return BraidSequence(braid_sequence, reverse(coercion_generators))
end


struct CastVote{G<:Group}
    #g::G # generator at which the tracker is valid
    tracker::G
    coercion_tag::ElGamalElement{G}
    selection::ElGamalRow{G}
end

struct CastVotes{G<:Group}
    g::G
    q::Union{G, Nothing} # Coercion generator
    # trackers::Vector{G}
    # coercion_tags::Vector{ElGamalElement{G}}
    # selections::Vector{ElGamalRow{G}}
    votes::Vector{CastVote{G}}
end


struct BareVotes{G<:Group}
    g::G
    trackers::Vector{G}
    selections::Vector{ElGamalRow{G}}
end

retrack_shuffle(votes::BareVotes, x::BigInt)::BareVotes = error("Unimplemented") 
retrack_shuffle(votes::CastVotes, x::BigInt)::CastVotes = error("Unimplemented") # coercion generator is set to nothing there



# struct PartialVoteDecryption{G<:Group}
#     votes::CastVotes
#     decryption::Decryption
#     coercion_tags::G # g uncoerced, g^2 coerced
# end

struct CoercionTags{G<:Group}
    tags::Decryption{G, 1}
    # encrypted_tags::Vector{ElGamalElement}
    # decryption::Decryption
    # tags::Vector{G}
end

function decrypt_coercion_tags(votes::CastVotes, x::BigInt)
    
    # return CoercionTags
end


struct CollectedVotes{G<:Group}
    cast_votes::Vector{CastVotes{G}}
    retrack_shuffles::Vector{RetrackShuffle{G}}
    coercion_tags::CoercionTags{G}
end

function collect_votes(cast_votes::Vector{CastVotes{<:Group}}, x::Integer)
    
    # return CollectedVotes
end 


function get_valid_votes(collection::CollectedVotes)
    # -----return CastVotes
    # return CastVotes with coercion generator as nothing
end

function get_coerced_trackers(collection::CollectedVotes) # Needed for backtracking valid votes
    # return Vector{G}
end


# struct DroppedVotes{G<:Group}
#     votes::Vector{CastVotes}
# end

function get_dropped_votes(collection::CollectedVotes)
    # return Vector{CastVotes}
    # coercion tag is being kept here
end


function generate_dummy_votes(votes::BareVotes, x::Integer) 
    # Dropped votes can be used to smooth out any patalogies
    
    # return CastVotes
    # coercion generator is nothing
end


struct SanitizedCastVotes{G<:Group}
    cast_votes::CastVotes{G}
    sanitized_votes::CastVotes{G}
    encrypted_trackers::Decryption
    # proof of resulting public key to be pk^{x^2} = q
end


# So I can have a function on vector and then on the 


function sanitize_votes(cast_votes::CastVotes, exponent::Integer, x::Integer)

    # return SanitizedCastVotes
end


function sanitize_votes(cast_votes::Vector{CastVotes}, x::Integer)


end


struct DroppedShuffle{G<:Group}
    dropped_votes::Vector{SanitizedCastVotes{G}} 
    dummy_votes::CastVotes{G} # Encrypted
    encrypted_trackers::Exponentiation{G} # for dropped votes, (Exponentiation would be a more proper type name)
    retrack_shuffle::RetrackShuffle{G}
    coercion_tags::CoercionTags
end


function dropped_vote_shuffle(dropped_votes::Vector{CastVotes{<:Group}}, x::Integer)

    # dummy_votes allow to smooth out potential patalogies in dropped votes
    dummy_votes = generate_dummy_votes(dropped_votes, x) 
    sanitized_dropped_votes = sanitize_votes(dropped_votes, x) 

    shuffled_votes = retrack_shuffle(sanitized_dropped_votes, x)
    tags = decrypt_coercion_tags(shuffled_votes, x)

    # fill in the rest...

    return #...
end


# encrypted_votes and 
struct Tally{G<:Group, N}
    trackers::Vector{G}
    #ecrypted_votes::ElGamalRow{G} # Skips the coercion tag
    #decryptions::Decryption
    selections::Vector{NTuple{N, G}}
end


function tally_coerced_votes(votes::DroppedShuffle, x::Integer)
    
    # return Tally
end


# I need to add votes into shuffle

# Coercion tags are stripped off from the shuffle
struct RevealShuffle{G<:Group}
    valid_votes::CastVotes{G}
    dummy_votes::Tally{G}
    retrack_shuffle::RetrackShuffle
end


function public_decryption_shuffle(votes::CastVotes, dummy_votes::Tally, x::Integer)

    # return RevealShuffle
end


function tally_votes(shuffle::RevealShuffle, x::Integer)

    # return Tally
end


# It is necessary that for each dummy vote selection there exist a valid vote which hence can create ambiguity
# otherwise unique vote selections can be filtereed out and hence is sucpetable to Italian style attacks. 
# An option is to do partial decryptions and shuffles if the type of ballots if a particular ballot allows that.
# Another option is to maintain a secret tally for some dummy votes that fixes the patalogies.
struct TallyProof{G<:Group}
    cast_votes::Vector{CastVotes{G}}
    skip_list::Vector{G} 
    collected_votes::CollectedVotes{G}
    dropped_shuffle::DroppedShuffle{G}
    dummy_votes::Tally{G} 
    reveal_shuffle::RevealShuffle{G}
    public_votes::Tally{G}
end


# skip_list allows to drop votes that have been cast with other means
function tally_votes(cast_votes::Vector{CastVotes{G}}, skip_list::Vector{G}, x::Integer) where G <: Group

    collected_votes = collect_votes(cast_votes, x) # BareVotes with coercion tags decrypted

    valid_votes = get_valid_votes(collected_votes)::BareVotes 

    dropped_votes = get_dropped_votes(collected_votes)::Vector{CastVotes} # also includes coerced ones at the end
    # raises exponent of the trackers so that they could be shuffled together wihtout
    # dealing with colisions and potential security implications of that

    shuffled_dropped_votes = dropped_vote_shuffle(dropped_votes, x) # 
    dummy_votes = get_coerced_votes(shuffled_dropped_votes)::BareVotes
    uncoerced_revotes = get_uncoerced_revotes(shuffled_dropped_votes)::BareVotes

    coerced_vote_trackers = get_coerced_vote_trackers(collected_votes) 
    recovered_votes = recover_valid_votes(uncoerced_revotes, coerced_vote_trackers, x)::BareVotes

    # Note that coerced votes dropped at the end are not coliding with recovered votes as their 
    # exponent had been raised. 
    collected_valid_votes = merge(valid_votes, recovered_votes)
    encrypted_public_votes = merge(skip(collected_valid_votes, skip_list), dummy_votes)::BareVotes
    shuffled_public_votes = retrack_shuffle(encrypted_public_votes, x)::BareVotes
    
    dummy_votes_tally = tally(dummy_votes, x)::Tally # votes that are added to the reveal shuffle
    public_votes_tally = tally(shuffled_public_votes, x)::Tally
    
    return trackers(collected_valid_votes), dummy_votes_tally, public_votes_tally
end



end # module TallyProofs


