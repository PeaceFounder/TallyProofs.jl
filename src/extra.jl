# any pin code is sufficient 
struct CastReceipt
    alias::Int
    cast_index::Int
    chg::BigInt
end

function get_token(tally::Tally{G}, cast_proofs::Vector{G}, members::Vector{G}, receipt::CastReceipt, hasher::HashSpec; skip_checks=false, commitment_challenge = receipt.chg) where G <: Group

    (; cast_index, alias, chg) = receipt

    C = tally.cast_commitments[cast_index]
    A = cast_proofs[cast_index]

    pseudonym = members[alias]
    
    N = findfirst(x -> x.signature.pbkey == pseudonym, tally.vote_commitments)
    vote_commitment = tally.vote_commitments[N]

    u = map2generator(pseudonym, hasher)

    @check !check_challenge(C, A, u, chg, hasher) "Cast challenge is not correct. Vote may not have been delivered to the ballotbox by a malicious voters device or there is an error in either challenge, cast_index or alias. Update history tree consistency proofs to ensure that the commitment had been retained on the buletin board."
    
    if isnothing(commitment_challenge)

        @warn "Skipping vote commitment challenge. It is not possible to assert exclusive ownership of the pseudonym without putting trust into voting calculator or (tallying authorithy and voting device (to not leak secrets to addversary))."
        
    else

        buffer = zeros(UInt8, 16)
        int2octet!(buffer, chg)
        blinded_challenge = hasher([buffer; octet(A)])

        @check blinded_challenge == vote_commitment.challenge "Vote commitment challenge incorrect"

    end

    return tally.tokens[N]
end

function count_votes(tally::Tally)

    counts = Dict{BigInt, Int}()
    
    for record in tally.tally
        counts[record.selection] = get(counts, record.selection, 0) + 1
    end
    
    for dummy in tally.dummy_votes
        counts[dummy.selection] = get(counts, dummy.selection, 0) - 1
    end

    # Convert to array of tuples and sort by count (descending)
    sorted_tuples = [(k, v) for (k, v) in counts if !iszero(v)]
    sort!(sorted_tuples, by=x->x[2], rev=true)
    
    return sorted_tuples
end
