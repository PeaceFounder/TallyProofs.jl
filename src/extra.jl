# any pin code is sufficient 
struct CastReceipt
    alias::Int
    id::Vector{UInt8}
    w::Vector{UInt8} # the blinding factor
end

#function get_token(tally::Tally{G}, cast_proofs::Vector{G}, members::Vector{G}, receipt::CastReceipt, hasher::HashSpec; skip_checks=false, commitment_challenge = receipt.chg) where G <: Group

function get_token(tally::Tally{G}, members::Vector{G}, receipt::CastReceipt, hasher::HashSpec; skip_checks=false) where G <: Group

    (; alias, id, w) = receipt

    pseudonym = members[alias]
    
    N = findfirst(x -> x.signature.pbkey == pseudonym, tally.vote_commitments)
    vote_commitment = tally.vote_commitments[N]

    I = hasher([w; id])

    @check vote_commitment.I == I "Identity commitment is not consistent with provided oppenings. Cannot assert exclusive ownership of the pseudonym. Your voting device have provided incorrect receipt for the cast vote if the same problem occurs using different devices for verifying."

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
