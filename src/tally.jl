using CryptoGroups: Group, order, octet
using CryptoGroups.Utils: int2octet!, octet2int, @check
using CryptoPRG: HashSpec
using CryptoPRG.Verificatum: PRG
using SigmaProofs: Proposition, Proof, Verifier, Simulator
import SigmaProofs: prove, verify, proof_type

using .HMACWatermark: apply_watermark

struct DecoyCommitment{G <: Group}
    Q::G # tracker commitment
    R::G
    selection::BigInt
end

function DecoyCommitment(opening::VoteOpening, setup::GeneratorSetup{<:Group})

    (; tracker, selection, γ) = opening

    @check γ == 0 "vote must be unblinded"

    Q, R = commitment(tracker, setup)

    return DecoyCommitment(Q, R, selection) # Needs to have also R
end

function commitment(vote::DecoyCommitment{G}, setup::GeneratorSetup{G}) where G <: Group
    
     (; g) = setup
     (; Q, R, selection) = vote
    
     V = g^selection
    
     return VoteCommitment(Q, R, V)
end

struct TallyRecord
    raw_tracker::BigInt
    display_tracker::BigInt
    selection::BigInt
end

struct Tally{G <: Group} <: Proposition
    proposal::Proposal
    cast_commitments::Vector{G}
    vote_commitments::Vector{CastRecord{G}}
    skip_list::Vector{G} # In case voter had cast a vote with other means
    dummy_votes::Vector{DecoyCommitment{G}}
    coercion_token::BigInt # decoy_tracker_challenge
    tokens::Vector{<:Integer} # tracker_challenges
    tally::Vector{TallyRecord} # tally_board 
end

struct TallyProof{G <: Group} <: Proof
    supersession::SupersessionProof{G}
    reveal::RevealShuffleProof{G}
end

proof_type(::Type{Tally{G}}) where G <: Group = TallyProof{G}

function extract_supersession(cast_openings::Vector{<:CastOpening})

    pseudonyms = [i.record.signature.pbkey for i in cast_openings]
    width = [length(trim(i.history)) for i in cast_openings]
    
    mask = extract_maximum_mask(pseudonyms, width)

    return mask
end

function compute_tokens(seed::Vector{UInt8}, ux::Vector{G}, token_max::Int, watermark_nbits::Int, hasher::HashSpec) where G <: Group

    prg = PRG(hasher, seed)

    nbits = ndigits(token_max, base=2) - 1
    offset = token_max - 2^nbits

    token_seeds = rand(prg, 0:BigInt(2)^nbits - 1, length(ux))
    tokens = [apply_watermark(ti, nbits, octet(uxi), hasher; num_positions = watermark_nbits) + offset for (ti, uxi) in zip(token_seeds, ux)]
    
    return tokens
end

function token_seed(Q::Vector{G}, R::Vector{G}, hasher::HashSpec) where G <: Group
    Q_vec = (octet(i) for i in Q)
    R_vec = (octet(i) for i in R)
    return hasher(UInt8[Iterators.flatten(R_vec) |> collect; Iterators.flatten(Q_vec) |> collect])
end

function tally(proposal::Proposal, cast_commitments::Vector{G}, cast_openings::Vector{CastOpening{G}}, hasher::HashSpec; skip_list = G[], mask = extract_supersession(cast_openings), dummy_votes::Vector{VoteOpening} = VoteOpening[]) where G <: Group

    (; token_max, watermark_nbits) = proposal

    public_cast_openings = @view(cast_openings[mask])
    
    pseudonyms = (i.record.signature.pbkey for i in public_cast_openings)
    skip_mask = BitVector(!(x in skip_list) for x in pseudonyms)

    public_dummy_votes = DecoyCommitment{G}[DecoyCommitment(i, proposal.basis) for i in dummy_votes]

    Q_vec = [i.record.commitment.Q for i in public_cast_openings]
    R_vec = [i.record.commitment.R for i in public_cast_openings]
    
    seed = token_seed(Q_vec, R_vec, hasher)
    tokens = compute_tokens(seed, Q_vec, token_max, watermark_nbits, hasher)

    tracker_challenges = tokens[skip_mask] #.|> BigInt

    Q′_vec = [i.Q for i in public_dummy_votes]
    R′_vec = [i.R for i in public_dummy_votes]

    decoy_seed = [seed; token_seed(Q′_vec, R′_vec, hasher)]
    
    coercion_token = rand(PRG(hasher, decoy_seed), 2:order(G) - 1) 

    append!(tracker_challenges, (coercion_token for i in eachindex(dummy_votes)))
    total_tracker_challenges = tracker_challenges
    
    vote_openings = (i.opening for i in @view(public_cast_openings[skip_mask])) # added here
    total_vote_openings = Iterators.flatten((vote_openings, dummy_votes))
    trackers = (tracker(opening, chg, order(proposal.g)) for (chg, opening) in zip(total_tracker_challenges, total_vote_openings))

    tally = TallyRecord[TallyRecord(Ti, octet2int(hasher(int2octet(Ti))[1:8]), opening.selection) for (Ti, opening) in zip(trackers, total_vote_openings)]

    vote_commitments = [i.record for i in public_cast_openings]

    return Tally(proposal, cast_commitments, vote_commitments, skip_list, public_dummy_votes, coercion_token, tokens, tally)
end

function reduce_representation(cast_openings::Vector{CastOpening{G}}, u::Vector{G}, ux::Vector{G}, history::Vector{Vector{BigInt}}, hasher::HashSpec) where G <: Group

    pseudonyms = (i.commitment.signature.pbkey for i in cast_openings)

    _u = (sup_generator(ci, hasher) for ci in cast_openings)
    _ux = (i.record.ux for i in cast_openings) 
    pok = (i.record.pok for i in cast_openings)
    _history = (i.history for i in cast_openings)
    β = (i.β for i in cast_openings)

    recommits = [SuccessionOpening(βi, ui, uxi, historyi, poki) for (βi, ui, uxi, historyi, poki) in zip(β, _u, _ux, _history, pok)]

    return reduce_representation(recommits, u, ux, history)
end

function validate(cast_openings::Vector{CastOpening{G}}, proposal::Proposal{G}, verifier::Verifier; mask = extract_supersession(cast_openings)) where G <: Group

    for i in @view(cast_openings[mask])
        @check isconsistent(i, proposal, verifier) "Consistency check have failed"
        for j in cast_openings
            if i.record.signature.pbkey == j.record.signature.pbkey
                @check isconsistent(i, j) "Consistency check have failed"
            end
        end
    end

    return
end

function prove(proposition::Tally{G}, verifier::Verifier, cast_openings::Vector{CastOpening{G}}, 𝛙_reveal::Vector{Int}; mask = extract_supersession(cast_openings), roprg = gen_roprg(), dummy_votes::Vector{VoteOpening} = VoteOpening[], validate_openings::Bool = true) where G <: Group

    hasher = verifier.prghash

    validate_openings && validate(cast_openings, proposition.proposal, verifier; mask)

    u = [sup_generator(i, hasher) for i in proposition.vote_commitments]
    ux = [i.ux for i in proposition.vote_commitments]
    pok = [i.pok for i in proposition.vote_commitments]

    history = [copy(trim(i.history)) for i in @view(cast_openings[mask])]

    ψ, α = reduce_representation(cast_openings, u, ux, history, hasher)
    β = [i.β for i in cast_openings]

    supersession_proposition = Supersession(proposition.cast_commitments, proposition.proposal.basis.h, u, ux, pok)

    supersession_proof = prove(supersession_proposition, verifier, ψ, β, α; roprg = gen_roprg(roprg(:supersession))) 
    skip_mask = BitVector(!(x.signature.pbkey in proposition.skip_list) for x in proposition.vote_commitments)

    tracker_challenges = proposition.tokens[skip_mask]
    coercion_tracker_challenges = (proposition.coercion_token for i in eachindex(proposition.dummy_votes))
    total_tracker_challenges = collect(BigInt, Iterators.flatten((tracker_challenges, coercion_tracker_challenges)))
    
    vote_commitments = (i.commitment for i in @view(proposition.vote_commitments[skip_mask]))
    dummy_vote_commitments = (commitment(i, proposition.proposal.basis) for i in dummy_votes)
    total_vote_commitments = collect(VoteCommitment{G}, Iterators.flatten((vote_commitments, dummy_vote_commitments)))
    
    reveal_proposition = RevealShuffle(proposition.proposal.basis, total_tracker_challenges, total_vote_commitments, [VoteRecord(i.raw_tracker, i.selection) for i in proposition.tally])

    vote_openings = (i.opening for i in @view(cast_openings[mask][skip_mask]))

    total_vote_openings = collect(VoteOpening, Iterators.flatten((vote_openings, dummy_votes)))

    reveal_proof = prove(reveal_proposition, verifier, total_vote_openings, 𝛙_reveal; roprg = gen_roprg(roprg(:reveal)))    

    return TallyProof(supersession_proof, reveal_proof)
end

function extract_decoy_votes(cast_openings)

    indicies = unique(reverse(eachindex(cast_openings))) do i
        
        (; θ, λ) = cast_openings[i].decoy
        pseudonym = cast_openings[i].record.signature.pbkey

        return (octet(pseudonym), θ, λ) # need to add hash for CryptoGroups
    end

    decoys = [i.decoy for i in @view(cast_openings[indicies]) if !iszero(i.decoy.selection)]

    return decoys
end

function compute_dummy_votes(votes, range; roprg = gen_roprg)
    return [VoteOpening(vi, range) for (i, vi) in enumerate(votes)] # need to add roprg here
end

function tally(proposal::Proposal, cast_commitments::Vector{G}, cast_openings::Vector{CastOpening{G}}, verifier::Verifier; skip_list = G[], decoy_votes::Vector{DecoyOpening} = DecoyOpening[], dummy_votes::Vector{VoteOpening} = compute_dummy_votes(Iterators.flatten((decoy_votes, extract_decoy_votes(cast_openings))), 2:order(G) - 1)) where G <: Group

    hasher = verifier.prghash

    filter_mask = extract_supersession(cast_openings)
    commit_perm = sortperm(@view(cast_openings[filter_mask]); by = x -> x.record.signature.pbkey)
    
    mask = findall(filter_mask)[commit_perm]

    proposition = tally(proposal, cast_commitments, cast_openings, hasher; skip_list, mask, dummy_votes)

    𝛙 = sortperm(proposition.tally, by = x -> x.display_tracker) # this may also work with the added dummy votes
    permute!(proposition.tally, 𝛙)

    proof = prove(proposition, verifier, cast_openings, 𝛙; mask, dummy_votes) 

    return Simulator(proposition, proof, verifier)    
end

function decoy_token(seed::Vector{UInt8}, decoy_votes::Vector{DecoyCommitment{G}}, hasher) where G <: Group

    Q′_vec = [i.Q for i in decoy_votes]
    R′_vec = [i.R for i in decoy_votes]

    decoy_seed = [seed; token_seed(Q′_vec, R′_vec, hasher)]

    return rand(PRG(hasher, decoy_seed), 2:order(G) - 1)
end

function verify(proposition::Tally{G}, proof::TallyProof{G}, verifier::Verifier) where G <: Group
    
    hasher = verifier.prghash

    (; h, g) = proposition.proposal.basis
    proposition.proposal.basis == GeneratorSetup(h, g) || return false
    
    (; token_max, watermark_nbits) = proposition.proposal
    (; vote_commitments, cast_commitments) = proposition

    for i in proposition.vote_commitments
        verify(i, proposition.proposal.g) || return false
    end

    u = [sup_generator(i, hasher) for i in vote_commitments]
    ux = [i.ux for i in vote_commitments]
    pok = [i.pok for i in vote_commitments]
    
    supersession_proposition = Supersession(cast_commitments, h, u, ux, pok)
    verify(supersession_proposition, proof.supersession, verifier) || return false

    # Verifying tokens
    Q_vec = [i.commitment.Q for i in vote_commitments]
    R_vec = [i.commitment.R for i in vote_commitments]
    seed = token_seed(Q_vec, R_vec, hasher)
    tokens = compute_tokens(seed, Q_vec, token_max, watermark_nbits, hasher)

    proposition.tokens == tokens || return false
    proposition.coercion_token == decoy_token(seed, proposition.dummy_votes, hasher) || return false

    # Making revaal shuffle taking into account skip_list and decoy_votes
    skip_mask = BitVector(!(x.signature.pbkey in proposition.skip_list) for x in vote_commitments)

    tracker_challenges = tokens[skip_mask] 
    append!(tracker_challenges, Iterators.repeated(proposition.coercion_token, length(proposition.dummy_votes)))

    reveal_vote_commitments = [i.commitment for i in @view(vote_commitments[skip_mask])]
    append!(reveal_vote_commitments, (commitment(i, proposition.proposal.basis) for i in proposition.dummy_votes))

    reveal_proposition = RevealShuffle(proposition.proposal.basis, tracker_challenges, reveal_vote_commitments, [VoteRecord(i.raw_tracker, i.selection) for i in proposition.tally])

    verify(reveal_proposition, proof.reveal, verifier) || return false

    return true
end
