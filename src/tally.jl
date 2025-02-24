using CryptoGroups: Group, order, octet
using CryptoGroups.Utils: int2octet!, octet2int, @check
using CryptoPRG: HashSpec
using CryptoPRG.Verificatum: PRG
using SigmaProofs: Proposition, Proof, Verifier, Simulator
import SigmaProofs: prove, verify, proof_type

using .HMACWatermark: apply_watermark

struct DecoyCommitment{G <: Group}
    Q::G
    R::G
    selection::BigInt
end

function DecoyCommitment(opening::VoteOpening, setup::GeneratorSetup{<:Group})

    (; tracker, selection, γ) = opening
    @check γ == 0 "vote must be unblinded"
    Q, R = commitment(tracker, setup)

    return DecoyCommitment(Q, R, selection) 
end

function commitment(vote::DecoyCommitment{G}, setup::GeneratorSetup{G}) where G <: Group
    
     (; g) = setup
     (; Q, R, selection) = vote
    
     V = g^selection
    
     return VoteCommitment(Q, R, V)
end

struct TallyRecord
    preimage_tracker::BigInt
    display_tracker::BigInt
    selection::BigInt
end

struct Tally{G <: Group} <: Proposition
    proposal::Proposal
    cast_commitments::Vector{G}
    cast_records::Vector{CastRecord{G}}
    skip_list::Vector{G} # In case voter had cast a vote with other means
    decoy_votes::Vector{DecoyCommitment{G}}
    decoy_challenge::BigInt 
    tracker_challenges::Vector{<:Integer} 
    tally_board::Vector{TallyRecord} 
end

struct TallyProof{G <: Group} <: Proof
    supersession::SupersessionProof{G}
    tally_board::TallyBoardProof{G}
end

proof_type(::Type{Tally{G}}) where G <: Group = TallyProof{G}

function extract_supersession(cast_openings::Vector{<:CastOpening})

    pseudonyms = [i.record.signature.pbkey for i in cast_openings]
    width = [length(trim(i.history)) for i in cast_openings]
    
    mask = extract_maximum_mask(pseudonyms, width)

    return mask
end

function compute_tracker_challenges(seed::Vector{UInt8}, Q::Vector{G}, challenge_max::Int, watermark_nbits::Int, hasher::HashSpec) where G <: Group

    prg = PRG(hasher, seed)

    nbits = ndigits(challenge_max, base=2) - 1
    offset = challenge_max - 2^nbits

    challenge_seeds = rand(prg, 0:BigInt(2)^nbits - 1, length(Q))
    challenges = [apply_watermark(ti, nbits, octet(Qi), hasher; num_positions = watermark_nbits) + offset for (ti, Qi) in zip(challenge_seeds, Q)]
    
    return challenges
end

function tracker_challenge_seed(Q::Vector{G}, R::Vector{G}, hasher::HashSpec) where G <: Group
    Q_vec = (octet(i) for i in Q)
    R_vec = (octet(i) for i in R)
    return hasher(UInt8[Iterators.flatten(R_vec) |> collect; Iterators.flatten(Q_vec) |> collect])
end

function compute_decoy_challenge(seed::Vector{UInt8}, decoy_votes::Vector{DecoyCommitment{G}}, hasher) where G <: Group

    Q′_vec = [i.Q for i in decoy_votes]
    R′_vec = [i.R for i in decoy_votes]

    decoy_seed = [seed; tracker_challenge_seed(Q′_vec, R′_vec, hasher)]

    return rand(PRG(hasher, decoy_seed), 2:order(G) - 1)
end

function tally(proposal::Proposal, cast_commitments::Vector{G}, cast_openings::Vector{CastOpening{G}}, hasher::HashSpec; skip_list = G[], mask = extract_supersession(cast_openings), dummy_votes::Vector{VoteOpening} = VoteOpening[]) where G <: Group

    (; challenge_max, watermark_nbits) = proposal

    sup_cast_openings = @view(cast_openings[mask])
    
    pseudonyms = (i.record.signature.pbkey for i in sup_cast_openings)
    skip_mask = BitVector(!(x in skip_list) for x in pseudonyms)

    decoy_vote_commitments = DecoyCommitment{G}[DecoyCommitment(i, proposal.basis) for i in dummy_votes]

    Q_vec = [i.record.commitment.Q for i in sup_cast_openings]
    R_vec = [i.record.commitment.R for i in sup_cast_openings]
    
    seed = tracker_challenge_seed(Q_vec, R_vec, hasher)
    tracker_challenges = compute_tracker_challenges(seed, Q_vec, challenge_max, watermark_nbits, hasher)
    decoy_challenge = compute_decoy_challenge(seed, decoy_vote_commitments, hasher)
    merged_tracker_challenges = append!(tracker_challenges[skip_mask], (decoy_challenge for i in eachindex(dummy_votes)))
    
    vote_openings = (i.opening for i in @view(sup_cast_openings[skip_mask])) 
    merged_vote_openings = Iterators.flatten((vote_openings, dummy_votes))
    trackers = (tracker(opening, chg, order(proposal.g)) for (chg, opening) in zip(merged_tracker_challenges, merged_vote_openings))

    tally = TallyRecord[TallyRecord(Ti, octet2int(hasher(int2octet(Ti))[1:8]), opening.selection) for (Ti, opening) in zip(trackers, merged_vote_openings)]

    vote_commitments = [i.record for i in sup_cast_openings]

    return Tally(proposal, cast_commitments, vote_commitments, skip_list, decoy_vote_commitments, decoy_challenge, tracker_challenges, tally)
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

function prove(proposition::Tally{G}, verifier::Verifier, cast_openings::Vector{CastOpening{G}}, 𝛙_shuffle::Vector{Int}; mask = extract_supersession(cast_openings), roprg = gen_roprg(), dummy_votes::Vector{VoteOpening} = VoteOpening[], validate_openings::Bool = true) where G <: Group

    hasher = verifier.prghash

    validate_openings && validate(cast_openings, proposition.proposal, verifier; mask)

    u = [sup_generator(i, hasher) for i in proposition.cast_records]
    ux = [i.ux for i in proposition.cast_records]
    pok = [i.pok for i in proposition.cast_records]

    history = [copy(trim(i.history)) for i in @view(cast_openings[mask])]

    ψ, α = reduce_representation(cast_openings, u, ux, history, hasher)
    β = [i.β for i in cast_openings]

    supersession_proposition = Supersession(proposition.cast_commitments, proposition.proposal.basis.h, u, ux, pok)

    supersession_proof = prove(supersession_proposition, verifier, ψ, β, α; roprg = gen_roprg(roprg(:supersession))) 
    skip_mask = BitVector(!(x.signature.pbkey in proposition.skip_list) for x in proposition.cast_records)

    tracker_challenges = proposition.tracker_challenges[skip_mask]
    decoy_challenge_vector = (proposition.decoy_challenge for i in eachindex(proposition.decoy_votes))
    merged_tracker_challenges = collect(BigInt, Iterators.flatten((tracker_challenges, decoy_challenge_vector)))
    
    vote_commitments = (i.commitment for i in @view(proposition.cast_records[skip_mask]))
    dummy_vote_commitments = (commitment(i, proposition.proposal.basis) for i in dummy_votes)
    merged_vote_commitments = collect(VoteCommitment{G}, Iterators.flatten((vote_commitments, dummy_vote_commitments)))
    
    tally_board_shuffle = TallyBoard(proposition.proposal.basis, merged_tracker_challenges, merged_vote_commitments, [VoteRecord(i.preimage_tracker, i.selection) for i in proposition.tally_board])

    vote_openings = (i.opening for i in @view(cast_openings[mask][skip_mask]))

    merged_vote_openings = collect(VoteOpening, Iterators.flatten((vote_openings, dummy_votes)))

    tally_board_proof = prove(tally_board_shuffle, verifier, merged_vote_openings, 𝛙_shuffle; roprg = gen_roprg(roprg(:shuffle)))    

    return TallyProof(supersession_proof, tally_board_proof)
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

function tally(proposal::Proposal, cast_commitments::Vector{G}, cast_openings::Vector{CastOpening{G}}, verifier::Verifier; skip_list = G[], decoy_votes::Vector{DecoyOpening} = extract_decoy_votes(cast_openings)) where G <: Group

    dummy_votes = [VoteOpening(vi, 2:order(G)-1) for vi in decoy_votes]

    hasher = verifier.prghash

    filter_mask = extract_supersession(cast_openings)
    commit_perm = sortperm(@view(cast_openings[filter_mask]); by = x -> x.record.signature.pbkey)
    
    mask = findall(filter_mask)[commit_perm]

    proposition = tally(proposal, cast_commitments, cast_openings, hasher; skip_list, mask, dummy_votes)

    𝛙 = sortperm(proposition.tally_board, by = x -> x.display_tracker) 
    permute!(proposition.tally_board, 𝛙)

    proof = prove(proposition, verifier, cast_openings, 𝛙; mask, dummy_votes) 

    return Simulator(proposition, proof, verifier)    
end

function verify(proposition::Tally{G}, proof::TallyProof{G}, verifier::Verifier) where G <: Group
    
    hasher = verifier.prghash

    (; h, g) = proposition.proposal.basis
    proposition.proposal.basis == GeneratorSetup(h, g) || return false
    
    (; challenge_max, watermark_nbits) = proposition.proposal
    (; cast_records, cast_commitments) = proposition

    for i in cast_records
        verify(i, proposition.proposal.g) || return false
    end

    u = [sup_generator(i, hasher) for i in cast_records]
    ux = [i.ux for i in cast_records]
    pok = [i.pok for i in cast_records]
    
    supersession_proposition = Supersession(cast_commitments, h, u, ux, pok)
    verify(supersession_proposition, proof.supersession, verifier) || return false

    # Verifying challenges
    Q_vec = [i.commitment.Q for i in cast_records]
    R_vec = [i.commitment.R for i in cast_records]
    seed = tracker_challenge_seed(Q_vec, R_vec, hasher)
    tracker_challenges = compute_tracker_challenges(seed, Q_vec, challenge_max, watermark_nbits, hasher)

    proposition.tracker_challenges == tracker_challenges || return false
    proposition.decoy_challenge == compute_decoy_challenge(seed, proposition.decoy_votes, hasher) || return false

    # Making revaal shuffle taking into account skip_list and decoy_votes
    skip_mask = BitVector(!(x.signature.pbkey in proposition.skip_list) for x in cast_records)

    tracker_challenges = tracker_challenges[skip_mask] 
    append!(tracker_challenges, Iterators.repeated(proposition.decoy_challenge, length(proposition.decoy_votes)))

    tally_board_commitments = [i.commitment for i in @view(cast_records[skip_mask])]
    append!(tally_board_commitments, (commitment(i, proposition.proposal.basis) for i in proposition.decoy_votes))

    tally_board_shuffle = TallyBoard(proposition.proposal.basis, tracker_challenges, tally_board_commitments, [VoteRecord(i.preimage_tracker, i.selection) for i in proposition.tally_board])

    verify(tally_board_shuffle, proof.tally_board, verifier) || return false

    return true
end
