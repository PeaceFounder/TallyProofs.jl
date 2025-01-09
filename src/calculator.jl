using CryptoGroups: Group, order, octet
using CryptoGroups.Utils: int2octet!, octet2int, @check
using CryptoPRG: HashSpec
using CryptoPRG.Verificatum: PRG
using SigmaProofs.LogProofs: SchnorrProof, LogKnowledge
using SigmaProofs.Parser: Tree, encode
using SigmaProofs.Verificatum: generator_basis, GeneratorBasis
import SigmaProofs: prove, verify

# Hash commitment
commitment(blind::Vector{UInt8}, value::Vector{UInt8}, hasher::HashSpec) = hasher([blind; value])

struct OverrideMask
    pin::Int
    tracker::BigInt # nothing is when not overriden
end

struct DecoyCredential
    pin::Int
    seed::Vector{UInt8} # in a sense it is also a credential
end

function map2generator(g::G, hasher::HashSpec) where G <: Group

    prg = PRG(hasher, octet(g))
    u = GeneratorBasis.generator_basis(prg, G) 

    return u
end

struct VotingCalculator{G <: Group} # More preciselly it would be VotingCalculatorInstance
    id::Vector{UInt8}
    π_w::SchnorrProof{G}
    #w::G
    #π_w::ChaumPedersenProof{G}

    proposal::Proposal{G}

    verifier::Verifier
    hasher::HashSpec # We shall also take it from the verifier

    supersession::SupersessionCalculator{G}

    pseudonym::G # computed from a generator
    key::BigInt

    # We shall keep the tracker constant for simplicity
    pin::Int # Pin code for authetification
    tracker::TrackerOpening
    π_t::SchnorrProof{G} # The proof that tracker have been computed incorporating knowledge of secret key  

    current_selection::Ref{BigInt}
    trigger_token::Ref{Union{Int, Nothing}}
    
    override_mask::Vector{OverrideMask}
    decoys::Vector{DecoyCredential}
end

function VotingCalculator(id::AbstractVector{UInt8}, proposal::Proposal{G}, verifier::Verifier, pin::Int; roprg = gen_roprg(), history_width::Int = 5, key = rand(roprg(:key), 2:order(G) - 1)) where G <: Group

    id = convert(Vector{UInt8}, id) 
    hasher = verifier.prghash # the verifier could implement hasher method

    (; g) = proposal
    (; h) = proposal.basis

    pseudonym = g^key

    π_w = prove(LogKnowledge(g, pseudonym), verifier, key; roprg = gen_roprg(roprg(:π_w)), suffix = b"ID") # 
    I = commitment(seed(π_w), id, hasher)

    u = sup_generator(pseudonym, I, hasher)
    sup_calc = SupersessionCalculator(h, u, verifier; history_width, roprg)

    π_t = prove(LogKnowledge(g, pseudonym), verifier, key; roprg = gen_roprg(roprg(:π_t)), suffix = b"TRACKER")
    tracker = TrackerOpening(2:order(G)-1; roprg = gen_roprg(seed(π_t)))

    return VotingCalculator(id, π_w, proposal, verifier, hasher, sup_calc, pseudonym, key |> BigInt, pin, tracker, π_t, Ref{BigInt}(0), Ref{Union{Int, Nothing}}(nothing), OverrideMask[], DecoyCredential[])
end

# Installs override tracker for VotingCalculator for override_pin code. Leaves verification to verifier_pin
# Override mask is a vector and we simply need to find the last element from the list
# The pin at which it is authorized is where the tracker would be overriden
function install_decoy_tracker!(calc::VotingCalculator, tracker::BigInt, authorizing_pin::Int)

    if authorizing_pin == calc.pin || authorizing_pin in (i.pin for i in calc.decoys)
        push!(calc.override_mask, OverrideMask(authorizing_pin, tracker))
    else
        error("Incorrect pin code")
    end
end

# in case it fails it is possible to repeat the process
function create_decoy_credential!(calc::VotingCalculator, fake_pin::Int, authorizing_pin::Int; roprg = gen_roprg())
    
    if authorizing_pin == calc.pin || authorizing_pin in (i.pin for i in decoys)

        seed = roprg(:seed)[1:32]
        credential = DecoyCredential(fake_pin, seed)

        push!(calc.decoys, credential)

        return seed
    else
        error("Incorrect pin code")
    end
end

function compute_tracker(voter::VotingCalculator, token::Integer, pin::Int; reset_trigger_token::Bool = false)

    (; hasher) = voter
    (Q, R) = commitment(voter.tracker, voter.proposal.basis)

    if (isnothing(voter.trigger_token[]) || reset_trigger_token) && verify_watermark(voter.proposal, Q, token, hasher)
        voter.trigger_token[] = token
    end

    # The computation is always present in spite if it is even to be superseeded by the mask
    if voter.pin == pin
        (; θ, λ) = voter.tracker
    else

        N = findlast(x -> x.pin == pin, voter.decoys)

        if isnothing(N)
            error("Incoreect PIN code")
        else
            (; seed) = voter.decoys[N]
            θ, λ = compute_tracker_preimage(voter.proposal, seed)
        end

    end

    t = tracker(θ, λ, token, order(voter.proposal.g))

    M = findlast(x -> x.pin == pin, voter.override_mask)

    if voter.trigger_token[] == token && !isnothing(M)
        return voter.override_mask[M].tracker 
    else
        return hasher(int2octet(t))[1:8] |> octet2int
    end
end

struct VoteEnvelope{G}
    proposal::Vector{UInt8}
    C::G
    opening::Encryption{CastOpening{G}, G}
    signature::Union{Signature{G}, Nothing}
end

function VoteEnvelope(proposal::Vector{UInt8}, C::G, opening::Encryption{CastOpening{G}, G}, signer::Signer{G}) where G <: Group

    unsigned_vote = VoteEnvelope(proposal, C, opening, nothing)
    signature = sign(encode(Tree(unsigned_vote)), signer.g, signer.key)

    return VoteEnvelope(proposal, C, opening, signature)
end

function verify(vote::VoteEnvelope{G}, g::G) where G <: Group

    (; proposal, C, opening, signature) = vote
    unsigned_vote = VoteEnvelope(proposal, C, opening, nothing)

    return verify(encode(Tree(unsigned_vote)), g, vote.signature)
end

# auxilary data that enables delivery device to be sure that identity commitment will appear on the buletin board
struct VoteContext{G} 
    vote::VoteEnvelope{G}
    A::G 
    id::Vector{UInt8}
    π_w::SchnorrProof{G}
end

function sup_generator(envelope::VoteContext, hasher::HashSpec)

    (; id, π_w) = envelope
    (; pbkey) = envelope.vote.signature

    I = commitment(seed(π_w), id, hasher)

    return sup_generator(pbkey, I, hasher)
end

# hasher could be derived from the verifier
function isconsistent(envelope::VoteContext, τ::Integer, g::G, hasher::HashSpec, verifier::Verifier) where G <: Group

    (; C) = envelope.vote
    (; pbkey) = envelope.vote.signature
    (; A, id, π_w) = envelope

    verify(LogKnowledge(g, pbkey), π_w, verifier; suffix = b"ID") || return false

    u = sup_generator(envelope, hasher)
    
    check_challenge(C, A, u, τ, hasher) || return false

    verify(envelope.vote, g) || return false

    return true
end

function assemble_vote!(voter::VotingCalculator{G}, selection::Integer, chg::Integer, pin::Int; inherit_challenge=false, roprg = gen_roprg()) where G <: Group

    if pin == voter.pin
        
        encoded_selection = selection
        coerced_vote = DecoyOpening()

    elseif pin in (i.pin for i in voter.decoys)

        encoded_selection = voter.current_selection[]
        N = findlast(i -> i.pin == pin, voter.decoys)
        coerced_vote = DecoyOpening(voter.proposal, selection, voter.decoys[N].seed)

    else

        error("Invalid pin code")

    end
        
    C, A, sup_opening = TallyProofs.recommit!(voter.supersession, chg; roprg = gen_roprg(roprg(:supersession))) 
    (; β, history, ux, pok) = sup_opening

    vote_opening = VoteOpening(voter.tracker, encoded_selection, 2:order(G)-1; roprg)
    vote_commitment = commitment(vote_opening, voter.proposal.basis)

    signer = Signer(voter.proposal.g, voter.key)

    proposal_hash = voter.hasher(encode(Tree(voter.proposal)))

    (; π_w, id) = voter
    (; hasher) = voter.proposal
    I = commitment(seed(π_w), id, hasher)

    signed_vote_commitment = CastRecord(proposal_hash, ux, vote_commitment, I, pok, signer)

    cast_opening = CastOpening(β, history, signed_vote_commitment, vote_opening, coerced_vote, voter.π_t)

    cast_opening_enc = encrypt(cast_opening, voter.proposal.g, voter.proposal.collector, voter.proposal.encrypt_spec)

    voter.current_selection[] = encoded_selection

    vote = VoteEnvelope(proposal_hash, C, cast_opening_enc, signer)

    vote_envelope = VoteContext(vote, A, id, π_w)

    return vote_envelope
end
