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

struct ProposalInstance{G<:Group}
    proposal::Proposal{G}
    id::Vector{UInt8}
    π_w::SchnorrProof{G}
    pseudonym::G # computed from a generator
    supersession::SupersessionCalculator{G}
    tracker::TrackerOpening
    current_selection::Ref{BigInt} # Perhaps change to mutable struct
    trigger_challenge::Ref{Union{Int, Nothing}}
    override_mask::Vector{OverrideMask}
end

function ProposalInstance(proposal::Proposal{G}, id::Vector{UInt8}, verifier::Verifier, key::BigInt; history_width::Int = 5, roprg = gen_roprg()) where G <: Group
    
    (; g, hasher) = proposal
    (; h) = proposal.basis

    pseudonym = g^key

    π_w = prove(LogKnowledge(g, pseudonym), verifier, key; roprg = gen_roprg(roprg(:π_w)), suffix = b"ID") # 
    I = commitment(seed(π_w), id, hasher)

    u = sup_generator(pseudonym, I, hasher)
    sup_calc = SupersessionCalculator(h, u, verifier; history_width, roprg)
    
    w = π_w.s
    pk_BB = proposal.collector
    tracker_seed = pk_BB^(w * key)
    tracker = TrackerOpening(2:order(G)-1; roprg = gen_roprg(octet(tracker_seed)))                       

    return ProposalInstance(proposal, id, π_w, pseudonym, sup_calc, tracker, Ref{BigInt}(0), Ref{Union{Int, Nothing}}(nothing), OverrideMask[])
end

struct VotingCalculator{G <: Group} # More preciselly it would be VotingCalculatorInstance
    id::Vector{UInt8}
    g0::G # Base generator
    verifier::Verifier
    hasher::HashSpec # We shall also take it from the verifier
    key::BigInt
    pin::Int # Pin code for authetification
    decoys::Vector{DecoyCredential}
    instances::Vector{ProposalInstance{G}}
end

function Base.get!(voter::VotingCalculator{G}, proposal::Proposal{G}; history_width::Int = 5) where G <: Group

    N = findfirst(x -> x.proposal == proposal, voter.instances)

    if isnothing(N)
        instance = ProposalInstance(proposal, voter.id, voter.verifier, voter.key; history_width)
        push!(voter.instances, instance)
    else
        instance = voter.instances[N]
    end
    
    return instance
end

function Base.get(voter::VotingCalculator{G}, pid::Int) where G <: Group

    N = findfirst(x -> x.proposal.pid == pid, voter.instances)

    if !isnothing(N)
        return voter.instances[N]
    else
        error("Proposal instance with pid=$pid not found")
    end
end

function VotingCalculator(id::AbstractVector{UInt8}, g0::G, verifier::Verifier, pin::Int; roprg = gen_roprg(), history_width::Int = 5, key = rand(roprg(:key), 2:order(G) - 1)) where G <: Group

    id = convert(Vector{UInt8}, id) 
    hasher = verifier.prghash # the verifier could implement hasher method

    return VotingCalculator(id, g0, verifier, hasher, key |> BigInt, pin, DecoyCredential[], ProposalInstance{G}[])
end

# Installs override tracker for VotingCalculator for override_pin code. Leaves verification to verifier_pin
# Override mask is a vector and we simply need to find the last element from the list
# The pin at which it is authorized is where the tracker would be overriden
function install_decoy_tracker!(calc::VotingCalculator, pid::Int, tracker::BigInt, authorizing_pin::Int)

    if authorizing_pin == calc.pin || authorizing_pin in (i.pin for i in calc.decoys)
        instance = get(calc, pid)
        push!(instance.override_mask, OverrideMask(authorizing_pin, tracker))
    else
        error("Invalid pin code")
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

function compute_tracker(voter::VotingCalculator, pid::Int, challenge::Integer, pin::Int; reset_trigger_challenge::Bool = false)

    if pin == voter.pin || pin in (i.pin for i in voter.decoys)
        instance = get(voter, pid)
    else
        error("Invalid pin code")
    end

    (; hasher) = voter
    (Q, R) = commitment(instance.tracker, instance.proposal.basis)

    if (isnothing(instance.trigger_challenge[]) || reset_trigger_challenge) && verify_watermark(instance.proposal, Q, challenge, hasher)
        instance.trigger_challenge[] = challenge
    end

    # The computation is always present in spite if it is even to be superseeded by the mask
    if voter.pin == pin
        (; θ, λ) = instance.tracker
    else
        N = findlast(x -> x.pin == pin, voter.decoys)
        (; seed) = voter.decoys[N]
        θ, λ = compute_tracker_preimage(instance.proposal, seed)
    end

    t = tracker(θ, λ, challenge, order(instance.proposal.g))

    M = findlast(x -> x.pin == pin, instance.override_mask)

    if instance.trigger_challenge[] == challenge && !isnothing(M)
        return instance.override_mask[M].tracker 
    else
        return hasher(int2octet(t))[1:8] |> octet2int
    end
end

struct VoteEnvelope{G}
    proposal::Vector{UInt8}
    C::G
    opening::Encryption{CastOpening{G}, G}
    pkw::G # For main tracker oppening
    gz::G # For decoy tracker oppening (prevents leaks)
    R0::G # 
    signature::Union{Signature{G}, Nothing}
end

function VoteEnvelope(proposal::Vector{UInt8}, C::G, opening::Encryption{CastOpening{G}, G}, pkw::G, gz::G, R0::G, signer::Signer{G}) where G <: Group

    unsigned_vote = VoteEnvelope(proposal, C, opening, pkw, gz, R0, nothing)
    signature = sign(encode(Tree(unsigned_vote)), signer.g, signer.key)

    return VoteEnvelope(proposal, C, opening, pkw, gz, R0, signature)
end

function verify(vote::VoteEnvelope{G}, g::G) where G <: Group

    (; proposal, C, opening, pkw, gz, R0, signature) = vote
    unsigned_vote = VoteEnvelope(proposal, C, opening, pkw, gz, R0, nothing)

    return verify(encode(Tree(unsigned_vote)), g, vote.signature)
end

# This function may become redundant with compressed encryption
function isconsistent(opening::CastOpening{G}, vote::VoteEnvelope{G}, hasher::HashSpec, key::Integer) where G <: Group

    (; gz, pkw) = vote

    # decoy tracker
    (; θ, λ) = opening.decoy
    (θ, λ) == compute_tracker_preimage(gz^key, hasher) || return false

    # main tracker
    tracker_seed = pkw^key
    opening.opening.tracker == TrackerOpening(2:order(G)-1; roprg = gen_roprg(octet(tracker_seed))) || return false

    return true
end

function extract_opening(vote::VoteEnvelope{G}, proposal::Proposal{G}, verifier::Verifier, sk::Integer) where G <: Group

    # Here I can also obtain the relevant key 
    
    key = decap(vote.opening.encapsulation, sk) # The key used for encryption
    cast_opening = decrypt(vote.opening, sk, proposal.encrypt_spec; key)

    δ = rand(PRG(proposal.hasher, [octet(vote.R0); key]), 2:order(G)-1)
    (; R) = cast_opening.record.signature.proof
    (; R0) = vote
    (; g) = proposal
    @check R/R0 == g^δ "Witness of the signature not sufficiently randomized"

    @check isconsistent(cast_opening, vote, proposal.hasher, sk) "Leakage channel detected"
    @check isbinding(vote.C, cast_opening, proposal.basis.h) "Cast opening and cast commitment are not binding"
    @check isconsistent(cast_opening, proposal, verifier) "Cast opening is not consistent"

    return cast_opening
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

function assemble_vote!(voter::VotingCalculator{G}, proposal::Proposal, selection::Integer, chg::Integer, pin::Int; inherit_challenge=false, roprg = gen_roprg()) where G <: Group

    if pin == voter.pin || pin in (i.pin for i in voter.decoys)
        instance = get!(voter, proposal)
    else
        error("Invalid pin code")
    end

    if pin == voter.pin
        decoy_selection = 0
        encoded_selection = selection
        z = compute_decoy_tracker_seed(proposal, int2octet(voter.key))
    else
        decoy_selection = selection
        encoded_selection = instance.current_selection[]
        N = findlast(i -> i.pin == pin, voter.decoys)
        z = compute_decoy_tracker_seed(proposal, voter.decoys[N].seed)
    end

    (; collector, hasher, g) = proposal
    decoy_vote = DecoyOpening(hasher, decoy_selection, collector ^ z)
    gz = g^z # generator element used by buletin board to derive decoy seed

    vote_opening = VoteOpening(instance.tracker, encoded_selection, 2:order(G)-1; roprg)
    vote_commitment = commitment(vote_opening, proposal.basis)

    (; π_w, id) = instance
    (; hasher) = proposal
    I = commitment(seed(π_w), id, hasher)

    C, A, sup_opening = TallyProofs.recommit!(instance.supersession, chg; roprg = gen_roprg(roprg(:supersession))) 
    (; β, history, ux, pok) = sup_opening

    k_BB = encap(proposal.g, proposal.collector)

    r0 = rand(roprg(:r0), 2:order(G) - 1)
    R0 = g^r0
    δ = rand(PRG(hasher, [octet(R0); decap(k_BB)]), 2:order(G)-1)

    signer = Signer(proposal.g, voter.key)
    proposal_hash = hasher(encode(Tree(proposal)))
    cast_record = CastRecord(proposal_hash, ux, vote_commitment, I, pok, signer; r = r0 + δ)

    cast_opening = CastOpening(β, history, cast_record, vote_opening, decoy_vote)

    cast_opening_enc = encrypt(cast_opening, k_BB, proposal.encrypt_spec)

    instance.current_selection[] = encoded_selection
        
    pkw = instance.pseudonym ^ π_w.s
    vote = VoteEnvelope(proposal_hash, C, cast_opening_enc, pkw, gz, R0, signer)

    vote_context = VoteContext(vote, A, id, π_w)

    return vote_context
end
