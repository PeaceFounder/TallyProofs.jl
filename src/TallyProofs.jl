module TallyProofs

using CryptoPRG: HashSpec
using CryptoPRG.Verificatum: ROPRG, PRG
using Random: RandomDevice

function gen_roprg(ρ::AbstractVector{UInt8})

    rohash = HashSpec("sha256")
    prghash = HashSpec("sha256")
    roprg = ROPRG(ρ, rohash, prghash)

    return roprg
end

gen_roprg() = gen_roprg(rand(RandomDevice(), UInt8, 32))
gen_roprg(prg::PRG) = gen_roprg(prg.s)

include("watermark.jl")
include("kem.jl")

include("supersession.jl")
include("pedersen.jl")
include("shuffle.jl")

include("protocol.jl")
include("tally.jl")
include("calculator.jl")

include("extra.jl")
include("parser.jl")

export Proposal, CastOpening, tally, verify, count_votes, isconsistent, isbinding
export VotingCalculator, assemble_vote!, get_challenge, compute_tracker, extract_opening, CastReceipt, seed
export create_decoy_credential!, install_decoy_tracker! # coercion resistance toolbox

end
