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

include("supersession.jl")
include("pedersen.jl")
include("reveal.jl")

include("tally.jl")

include("parser.jl")

end
