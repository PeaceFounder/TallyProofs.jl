using SafeTestsets

@safetestset "Token Watermark" begin
    include("watermark.jl")
end

@safetestset "Supersession" begin
    include("supersession.jl")
end

@safetestset "Reveal Shuffle" begin
    include("reveal.jl")
end

@safetestset "Tally Proofs" begin
    include("tally.jl")
end
