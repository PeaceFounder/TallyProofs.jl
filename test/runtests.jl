using SafeTestsets

@safetestset "Supersession" begin
    include("supersession.jl")
end

@safetestset "Reveal Shuffle" begin
    include("reveal.jl")
end

@safetestset "Tally Proofs" begin
    include("tally.jl")
end
