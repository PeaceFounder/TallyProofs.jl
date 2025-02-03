using SafeTestsets

function extract_examples(markdown_file)
    # Read the markdown file
    content = read(markdown_file, String)
    
    # Pattern to match both simple ```julia and ```julia{attributes}
    # Capture the attributes part if it exists
    pattern = r"```julia({[^}]*})?\n(.*?)\n```"s
    
    # Extract all code blocks
    code_blocks = collect(eachmatch(pattern, content))
    
    # Run each code block
    for block in code_blocks
        attr_string = block.captures[1]  # Get attributes string (might be nothing)
        code = block.captures[2]         # Get the actual code

        if attr_string == "{skip=true}"
            continue
        end

        # Clean up the code - remove any BOM and normalize line endings
        code = replace(code, "\r\n" => "\n")  # Normalize Windows line endings
        code = strip(code)  # Remove leading/trailing whitespace
        
        try
            expr = Meta.parseall(code)
            eval(expr)
        catch e
            println("\nError executing code block:")
            println("Attributes: ", attr_string)
            println("-" ^ 40)
            println(code)
            println("-" ^ 40)             
            rethrow(e)
        end
    end
end


@safetestset "Watermarks" begin
    include("watermark.jl")
end

@safetestset "Supersession" begin
    include("supersession.jl")
end

@safetestset "TallyBoard" begin
    include("reveal.jl")
end

@safetestset "Tally" begin
    include("tally.jl")
end

@safetestset "Example" begin
    include("example.jl")
end

@safetestset "README" begin
    Main.extract_examples(joinpath(dirname(@__DIR__), "README.md"))
end
