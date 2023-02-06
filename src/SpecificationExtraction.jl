module SpecificationExtraction

using ..Grammars
using ..Search
using ..Evaluation

include("specification_extractor.jl")
include("auto_generator.jl")

export
    extract_specifications,
    exhaustive_auto_generator

end # module
