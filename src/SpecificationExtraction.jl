module SpecificationExtraction

using ..HerbGrammar
using ..HerbSearch
using ..HerbEvaluation
using ..HerbConstraints
using Base.Iterators
using ProgressBars

include("expr_util.jl")
include("specification_extractor.jl")
include("pruning.jl")
include("auto_generator.jl")
include("specification_procedure.jl")
include("constraint_conversion.jl")

export
    get_equivalences,
    exhaustive_auto_generator,
    constraint_discovery,
    spec2constraint

end # module
