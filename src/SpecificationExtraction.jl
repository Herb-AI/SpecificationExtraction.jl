module SpecificationExtraction

using ..HerbGrammar
using ..HerbSearch
using ..HerbEvaluation
using ..HerbConstraints
using Base.Iterators
using ProgressBars

include("equivalence_constraints/specification.jl")
include("expr_util.jl")
include("equivalence_constraints/specification_extractor.jl")
include("equivalence_constraints/pruning.jl")
include("auto_generator.jl")
include("equivalence_constraints/specification_procedure.jl")
include("equivalence_constraints/constraint_conversion.jl")

include("specification_constraints/procedure.jl")

export
    Specification,
    EquivalenceSpecification,

    get_equivalences,
    exhaustive_auto_generator,
    constraint_discovery,
    specs2constraints

end # module
