module SpecificationExtraction

using HerbCore
using HerbGrammar
using HerbSearch
using HerbInterpret
using HerbConstraints

using Base.Iterators
using ProgressBars
using PyCall

sympy = pyimport("sympy")

include("equivalence_constraints/specification.jl")
include("expr_util.jl")
include("equivalence_constraints/specification_extractor.jl")
include("equivalence_constraints/pruning.jl")
include("auto_generator.jl")
include("equivalence_constraints/specification_procedure.jl")
include("equivalence_constraints/constraint_conversion.jl")

include("specification_constraints/specification_generation.jl")
include("specification_constraints/procedure.jl")

export
    Specification,
    EquivalenceSpecification,

    SpecificationSymbol,
    SpecificationVariable,
    SpecificationOperator,
    SpecificationLiteral,

    specification_discovery,
    get_equivalences,
    exhaustive_auto_generator,
    constraint_discovery,
    specs2constraints

end # module
