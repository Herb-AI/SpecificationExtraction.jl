using Z3

"""
Converts a rulenode to a matchnode.
"""
function rulenode2matchnode(rn::RuleNode, variables::Dict{Int, Symbol})::AbstractMatchNode
    if rn.ind ∈ keys(variables)
        return MatchVar(variables[rn.ind])
    end
    return MatchNode(rn.ind, [rulenode2matchnode(c, variables) for c ∈ rn.children])
end

containsrule(rn::RuleNode, vars::Vector{Int}) = rn.ind ∈ vars || any(containsrule(c, vars) for c ∈ rn.children)


"""
Automatically discovers specifications in the provided grammar and
returns them in the form of constraints.
# Arguments
  - `grammar::Grammar`: The grammar from which specifications should be extracted
  - `candidate_depth::Int`: The maximum depth for the candidate programs for generating specifications.
  - `generator_depth::Int`: The maximum depth for the automatic generators for types in the grammar.
  - `num_programs_per_type::Int`: The number of programs that should be enumerated for each type in the specification discovery.
  - `num_variables_per_type::Int`: The maximum number of unique variables that can be used in a specification.
  """
function constraint_discovery(
    grammar::Grammar,
    candidate_depth::Int;
    generator_depth::Int=2,
    num_programs_per_type::Int=1000,
    num_variables_per_type::Int=1
)::Vector{PropagatorConstraint}

    types = keys(grammar.bytype)

    # Create data generators and variable specification for each data type
    generators::Dict{Symbol, Function} = Dict()
    for type ∈ types
        generators[type] = exhaustive_auto_generator(grammar, generator_depth, type)
    end

    g = deepcopy(grammar)

    # Remove any variables from the grammar
    variable_rules = findall(x -> isvariable(g, x), 1:length(g.rules))
    for idx ∈ variable_rules
        remove_rule!(g, idx)
    end

    # Add custom variables to the grammar
    variables_by_type = Dict{Symbol, Vector{Symbol}}()
    type_by_variable = Dict{Symbol, Symbol}()
    input_variables = []
    chars = Iterators.Stateful([Symbol(Char(x)) for x ∈ 97:122])
    for type ∈ types
        variables_by_type[type] = []
        for _ ∈ 1:num_variables_per_type
            x, _ = Iterators.peel(chars)
            add_rule!(g, :($type = $x))
            type_by_variable[x] = type
            push!(variables_by_type[type], x)
            i = length(g.rules)
            push!(input_variables, (var=x, type=type, index=i))
        end
    end

    # Extract specifications
    constraints = []
    for type ∈ types
        equivalence_classes = get_equivalences(g, num_programs_per_type, type, generators, type_by_variable, variables_by_type, max_depth=candidate_depth)

        # Remove all equivalence classes with length < 2
        equivalence_classes = filter!(x -> length(x) ≥ 2, equivalence_classes) 

        pruned_specs = equivalences2specs(g, equivalence_classes, Dict(var.index => var.var for var ∈ input_variables))

        # Obtain variables
        variables::Dict{Int, Symbol} = Dict()
        for v ∈ input_variables
            variables[v.index] = v.var
        end

        for specs ∈ pruned_specs
            append!(constraints, specs2constraints(filter(x -> containsrule(x.lhs, [v.index for v ∈ input_variables]), specs), variables))

            # TODO: Remove printing
            for equivalence ∈ specs
                if containsrule(equivalence.lhs, [v.index for v ∈ input_variables])
                    println("$(rulenode2expr(equivalence.lhs, g)) → $(rulenode2expr(equivalence.rhs, g))")
                end
            end
        end
    end
    return constraints
end