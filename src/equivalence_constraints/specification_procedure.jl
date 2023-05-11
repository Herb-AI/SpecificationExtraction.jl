"""
Converts a rulenode to a matchnode.
"""
function rulenode2matchnode(rn::RuleNode, variables::Dict{Int, Symbol})::AbstractMatchNode
    if rn.ind ∈ keys(variables)
        return MatchVar(variables[rn.ind])
    end
    return MatchNode(rn.ind, [rulenode2matchnode(c, variables) for c ∈ rn.children])
end

"""
Returns `true` if the rulenode contains any of the rules included in `rules`
# Arguments
  - `rn::RuleNode`:         The RuleNode tree to check
  - `rules::Vector{Int}`:   A list of rule indices to check fosr
"""
containsrule(rn::RuleNode, rules::Vector{Int}) = rn.ind ∈ rules || any(containsrule(c, rules) for c ∈ rn.children)


"""
Automatically discovers specifications in the provided grammar and
returns them in the form of constraints.
# Arguments
  - `grammar::Grammar`:                 The grammar from which specifications should be extracted.
  - `candidate_max_size::Int`:          The maximum number of nodes in the candidate programs for 
                                        generating specifications.
  - `candidate_max_depth::Int`:         The maximum depth for the candidate programs for generating 
                                        specifications. Set to `typemax(Int)` by default.
  - `generators::Dict{Symbol, Function}`:A set of generators that have already been defined by the
                                        user. If generators for certain types are missing, a new
                                        generator is automatically created for this type.  
  - `max_generator_ast_size`:           The maximum number of nodes for the automatic generators 
                                        for types in the grammar. Set to 5 by default.
  - `num_programs_per_type::Int`:       The number of programs that should be enumerated for each 
                                        type in the specification discovery. Set to 1000 by default.
  - `num_variables_per_type::Int`:      The maximum number of unique variables that can be used in 
                                        a specification. Set to 2 by default.
  - `only_general_constraints::Bool`:   Determines whether only general constraints (that contain) 
                                        variables should be generated or also specific constraints
                                        that do not contain variables.
  """
function constraint_discovery(
    grammar::Grammar,
    candidate_max_size::Int;
    candidate_max_depth::Int=typemax(Int),
    generators::Dict{Symbol, Function}=Dict{Symbol, Function}(),
    max_generator_ast_size::Int=5,
    num_programs_per_type::Int=1000,
    num_variables_per_type::Int=2,
    only_general_constraints::Bool=true
)::Vector{PropagatorConstraint}

    types = keys(grammar.bytype)

    # Create data missing generators
    for type ∈ types
        if type ∉ keys(generators)
            generators[type] = exhaustive_auto_generator(grammar, type, max_generator_ast_size)
        end
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
        equivalence_classes = get_equivalences(
            g, 
            num_programs_per_type, 
            type, 
            generators, 
            type_by_variable, 
            variables_by_type, 
            max_depth=candidate_max_depth,
            max_size=candidate_max_size
        )
        
        # Remove all equivalence classes with length < 2
        equivalence_classes = filter!(x -> length(x) ≥ 2, equivalence_classes) 

        pruned_specs = equivalences2specs(g, equivalence_classes, Dict(var.index => var.var for var ∈ input_variables))

        # Obtain variables
        variables::Dict{Int, Symbol} = Dict()
        for v ∈ input_variables
            variables[v.index] = v.var
        end

        if only_general_constraints
            for specs ∈ pruned_specs
                append!(constraints, specs2constraints(filter(x -> containsrule(x.lhs, [v.index for v ∈ input_variables]), specs), variables))
                # TODO: Remove printing
                for equivalence ∈ specs
                    if containsrule(equivalence.lhs, [v.index for v ∈ input_variables])
                        println("$(rulenode2expr(equivalence.lhs, g)) → $(rulenode2expr(equivalence.rhs, g))")
                    end
                end
            end
        else
            for specs ∈ pruned_specs
                append!(constraints, specs2constraints(specs, variables))
                # TODO: Remove printing
                for equivalence ∈ specs
                    println("$(rulenode2expr(equivalence.lhs, g)) → $(rulenode2expr(equivalence.rhs, g))")
                end
            end
        end
    end
    return constraints
end

