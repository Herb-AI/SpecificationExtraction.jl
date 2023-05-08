"""
Converts a equality specification with lefthandside `lhs` and righthandside `rhs` 
to a constraint.
The `variables` dict has an entry for each variable with the key being the rulenode 
index of the variable and as value the associated variable.
This is necessary for converting RuleNodes to MatchVars.
"""
function specs2constraints(equivalences::Vector{EquivalenceSpecification}, variables::Dict{Int, Symbol})::Vector{PropagatorConstraint}
    specs = deepcopy(equivalences)
    constraints = PropagatorConstraint[]

    create_forbidden_constraints!(specs, constraints, variables)
    create_ordered_constraints!(specs, constraints, variables)

    generalize_ordered_constraints(constraints)

    return constraints
end

function create_forbidden_constraints!(
    specifications::Vector{EquivalenceSpecification}, 
    constraints::Vector{PropagatorConstraint}, 
    variables::Dict{Int, Symbol}
)::Nothing
    deleted_specifications = Int[]
    for (i, equivalence) ∈ enumerate(specifications)
        # See if we can match the rhs of the expression using the left-hand side.
        rewrite_function₁ = varname -> Symbol(string(varname) * "₁")
        rewrite_function₂ = varname -> Symbol(string(varname) * "₂")

        # Create match nodes
        mn₁ = rulenode2matchnode(equivalence.lhs, variables)
        mn₂ = rulenode2matchnode(equivalence.rhs, variables)

        # Create rewritten match nodes where variables are renamed to prevent identically-named variables in either side.
        rmn₁ = copy_and_rewrite_variable_names(mn₁, rewrite_function₁)
        rmn₂ = copy_and_rewrite_variable_names(mn₂, rewrite_function₂)

        # Create list of all new variables
        rewritten_variables = append!([rewrite_function₁(v) for v ∈ values(variables)], [rewrite_function₂(v) for v ∈ values(variables)])

        # Detect if there exists a rulenode that matches both patterns
        circular = detect_circularity(rmn₁, rmn₂, Dict{Symbol, MatchNode}(), Dict{Symbol, Set{Symbol}}(s => Set{Symbol}([s]) for s ∈ rewritten_variables))
        if !circular
            push!(constraints, Forbidden(mn₁))
            push!(deleted_specifications, i)
        end
    end

    # Remove all specifications that have been converted to constraints.
    for i ∈ reverse!(deleted_specifications)
        deleteat!(specifications, i)
    end
end

function create_ordered_constraints!(
    specifications::Vector{EquivalenceSpecification}, 
    constraints::Vector{PropagatorConstraint},
    variables::Dict{Int, Symbol}
)::Nothing
    # TODO: Check if lhs and rhs are equal apart from variable renaming
    deleted_specifications = Int[]
    for (i, equivalence) ∈ enumerate(specifications)
        constraint_variables = _get_variables_from_rulenode(equivalence.lhs, variables)

        if length(constraint_variables) ≥ 2
            c = Ordered(rulenode2matchnode(equivalence.lhs, variables), [variables[k] for k ∈ constraint_variables])
            push!(constraints, c)
            push!(deleted_specifications, i)
        end
    end

    # Remove all specifications that have been converted to constraints.
    for i ∈ reverse!(deleted_specifications)
        deleteat!(specifications, i)
    end
end


function generalize_ordered_constraints(constraints::Vector{PropagatorConstraint})   
    ordered_constraints = filter(x -> x isa Ordered, constraints)
    filter!(x -> !(x isa Ordered), constraints)
    orders = Dict{AbstractMatchNode, Set{Symbol}}()
    for c ∈ ordered_constraints
        if c.tree ∉ keys(orders)
            orders[c.tree] = Set(c.order)
        else
            union!(orders[c.tree], Set(c.order))
        end
    end
    for (pattern, order) ∈ orders
        push!(constraints, Ordered(pattern, collect(order)))
    end
end

function copy_and_rewrite_variable_names(mn::MatchNode, rewrite::Function)
    return MatchNode(mn.rule_ind, [copy_and_rewrite_variable_names(c, rewrite) for c ∈ mn.children])
end

function copy_and_rewrite_variable_names(mv::MatchVar, rewrite::Function)
    return MatchVar(rewrite(mv.var_name))
end

"""
Detects whether there is a rulenode instance that could be removed by both lhs and rhs.

`equalities` should be instantiated to a dict with for each variable that 
    might occur the singleton set of the variable symbol.
"""
function detect_circularity(
    lhs::MatchNode, 
    rhs::MatchNode, 
    vars::Dict{Symbol, MatchNode},
    equalities::Dict{Symbol, Set{Symbol}}
)::Bool
    if lhs.rule_ind ≠ rhs.rule_ind || length(lhs.children) ≠ length(rhs.children)
        return false
    end
    return all(detect_circularity(c₁, c₂, vars, equalities) for (c₁, c₂) ∈ zip(lhs.children, rhs.children))
end

function detect_circularity(
    lhs::MatchVar, 
    rhs::MatchNode, 
    vars::Dict{Symbol, MatchNode},
    equalities::Dict{Symbol, Set{Symbol}}
)::Bool
    if contains_var(rhs)
        return false
    elseif lhs.var_name ∈ keys(vars)
        return rhs ≠ vars[lhs.var_name]
    elseif lhs.var_name ∈ keys(equalities)
        for equal_var ∈ equalities[lhs.var_name]
            if equal_var ∈ keys(vars)
                vars[equal_var] ≠ rhs && return false
            end
        end
    else
        vars[lhs.var_name] = rhs
    end
    return true
end

function detect_circularity(
    lhs::MatchNode, 
    rhs::MatchVar, 
    vars::Dict{Symbol, MatchNode},
    equalities::Dict{Symbol, Set{Symbol}}
)::Bool
    if contains_var(lhs)
        return false
    elseif rhs.var_name ∈ keys(vars)
        return lhs ≠ vars[rhs.var_name]
    elseif rhs.var_name ∈ keys(equalities)
        for equal_var ∈ equalities[rhs.var_name]
            if equal_var ∈ keys(vars)
                vars[equal_var] ≠ lhs && return false
            end
        end   
    else
        vars[rhs.var_name] = lhs
    end
    return true
end

function detect_circularity(
    lhs::MatchVar, 
    rhs::MatchVar, 
    vars::Dict{Symbol, MatchNode},
    equalities::Dict{Symbol, Set{Symbol}}
)::Bool
    assignment = nothing
    for v ∈ union(equalities[lhs.var_name], equalities[rhs.var_name])
        if v ∈ keys(vars)
            if assignment ≡ nothing
                assignment = vars[v]
            else
                # Check conflict with assignment
                assignment ≠ vars[v] && return false
            end
        end
    end

    for k ∈ equalities[lhs.var_name]
        union!(equalities[k], equalities[rhs.var_name])
    end
    for k ∈ equalities[rhs.var_name]
        union!(equalities[k], equalities[lhs.var_name])
    end
    return true
end