"""
Replaces variables in a rulenode with the replacements provided in the dictionary.
Returns a new rulenode.
"""
function _replace_variables(node::RuleNode, replacements::Dict)::RuleNode
    if node.ind ∈ replacements.keys
        return deepcopy(get(replacements, node.ind, node))
    end
    return RuleNode(node.ind, node._val, map(x -> _replace_variables(x, replacements), node.children))
end


"""
Tries to match rulenodes n₁ and n₂. 
Node n₂ can have its variables filled in.
Returns a dictionary with variable assignments if match is successful.
A variable is represented by the index of its rulenode.
Returns nothing if the match is unsuccessful.
"""
function _match_expr(n₁::RuleNode, n₂::RuleNode, vars_ids::Vector{Int})::Union{Dict{Int, RuleNode}, Nothing}
    if n₂.ind ∈ vars_ids
        return Dict(n₂.ind => n₁)
    elseif n₁.ind ≠ n₂.ind || length(n₁.children) ≠ length(n₂.children)
        return nothing
    else
        vars = Dict()
        for varsᵢ ∈ map(ab -> _match_expr(ab[1], ab[2], vars_ids), zip(n₁.children, n₂.children)) 
            if varsᵢ ≡ nothing 
                return nothing
            end
            # Check if another argument already assigned the same variables
            for (k, v) ∈ varsᵢ
                if k ∈ keys(vars) && v ≠ vars[k]
                    return nothing
                end
                vars[k] = v
            end
        end
        return vars
    end
end

"""
Tries to rewrite rulenode `n` by replacing (sub)expression `old` with `new`.
Returns the rewritten rulenode.
"""
function _rewrite(node::RuleNode, old::RuleNode, new::RuleNode, var_ids::Vector{Int})::RuleNode
    if node == old
        return new
    end
    variables = _match_expr(node, old, var_ids)
    if variables ≠ nothing
        return _replace_variables(new, variables)
    end
    return RuleNode(node.ind, node._val, map(x -> _rewrite(x, old, new, var_ids), node.children))
end

"""
Get all variables in the given expression
"""
_get_variables(s::Symbol) = Set([s])
_get_variables(e::Expr) = union(Set(), _get_variables.(e.args[2:end])...)
_get_variables(::Any) = Set()


"""
Checks if variables usage is ordered. 
This can be used to detect duplicates by variable renaming.
"""
function _check_variable_renaming(s::Symbol, variables_by_type, type_by_variable, maximum_index) 
    type = type_by_variable[s]
    index = findfirst(isequal(s), variables_by_type[type])
    m = deepcopy(maximum_index)
    m[type] = max(m[type], index)
    (index ≤ maximum_index[type] + 1, m)
end

function _check_variable_renaming(expr::Expr, variables_by_type, type_by_variable, maximum_index)
    m = deepcopy(maximum_index)
    for arg ∈ expr.args[2:end]
        (valid, m) = _check_variable_renaming(arg, variables_by_type, type_by_variable, m)
        if !valid
            return (false, m)
        end
    end
    return (true, m)
end

_check_variable_renaming(::Any, _, _, maximum_index) = (true, maximum_index)

"""
Given the order of variables in variables_by_type, e.g. [:a, :b, :c]
this function returns false if a variable is used without any of the previous variables in the order being used.
For example, `a + c` would be return false, since `c` is used while `b` is not used.
It does not matter if the variable usage itself is unordered, e.g. `b + a` is still a valid program.
"""
function _check_variable_usage(x, type_by_variable, variables_by_type)::Bool
    vars = _get_variables(x)
    for var ∈ vars
        type = type_by_variable[var]
        for varᵢ ∈ variables_by_type[type][1:findfirst(isequal(var), variables_by_type[type])]
            if varᵢ ∉ vars
                return false
            end
        end
    end
    return true
end



"""
Returns a tuple with two integers. 
    1. The number of nodes in the rulenode.
    2. The number of non-variable terminals in the rulenode.
This tuple signifies the generality of rulenodes for specification generation and can be used for sorting.
"""
function _expr_size_vars(node::RuleNode, g::Grammar)::Tuple{Int, Int}
    if isvariable(g, node)
        return (1, 0)
    elseif isterminal(g, node)
        return (1, 1)
    end
    child_size_vars = collect(zip(collect(map(x -> _expr_size_vars(x, g), node.children))...))
    return (sum(child_size_vars[1]) + 1, 
        sum(child_size_vars[2])
    )
end

"""
Returns the set of variable indices that are used in the rulenode tree
"""
function _get_variables_from_rulenode(rn::RuleNode, variables::Dict{Int, Symbol})::Set{Int}
    if rn.ind ∈ keys(variables)
        return Set{Int}([rn.ind])
    else
        return union(Set{Int}(), (_get_variables_from_rulenode(x, variables) for x ∈ rn.children)...)
    end
end
