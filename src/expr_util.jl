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
Node n₂ can have it's variables filled in.
Returns a dictionary with variable assignments if match is successful.
A variable is represented by the index of it's rulenode.
Returns nothing if the match is unsuccessful.
"""
function _match_expr(g::ContextFreeGrammar, n₁::RuleNode, n₂::RuleNode)::Union{Dict{Int, RuleNode}, Nothing}
    if isvariable(g, n₂)
        return Dict(n₂.ind => n₁)
    elseif n₁.ind ≠ n₂.ind || length(n₁.children) ≠ length(n₂.children)
        return nothing
    else
        vars = Dict()
        for varsᵢ ∈ map(ab -> _match_expr(g, ab[1], ab[2]), zip(n₁.children, n₂.children)) 
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
function _rewrite(g::ContextFreeGrammar, node::RuleNode, old::RuleNode, new::RuleNode)::RuleNode
    if node == old
        return new
    end
    variables = _match_expr(g, node, old)
    if variables ≠ nothing
        return _replace_variables(new, variables)
    end
    return RuleNode(node.ind, node._val, map(x -> _rewrite(g, x, old, new), node.children))
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
Returns a tuple with three integers. 

    1. The maximum depth of the rulenode.
    2. The number of nodes in the rulenode.
    3. The number of non-variable terminals in the rulenode.
This tuple signifies the generality of rulenodes for specification generation and can be used for sorting.
"""
function _expr_depth_size_vars(node::RuleNode, g::Grammar)::Tuple{Int, Int, Int}
    if isvariable(g, node)
        return (0, 1, 0)
    elseif isterminal(g, node)
        return (0, 1, 1)
    end
    child_depth_size_vars = collect(zip(collect(map(x -> _expr_depth_size_vars(x, g), node.children))...))
    return (maximum(child_depth_size_vars[1], init=0) + 1, 
        sum(child_depth_size_vars[2]) + 1, 
        sum(child_depth_size_vars[3])
    )
end