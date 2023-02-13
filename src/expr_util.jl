"""
Replaces variables in an expression with the replacements provided in the dictionary.
Returns a new expression.
"""
function _replace_variables(e::Expr, replacements::Dict)
    return Expr(e.head, e.args[1], map(x -> _replace_variables(x, replacements), e.args[2:end])...)
end
_replace_variables(e::Symbol, replacements::Dict) = deepcopy(get(replacements, e, e))
_replace_variables(e::Any, _) = deepcopy(e)


"""
Tries to match expression e₁ and e₂. 
Expression e₂ can have it's variables filled in.
Returns a dictionary with variable assignments if match is successful.
Returns nothing if the match is unsuccessful.
"""
_match_expr(e₁::Symbol, e₂::Symbol) = Dict(e₂ => e₁)
_match_expr(e₁, e₂::Symbol) = Dict(e₂ => e₁)
_match_expr(::Symbol, _) = nothing
_match_expr(e₁, e₂) = e₁ == e₂ ? Dict() : nothing

function _match_expr(e₁::Expr, e₂::Expr)
    if e₁.head ≠ e₂.head || e₁.args[1] ≠ e₂.args[1] || length(e₁.args) ≠ length(e₂.args)
        return nothing
    else
        vars = Dict()
        for varsᵢ ∈ map(ab -> _match_expr(ab[1], ab[2]), zip(e₁.args[2:end], e₂.args[2:end])) 
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
Tries to rewrite expression `e` by replacing (sub)expression `old` with `new`.
Returns the rewritten expression.
"""
_rewrite(e::Symbol, old::Symbol, new::Any) = e == old ? new : deepcopy(e)
_rewrite(e::Any, ::Any, ::Any) = deepcopy(e)

function _rewrite(e::Expr, old::Expr, new::Any)
    variables = _match_expr(e, old)
    if variables ≠ nothing
        return _replace_variables(new, variables)
    end
    return Expr(:call, e.args[1], map(a -> _rewrite(a, old, new), e.args[2:end])...)
end

"""
Get all variables in the given expression
"""
_get_variables(s::Symbol) = Set([s])
_get_variables(e::Expr) = union(_get_variables.(e.args[2:end])...)
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