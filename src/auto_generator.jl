
"""
Searches the grammar up to the maximum depth for possible values of a type.
Doesn't account for data that might be introduced via the input variables.
"""
function exhaustive_auto_generator(grammar, max_depth, type)::Function
    # Remove any variable rules
    g₁ = deepcopy(grammar)
    variable_rules = findall(x -> isvariable(g₁, x), 1:length(g₁.rules))
    for idx ∈ variable_rules
        remove_rule!(g₁, idx)
    end
    cleanup_removed_rules!(g₁)

    # Enumerate trees 
    possible_values_set = Set()
    symboltable::SymbolTable = SymbolTable(g₁)
    for tree ∈ get_dfs_enumerator(g₁, max_depth, type)
        output = interpret(symboltable, rulenode2expr(tree, g₁))
        push!(possible_values_set, output)
    end
    # TODO: Look at different ways of randomizing the values
    return () -> Base.rand(possible_values_set)
end