
"""
Searches the grammar up to the maximum depth for possible values of a type.
Doesn't account for data that might be introduced via the input variables.
"""
function exhaustive_auto_generator(grammar, max_depth, type)::Function
    # Remove any variable rules
    g₁ = deepcopy(grammar)
    variable_rules = findall(x -> x isa Symbol && x ∉ grammar.types, g₁.rules)
    for idx ∈ variable_rules
        Grammars.remove_rule!(g₁, idx)
    end
    @show g₁
    Grammars.cleanup_deleted_rules!(g₁)
    @show g₁

    # Enumerate trees 
    possible_values_set = Set()
    symboltable::SymbolTable = Grammars.SymbolTable(g₁)
    for tree ∈ Search.get_dfs_enumerator(g₁, max_depth, type)
        output = Evaluation.interpret(symboltable, Grammars.rulenode2expr(tree, g₁))
        push!(possible_values_set, output)
    end
    # TODO: Look at different ways of randomizing the values
    return () -> Base.rand(possible_values_set)
end