
"""
Searches the grammar up to the maximum depth for possible values of a type.
Can take data from the input dataset into account.
Creating the generator can be a bit slow, since it generates a large number of 
programs and evaluates them.

# Arguments
 - `grammar::Grammar`:  The grammar for which to create a data generator.
 - `type::Symbol`:      The type in the grammar for which to create a data generator.
 - `max_size::Int`:     The maximum size in number of nodes of candidate programs for
                        obtaining values for the generator.
 - `max_depth::Int`:    The maximum depth of candidate programs for obtaining values
                        for the generator. Default value: `typemax(Int)`.
 - input_variable_data: A dict with a list of possible values for each variable for 
                        which data is available.
"""
function exhaustive_auto_generator(
    grammar::Grammar, 
    type::Symbol,
    max_size::Int;
    max_depth::Int=typemax(Int),
    input_variable_data=Dict{Symbol,Vector{Any}}()
)::Function
    g₁ = deepcopy(grammar)
    # Remove any variable rules for which there is no data
    for i ∈ 1:length(g₁.rules)
        if isvariable(g₁, i) && g₁.rules[i] ∉ keys(input_variable_data)
            remove_rule!(g₁, i)
        end
    end
    cleanup_removed_rules!(g₁)

    # Enumerate trees 
    possible_values_set = Set()
    symboltable::SymbolTable = SymbolTable(g₁)
    for tree ∈ get_dfs_enumerator(g₁, max_depth, max_size, type)
        for (k, v) ∈ input_variable_data
            symboltable[k] = Base.rand(v)
        end
        output = interpret(symboltable, rulenode2expr(tree, g₁))
        push!(possible_values_set, output)
    end
    return () -> Base.rand(possible_values_set)
end

function combine_generators(gen₁::Function, p::Real, gen₂::Function)
    return () -> Base.rand() ≤ p ? gen₁() : gen₂()
end