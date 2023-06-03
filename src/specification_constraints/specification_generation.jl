
function specification_generation(
    grammar::Grammar,
    numprograms::Int,
    tested_rule_ind::Int,
    tested_rule_expr::Any,
    relation_grammar::Grammar,
    data_generators::Dict{Symbol, Function},
    type_by_variable::Dict{Symbol, Symbol},
    variable_ids_by_type::Dict{Symbol, Vector{Int}};
    max_depth::Int=typemax(Int),
    max_size::Int=typemax(Int),
    batch_size::Int=64,
    required_batches_after_last_invalidation::Int=5
)::Vector{NamedTuple{(:rulenode, :expr), Tuple{RuleNode, Any}}}
    relations::Vector{NamedTuple{(:rulenode, :expr), Tuple{RuleNode, Any}}} = []
    enumerator = get_bfs_enumerator(relation_grammar, max_depth, max_size, :Bool)
    variable_ids = append!(Int[], [v for (k, v) ∈ variable_ids_by_type]...)

    for _ ∈ 1:numprograms
        next = Iterators.peel(enumerator)
        next ≡ nothing && break # All programs enumerated
        x, enumerator = next
        push!(relations, (rulenode = x, expr = rulenode2expr(x, relation_grammar)))
    end

    # Filter out any relations that don't contain variables
    filter!(x -> containsrule(x.rulenode, variable_ids), relations)


    g_symboltable = SymbolTable(grammar)
    rg_symboltable = SymbolTable(relation_grammar)


    # Filter any false specification from programs
    batches_since_last_invalidation = 0
    while batches_since_last_invalidation < required_batches_after_last_invalidation
        # Create tests
        tests = []
        for _ ∈ 1:batch_size
            success = false
            attempts = 0
            error = nothing
            while !success && attempts < 100

                rule_test::SymbolTable = Dict{Symbol, Any}()
                test::SymbolTable = Dict{Symbol, Any}()
                type_counter = Dict{Symbol, Int}(t => 0 for t ∈ grammar.types)
                for type ∈ grammar.childtypes[tested_rule_ind]
                    i = type_counter[type] += 1
                    
                    generated_value = data_generators[type]()
                    varname = Symbol("VarInput$type$i") 
                    test[varname] = generated_value
                    rule_test[varname] = generated_value
                end
                attempts += 1
                try
                    output_value = test_with_input(g_symboltable, tested_rule_expr, rule_test)
                    test[Symbol("VarOutput$(grammar.types[tested_rule_ind])")] = output_value
                    push!(tests, test)
                    success = true
                catch e 
                    error = e
                end
            end
            if !success
                @warn "Couldn't find a working example in 100 attempts:"
                Base.showerror(stdout, error)
            end
        end

        @show length(tests)
        if length(tests) == 0
            return nothing
        end

        # Filter any relation that doesn't return true for all tests
        size_before = length(relations)
        filter!(r -> all(test_with_input(rg_symboltable, r.expr, t) for t ∈ tests), relations)
        size_after = length(relations)

        if size_before == size_after
            batches_since_last_invalidation += 1
        else
            batches_since_last_invalidation = 0
        end
    end

    return relations
end