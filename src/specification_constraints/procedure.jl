function specification_discovery(
    grammar::Grammar,
    relation_grammar::Grammar,
    candidate_depth::Int,
    generator_depth::Int;
    numprograms::Int=1000
)
    @assert :Bool ∈ relation_grammar.types

    rg_without_vars = deepcopy(relation_grammar)

    grammar_without_vars = deepcopy(grammar)

    # Remove any variables from the grammar
    variable_rules = findall(x -> isvariable(grammar_without_vars, x), 1:length(grammar_without_vars.rules))
    for idx ∈ variable_rules
        remove_rule!(grammar_without_vars, idx)
    end

    # Remove any variables from the relation grammar
    relation_variable_rules = findall(x -> isvariable(rg_without_vars, x), 1:length(rg_without_vars.rules))
    for idx ∈ relation_variable_rules
        remove_rule!(rg_without_vars, idx)
    end

    # Create data generators
    generators::Dict{Symbol, Function} = Dict()
    for type ∈ grammar_without_vars.types
        generators[type] = exhaustive_auto_generator(grammar_without_vars, generator_depth, type)
    end

    # Add types to the relation grammar
    for type ∈ grammar_without_vars.types
        inputtype = Symbol("Input$type")
        outputtype = Symbol("Output$type")
        if inputtype ∉ keys(rg_without_vars.bytype)
            rg_without_vars.bytype[inputtype] = []
            rg_without_vars.domains[inputtype] = BitArray([false for _ ∈ 1 : length(rg_without_vars.rules)])
        end
        if outputtype ∉ keys(rg_without_vars.bytype)
            rg_without_vars.domains[outputtype] = BitArray([false for _ ∈ 1 : length(rg_without_vars.rules)])
            rg_without_vars.bytype[outputtype] = []
        end
    end

    for (i, rule) ∈ enumerate(grammar_without_vars.rules)
        println("-=-=================-=-")
        @show rule
        g = deepcopy(grammar_without_vars)
        rg = deepcopy(rg_without_vars)
        
        # Add input variables to relation grammar
        type_counter = Dict{Symbol, Int}(t => 0 for t ∈ g.types)
        type_by_variable = Dict{Symbol, Symbol}()
        relation_variable_ids_by_type = Dict{Symbol, Vector{Int}}(t => Int[] for t ∈ g.types)
        rulenode_under_test = RuleNode(i)
        for type ∈ g.childtypes[i]
            type_counter[type] += 1
            relation_type = Symbol("Input$type")
            varname = Symbol("VarInput$type$(type_counter[type])")
            add_rule!(rg, :($relation_type = $varname))
            add_rule!(g, :($type = $varname))
            push!(rulenode_under_test.children, RuleNode(length(g.rules)))
            push!(relation_variable_ids_by_type[type], length(rg.rules))
            type_by_variable[varname] = type
        end
        expression_under_test = rulenode2expr(rulenode_under_test, g)

        # Add output variable
        typesymbol = Symbol("Output$(g.types[i])")
        varname = Symbol("VarOutput$(g.types[i])")
        add_rule!(rg, :($typesymbol = $varname))
        push!(relation_variable_ids_by_type[g.types[i]], length(rg.rules))

        relations = specification_generation(
            g, 
            numprograms, 
            i, 
            expression_under_test, 
            rg, 
            generators, 
            type_by_variable, 
            relation_variable_ids_by_type,
            max_depth=candidate_depth
        )

        for relation ∈ relations
            @show relation.expr
        end
    end

end

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
)
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
            output_value = test_with_input(g_symboltable, tested_rule_expr, rule_test)
            test[Symbol("VarOutput$(grammar.types[tested_rule_ind])")] = output_value
            push!(tests, test)
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