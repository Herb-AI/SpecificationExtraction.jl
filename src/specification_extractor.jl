
"""
Generates all programs up to the maximum depth in the grammar,
and divides them into equivalence classes.
Returns vector of vectors with equivalent rulenodes.

TODO: Optimize that programs without variables are only executed once
"""
function get_equivalences(
        g::Grammar, 
        numprograms::Int,
        start_symbol::Symbol, 
        data_generators, 
        type_by_variable::Dict{Symbol, Symbol},
        variables_by_type::Dict{Symbol, Vector{Symbol}};
        max_depth::Int=typemax(Int),
        batch_size::Int=64,
        num_batches_after_last_split::Int=5
    )

    enumerator_constructor = (isprobabilistic(g) ? 
        get_most_likely_first_enumerator :
        get_bfs_enumerator)
    
    enumerator = enumerator_constructor(g, max_depth, start_symbol)

    # Enumerate a lot of programs and precompute their expressions
    programs::Vector{NamedTuple{(:rulenode, :expr), Tuple{RuleNode, Any}}} = []
    println("Generating expressions")
    @show g.rules
    for _ ∈ ProgressBar(1:numprograms)
        next = Iterators.peel(enumerator)
        next ≡ nothing && break
        x, enumerator = next
        push!(programs, (rulenode = x, expr = rulenode2expr(x, g)))
    end
    
    # Only allow programs that when using a variable also use all variables of the same type 
    # that are defined above it in the grammar.
    # Prevents certain duplicates by variable renaming.
    Iterators.filter!(x -> _check_variable_usage(x.expr, type_by_variable, variables_by_type), programs)

    final_equivalence_classes = []
    equivalence_classesᵢ = [programs]
    batches_since_last_splitᵢ = [0]
    equivalence_classesᵢ₊₁ = []
    batches_since_last_splitᵢ₊₁ = []
    batches_since_last_split = 0

    symboltable::SymbolTable = SymbolTable(g)

    while length(equivalence_classesᵢ) > 0
        for (equivalence_class, batches_since_last_split) ∈ zip(equivalence_classesᵢ, batches_since_last_splitᵢ)
            if batches_since_last_split ≥ num_batches_after_last_split
                push!(final_equivalence_classes, map(x -> x.rulenode, equivalence_class))
                continue
            end
            tests = []
            # create tests
            for _ ∈ 1:batch_size
                test::SymbolTable = Dict()
                for (var, type) ∈ type_by_variable
                    test[var] = data_generators[type]()
                end
                push!(tests, test)
            end
            new_classes = Dict()

            # run tests
            for program ∈ equivalence_class
                outcomes = ntuple(i -> test_with_input(symboltable, program.expr, tests[i]), length(tests))
                new_classes[outcomes] = push!(get(new_classes, outcomes, Any[]), program)
            end
            nc = values(new_classes)
            
            if length(values(new_classes)) == 1
                append!(equivalence_classesᵢ₊₁, nc)
                push!(batches_since_last_splitᵢ₊₁, batches_since_last_split + 1)
            else
                append!(equivalence_classesᵢ₊₁, nc)
                append!(batches_since_last_splitᵢ₊₁, zeros(length(nc)))
            end
        end
        equivalence_classesᵢ = equivalence_classesᵢ₊₁
        equivalence_classesᵢ₊₁ = []
        batches_since_last_splitᵢ = batches_since_last_splitᵢ₊₁
        batches_since_last_splitᵢ₊₁ = []
    end
    return final_equivalence_classes
end

"""
Rewrites an equivalence class to a set of equalities.
Returns the simplest rulenode tree in the equivalence class and the set of equivalence specifications.
The simplest tree is also used in every equality.
The left-hand sides of the expressions stay in the order of the equivalence class. 
"""
function equivalence_class2specs(grammar::Grammar, equivalence_class)::Vector{EquivalenceSpecification}
    # Find program with smallest size for the minimal depth.
    rhs = argmin(x -> (_expr_depth_size_vars(x, grammar), x), equivalence_class)

    equivalences = EquivalenceSpecification[]
    for lhs ∈ equivalence_class
        if lhs ≠ rhs
            push!(equivalences, EquivalenceSpecification(lhs, rhs))
        end
    end
    return equivalences
end