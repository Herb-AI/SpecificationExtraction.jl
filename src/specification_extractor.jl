
"""
Generates all programs up to the maximum depth in the grammar,
and divides them into equivalence classes.
Returns vector of vectors with equivalent rulenodes.

TODO: Optimize that programs without variables are only executed once
"""
function extract_specifications(
        grammar::Grammars.ContextFreeGrammar, 
        max_depth::Int, 
        start_symbol::Symbol, 
        data_generators, 
        batch_size::Int=64,
        num_batches_after_last_split::Int=5
    )

    # Identify the input variables in the grammar
    variables_by_type = Dict()
    type_by_variable = Dict()
    input_variables::Vector{NamedTuple{(:var, :type), Tuple{Symbol, Symbol}}} = []
    for (i, rule) ∈ enumerate(grammar.rules)
        if rule isa Symbol && rule ∉ grammar.types
            push!(input_variables, (var = rule, type = grammar.types[i]))
            push!(get!(variables_by_type, grammar.types[i], []), rule)
            type_by_variable[rule] = grammar.types[i]
        end
    end

    # Enumerate a lot of programs and precompute their expressions
    programs::Vector{NamedTuple{(:rulenode, :expr), Tuple{RuleNode, Any}}} = map(
        x -> (rulenode = x, expr = Grammars.rulenode2expr(x, grammar)), 
        Search.get_bfs_enumerator(grammar, max_depth, start_symbol)
    )

    # Only allow programs that when using a variable also use all variables of the same type 
    # that are defined above it in the grammar.
    # Prevents certain duplicates by variable renaming.
    # TODO: Make this step more efficient, it takes up a lot of time
    filter!(x -> _check_variable_usage(x.expr, type_by_variable, variables_by_type), programs)

    final_equivalence_classes = []
    equivalence_classesᵢ = [programs]
    batches_since_last_splitᵢ = [0]
    equivalence_classesᵢ₊₁ = []
    batches_since_last_splitᵢ₊₁ = []
    batches_since_last_split = 0

    symboltable::SymbolTable = SymbolTable(grammar)

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
                for input_variable ∈ input_variables
                    test[input_variable.var] = data_generators[input_variable.type]()
                end
                push!(tests, test)
            end
            new_classes = Dict()

            # run tests
            for program ∈ equivalence_class
                outcomes = ntuple(i -> Evaluation.evaluate_with_input(symboltable, program.expr, tests[i]), length(tests))
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
Returns the simplest expression in the equivalence class and the set of equalities.
The simplest expression is also used in every equality.
The left-hand sides of the expressions are assumed to stay in the order of the equivalence class. 
"""
function equivalence2specs(grammar::ContextFreeGrammar, equivalence_class)
    # Find program with smallest size for the minimal depth.
    simplest_expr = argmin(x -> _expr_depth_size_vars(x, grammar), equivalence_class)

    equivalences::Vector{Tuple{Any, Any}} = []
    for expr ∈ equivalence_class
        if expr ≠ simplest_expr
            push!(equivalences, (expr, simplest_expr))
        end
    end
    return (simplest_expr, equivalences)
end


"""
Converts equivalences to specifications and prunes them.
TODO: Automatically derive variable types from grammar
"""
function equivalences2specs(grammar::ContextFreeGrammar, equivalence_classes)
    # Helper function for finding the best expression in an equivalence class
    best_element(ec) = minimum(map(x -> _expr_depth_size_vars(x, grammar), ec))

    # Sort equivalence classes in increasing order of complexity of the smallest element.
    # or equivalently, decreasing order of generality of the smallest element. 
    println("Sorting classes")
    sort!(equivalence_classes, lt=(a, b) -> best_element(a) < best_element(b))

    # Sort all equivalence classes
    println("Sorting...")
    for i ∈ ProgressBar(eachindex(equivalence_classes))
        sort!(equivalence_classes[i], lt=(a, b) -> _expr_depth_size_vars(a, grammar) < _expr_depth_size_vars(b, grammar))
    end

    println("Pruning...")
    for i ∈ ProgressBar(eachindex(equivalence_classes))
        # Don't look at equivalence classes that have been emptied in earlier iterations.
        if length(equivalence_classes[i]) == 0
            continue
        end

        # Convert equivalence class to specifications and sort the specifications
        (_, specs) = equivalence2specs(grammar, equivalence_classes[i])

        # The specifications are sorted at this point, since the order of the equivalence class is maintained.

        # Prune current equivalence class
        new_ec = []
        for node ∈ equivalence_classes[i]
            redundant = false
            for (old, new) ∈ specs
                # Don't consider the expressions that generated this specification.
                if node == old || node == new
                    continue
                end
                rewritten_node = _rewrite(grammar, node, old, new)
                # If a successful rewrite was done 
                if rewritten_node ∈ new_ec
                    redundant = true
                    break
                end
            end
            if !redundant
                push!(new_ec, node)
            end
        end

        # Recompute new (pruned) equivalence class
        if length(new_ec) ≤ 1
            # There are no specifications left
            equivalence_classes[i] = []
            continue
        end
        equivalence_classes[i] = collect(new_ec)

        # Compute the specifications again from the pruned equivalence class
        (_, specs) = equivalence2specs(grammar, equivalence_classes[i])

        # The specifications are sorted at this point, since the order of the equivalence 
        # class is maintained (also after pruning).

        # For each other equivalence class:
        for j ∈ Base.Iterators.flatten((1:i-1, i+1:length(equivalence_classes)))
            # Don't look at equivalence classes that have already been emptied
            if length(equivalence_classes[j]) ≤ 1
                continue
            end

            # equivalence_classes[j] is still sorted.

            new_ec = []
            for node ∈ equivalence_classes[j]
                redundant = false
                for (old, new) ∈ specs
                    rewritten_node = _rewrite(grammar, node, old, new)
                    # An expression is redundant if it can be rewritten to another expression 
                    # that is already in the new equivalence class.
                    if rewritten_node ∈ new_ec
                        redundant = true
                        break
                    end
                end
                if !redundant
                    push!(new_ec, node)
                end
            end

            # If there is less than 2 expressions in the equivalence class, no equivalence can be generated,
            # and the class can be discarded.
            if length(new_ec) ≤ 1
                equivalence_classes[j] = []
            else
                equivalence_classes[j] = new_ec
            end
        end
    end
    return map(x -> equivalence2specs(grammar, x), filter(x -> x ≠ [], equivalence_classes))
end