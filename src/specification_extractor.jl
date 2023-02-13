
"""
Generates all programs up to the maximum depth in the grammar,
and divides them into equivalence classes.

TODO: Optimize that programs without variables are only executed once
TODO: Optimize for when there are multiple identical variables with different names
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

    # Enumerate a lot of programs
    programs = Set(map(x -> Grammars.rulenode2expr(x, grammar), Search.get_bfs_enumerator(grammar, max_depth, start_symbol)))

    # Filter out programs that are identical to others by variable renaming 
    # (enforce that variables must be ordered)
    m = Dict([x => 0 for x ∈ keys(variables_by_type)])
    filter!(x -> _check_variable_renaming(x, variables_by_type, type_by_variable, deepcopy(m))[1], programs)
    @show programs

    equivalence_classesᵢ = [programs]
    equivalence_classesᵢ₊₁ = []
    batches_since_last_split = 0

    symboltable::SymbolTable = SymbolTable(grammar)

    while true
        for equivalence_class ∈ equivalence_classesᵢ
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
                outcomes = ntuple(i -> Evaluation.evaluate_with_input(symboltable, program, tests[i]), length(tests))
                new_classes[outcomes] = push!(get(new_classes, outcomes, Any[]), program)
            end
            append!(equivalence_classesᵢ₊₁, values(new_classes))
        end
        # TODO: Keep track of splits for batches individually
        if length(equivalence_classesᵢ) == length(equivalence_classesᵢ₊₁)
            batches_since_last_split += 1
        else 
            batches_since_last_split = 0
        end

        equivalence_classesᵢ = equivalence_classesᵢ₊₁
        equivalence_classesᵢ₊₁ = []
        if batches_since_last_split ≥ num_batches_after_last_split
            return equivalence_classesᵢ
        end
    end
end


"""
Returns a tuple with three integers. 

    1. The maximum depth of the expression.
    2. The number of nodes in the expression.
    3. The number of non-variable terminals in the expression.
This tuple signifies the generality of expressions for specification generation and can be used for sorting.
"""
_expr_depth_size_vars(::Symbol)::Tuple{Int, Int, Int} = (0, 1, 0)
_expr_depth_size_vars(::Any)::Tuple{Int, Int, Int} = (0, 1, 1)

function _expr_depth_size_vars(e::Expr)::Tuple{Int, Int, Int}
    if length(e.args) == 1
        return (0, 1, 1)
    end
    child_depth_size_vars = collect(zip(collect(map(_expr_depth_size_vars, e.args[2:length(e.args)]))...))
    return (maximum(child_depth_size_vars[1], init=0) + 1, 
        sum(child_depth_size_vars[2]) + 1, 
        sum(child_depth_size_vars[3]))
end


"""
Rewrites an equivalence class to a set of equalities.
Returns the simplest expression in the equivalence class and the set of equalities.
The simplest expression is also used in every equality.
"""
function equivalence2specs(equivalence_class)
    # Find program with smallest size for the minimal depth.
    simplest_expr = argmin(_expr_depth_size_vars, equivalence_class)

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
    best_element(ec) = minimum(map(_expr_depth_size_vars, ec))

    # Sort equivalence classes in increasing order of complexity of the smallest element.
    # or equivalently, decreasing order of generality of the smallest element. 
    sort!(equivalence_classes, lt=(a, b) -> best_element(a) < best_element(b))

    for i ∈ eachindex(equivalence_classes)
        # Don't look at equivalence classes that have been emptied in earlier iterations.
        if length(equivalence_classes[i]) == 0
            continue
        end
        (_, specs) = equivalence2specs(equivalence_classes[i])
        sort!(specs, lt=(a, b) -> _expr_depth_size_vars(a[2]) < _expr_depth_size_vars(b[2]))

        new_ec = Set(deepcopy(equivalence_classes[i]))

        # Prune current equivalence class
        exprs_to_remove = Set()
        for (old, new) ∈ specs
            # Don't consider specifications that have been removed in earlier iterations
            if old ∉ new_ec 
                continue
            end
            # Test specification on all expressions still in the equivalence class
            for expr ∈ new_ec
                # Don't consider the expression that generated this specification.
                if expr == old || expr == new
                    continue
                end
                rewritten_expr = _rewrite(expr, old, new)
                # If a successful rewrite was done 
                if rewritten_expr ≠ expr
                    push!(exprs_to_remove, expr)
                end
            end
            # Subtract exprs_to_remove from new_ec outside loop
            setdiff!(new_ec, exprs_to_remove)
            empty!(exprs_to_remove)
        end

        # Recompute new (pruned) equivalence class
        if length(new_ec) ≤ 1
            equivalence_classes[i] = []
            continue
        end
        equivalence_classes[i] = collect(new_ec)
        (_, specs) = equivalence2specs(equivalence_classes[i])
        sort!(specs, lt=(a, b) -> _expr_depth_size_vars(a[2]) < _expr_depth_size_vars(b[2]))

        # For each equivalence class we haven't seen before
        for j ∈ i+1:length(equivalence_classes)
            # Don't look at equivalence classes that have already been emptied
            if length(equivalence_classes[j]) == 0
                continue
            end
            new_ec = Set(deepcopy(equivalence_classes[j]))

            for (old, new) ∈ specs
                # Test specification on all expressions still in the equivalence class
                for expr ∈ new_ec
                    rewritten_expr = _rewrite(expr, old, new)
                    # If a successful rewrite was done, and the equivalent version hasn't been removed yet,
                    # we remove the original (less general) expression.
                    if rewritten_expr ≠ expr && rewritten_expr ∈ new_ec && rewritten_expr ∉ exprs_to_remove
                        push!(exprs_to_remove, expr)
                    end
                end
                # Subtract exprs_to_remove from new_ec outside loop
                setdiff!(new_ec, exprs_to_remove)
                empty!(exprs_to_remove)
            end
            if length(new_ec) ≤ 1
                equivalence_classes[j] = []
            else
                equivalence_classes[j] = new_ec
            end
        end
    end
    return collect(equivalence2specs.(filter(x -> x ≠ [], equivalence_classes)))
end