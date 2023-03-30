"""
Converts equivalences to specifications and prunes them.
"""
function equivalences2specs(grammar::Grammar, equivalence_classes, vars::Dict{Int, Symbol})
    priority_function = isprobabilistic(grammar) ? rulenode_probability : _expr_depth_size_vars

    # Helper function for finding the best expression in an equivalence class
    best_element(ec) = minimum(map(x -> priority_function(x, grammar), ec))

    # Sort equivalence classes in increasing order of complexity of the smallest element.
    # or equivalently, decreasing order of generality of the smallest element. 
    println("Sorting classes")
    sort!(equivalence_classes, lt=(a, b) -> best_element(a) < best_element(b))

    # Sort all equivalence classes
    println("Sorting...")
    for i ∈ ProgressBar(eachindex(equivalence_classes))
        sort!(equivalence_classes[i], lt=(a, b) -> priority_function(a, grammar) < priority_function(b, grammar))
    end

    count = 0
    for ec ∈ equivalence_classes
        _, specs = equivalence2specs(grammar, ec)
        for (old, new) ∈ specs
            if containsrule(old, collect(keys(vars)))
                count += 1
                println("$(rulenode2expr(old, grammar)) → $(rulenode2expr(new, grammar))")
            end
        end
    end
    @show count

    println("Pruning...")
    for i ∈ ProgressBar(eachindex(equivalence_classes))
        # Don't look at equivalence classes that have been emptied in earlier iterations.
        if length(equivalence_classes[i]) == 0
            continue
        end

        # Convert equivalence class to specifications and sort the specifications
        _, specs = equivalence2specs(grammar, equivalence_classes[i])
        
        
        # The specifications are sorted at this point, since the order of the equivalence class is maintained.

        # Prune current equivalence class
        for (old, new) ∈ specs
            constraint = spec2constraint(old, new, vars)
            if old ∉ equivalence_classes[i]
                # We already removed this constraint in an earlier iteration, 
                # so we don't need to check it.
                continue
            end
            redundant_node_indices = []
            for (node_ind, node) ∈ enumerate(equivalence_classes[i])
                # Don't consider the expressions that generated this specification.
                if node == old || node == new
                    continue
                end
                if !check_tree(constraint, grammar, node)
                    # The tree didn't abide the constraint and thus will not be generated 
                    # if we would use the current constraint in the search.
                    # This makes the constraint corresponding to this node redundant.
                    push!(redundant_node_indices, node_ind)
                end
            end

            # Remove redundant node indices in reverse, since otherwise indices shift.
            for node_ind ∈ reverse!(redundant_node_indices)
                deleteat!(equivalence_classes[i], node_ind)
            end
        end

        # Recompute new (pruned) equivalence class
        if length(equivalence_classes[i]) ≤ 1
            # There are no specifications left
            equivalence_classes[i] = []
            continue
        end

        # Compute the specifications again from the pruned equivalence class
        _, specs = equivalence2specs(grammar, equivalence_classes[i])

        # The specifications are sorted at this point, since the order of the equivalence 
        # class is maintained (also after pruning).

        # For each other equivalence class:
        for j ∈ Base.Iterators.flatten((1:i-1, i+1:length(equivalence_classes)))
            # Don't look at equivalence classes that have already been emptied
            if length(equivalence_classes[j]) ≤ 1
                continue
            end

            # equivalence_classes[j] is still sorted.
            for (old, new) ∈ specs
                constraint = spec2constraint(old, new, vars)
                redundant_node_indices = []
                for (node_ind, node) ∈ enumerate(equivalence_classes[j])
                    if !check_tree(constraint, grammar, node)
                        # The tree didn't abide the constraint and thus will not be generated 
                        # if we would use the current constraint in the search.
                        # This makes the constraint corresponding to this node redundant.
                        push!(redundant_node_indices, node_ind)
                    end
                end
    
                # Remove redundant node indices in reverse, since otherwise indices shift.
                for node_ind ∈ reverse!(redundant_node_indices)
                    deleteat!(equivalence_classes[j], node_ind)
                end
            end

            # If there is less than 2 expressions in the equivalence class, no equivalence can be generated,
            # and the class can be discarded.
            if length(equivalence_classes[j]) ≤ 1
                equivalence_classes[j] = []
            end
        end
    end

    return map(x -> equivalence2specs(grammar, x), filter(x -> x ≠ [], equivalence_classes))
end