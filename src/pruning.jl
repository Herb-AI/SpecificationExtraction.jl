
"""
Converts equivalences to specifications and prunes them.
"""
function equivalences2specs(grammar::Grammar, equivalence_classes)
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