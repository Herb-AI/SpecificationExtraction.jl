
"""
Generates all programs up to the maximum depth in the grammar,
and divides them into equivalence classes.

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
    input_variables::Vector{NamedTuple{(:var, :type), Tuple{Symbol, Symbol}}} = []
    for (i, rule) ∈ enumerate(grammar.rules)
        if rule isa Symbol && rule ∉ grammar.types
            push!(input_variables, (var = rule, type = grammar.types[i]))
        end
    end
    
    # Enumerate a lot of programs
    programs = Set(map(x -> Grammars.rulenode2expr(x, grammar), Search.get_bfs_enumerator(grammar, max_depth, start_symbol)))

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

_expr_depth_and_size(::Symbol) = (0, 1)
_expr_depth_and_size(::Any) = (0, 1)

function _expr_depth_and_size(e::Expr)::Tuple{Int, Int}
    if length(e.args) == 0
        return (0, 1)
    end
    child_depth_size = collect(zip(collect(map(_expr_depth_and_size, e.args))...))
    return (maximum(child_depth_size[1], init=0) + 1, sum(child_depth_size[2]) + 1)
end

"""
Rewrites an equivalence class to a set equalities.
The simplest expression in the equivalence class is used in every equality.
"""
function equivalence2specs(equivalence_class)
    # Find program with smallest size for the minimal depth.
    simplest_expr = argmin(_expr_depth_and_size, equivalence_class)

    equivalences::Vector{Tuple{Any, Any}} = []
    for expr ∈ equivalence_class
        if expr ≠ simplest_expr
            push!(equivalences, (expr, simplest_expr))
        end
    end
    return equivalences
end