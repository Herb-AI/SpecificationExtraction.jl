
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
        batch_size::Int=64)
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

    symboltable::SymbolTable = SymbolTable(grammar)

    for _ ∈ 1:10
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
        equivalence_classesᵢ = equivalence_classesᵢ₊₁
        equivalence_classesᵢ₊₁ = []
        @show length(equivalence_classesᵢ)
    end
    return equivalence_classesᵢ
end