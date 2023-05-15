abstract type SpecificationSymbol end

"""
Used for signifying a rule as a variable.
Gets converted to a sympy variable.
"""
struct SpecificationVariable <: SpecificationSymbol end

"""
Used for signifying a rule as an operator.
`sympy_equivalent` represents operator to which this gets translated in sympy representation.
"""
struct SpecificationOperator <: SpecificationSymbol
    sympy_equivalent::Function
end

"""
Used for signifying a rule as a literal.
Gets evaluated before converting to sympy representation.
"""
struct SpecificationLiteral <: SpecificationSymbol end

function specification_discovery(
    grammar::Grammar,
    relation_grammar::Grammar,
    translation::Dict{Int, SpecificationSymbol},
    candidate_max_size::Int,
    generator_max_size::Int;
    generators::Dict{Symbol, Function}=Dict{Symbol, Function}(),
    numprograms::Int=1000
)
    @assert :Bool ∈ relation_grammar.types

    rg_without_vars = deepcopy(relation_grammar)

    grammar_without_vars = deepcopy(grammar)

    # Remove any variables from the grammar to ensure that it can be evaluated
    variable_rules = findall(x -> isvariable(grammar_without_vars, x), 1:length(grammar_without_vars.rules))
    for idx ∈ variable_rules
        remove_rule!(grammar_without_vars, idx)
    end

    # Remove any variables from the relation grammars to ensure that it can be evaluated
    relation_variable_rules = findall(x -> isvariable(rg_without_vars, x), 1:length(rg_without_vars.rules))
    for idx ∈ relation_variable_rules
        println("rule $idx removed")
        remove_rule!(rg_without_vars, idx)
    end

    # Create data generators
    for type ∈ grammar_without_vars.types
        if type ∉ keys(generators)
            generators[type] = exhaustive_auto_generator(grammar_without_vars, type, generator_max_size)
        end
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
            translation[length(rg.rules)] = SpecificationVariable()
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
        translation[length(rg.rules)] = SpecificationVariable()

        relations = specification_generation(
            g, 
            numprograms, 
            i, 
            expression_under_test, 
            rg, 
            generators, 
            type_by_variable, 
            relation_variable_ids_by_type,
            max_size=candidate_max_size
        )

        # for relation ∈ relations
        #     @show relation.expr
        # end

        prune_relations(rg, translation, relations)
    end
end

function rulenode2sympy(
    grammar::Grammar,
    translation::Dict{Int, SpecificationSymbol},
    rn::RuleNode
)
    t = translation[rn.ind]
    if t isa SpecificationVariable
        expr = rulenode2expr(rn, grammar)
        varname = replace("$expr", "(" => "", ")" => "")
        return sympy.Symbol(varname)
    elseif t isa SpecificationOperator
        sympy_children = map(x -> rulenode2sympy(grammar, translation, x), rn.children)
        return t.sympy_equivalent(sympy_children...)
    else
        expr = rulenode2expr(rn, grammar)
        return eval(expr) 
    end
end

function prune_relations(
    grammar::Grammar,
    translation::Dict{Int, SpecificationSymbol},
    relations::Vector{NamedTuple{(:rulenode, :expr), Tuple{RuleNode, Any}}},
)
    # Turn relation into SymPy representation
    sympy_terms = []
    for relation ∈ relations
        sympy_term = rulenode2sympy(
            grammar,
            translation,
            relation.rulenode        
        )
        push!(sympy_terms, sympy_term)
    end
    sympy_representation = sympy.And(sympy_terms...)
    y = sympy.simplify(sympy_representation)
    if pybuiltin(:type)(y) == sympy.And
        for t ∈ y.args
            spec = replace(string(t), "PyObject" => "")
            println(spec)
        end
    else
        spec = replace(string(y), "PyObject" => "")
        println(spec)    
    end
end
