"""
Abstract type that represents all specifications.
"""
abstract type Specification end

"""
A specification that specifies the equivalence of two rulenode trees.
"""
struct EquivalenceSpecification <: Specification
    lhs::RuleNode
    rhs::RuleNode
end