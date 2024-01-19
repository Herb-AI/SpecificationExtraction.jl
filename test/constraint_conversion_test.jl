@testset "Constraint conversion" verbose=true begin
    g = @csgrammar begin
        Real = a # 1
        Real = b # 2
        Real = |(0:9) # 3 - 12
        Real = Real +₂ Real # 13
        Real = Real -₂ Real # 14
        Real = Real *₂ Real # 15
    end

    @testset "a + 0 ≡ a" begin
        variables=Dict([16 => :a])
        lhs = RuleNode(13, [RuleNode(16), RuleNode(3)]) # a+0
        rhs = RuleNode(3) # 0
        e = EquivalenceSpecification(lhs, rhs)

        constraints = specs2constraints([e], variables)
        @test length(constraints) == 1 && constraints[1] isa Forbidden
    end

    @testset "2 × a ≡ a + a" begin
        variables=Dict([16 => :a])
        lhs = RuleNode(15, [RuleNode(5), RuleNode(16)]) # 2*a
        rhs = RuleNode(13, [RuleNode(16), RuleNode(16)]) # a+a
        e = EquivalenceSpecification(lhs, rhs)

        constraints = specs2constraints([e], variables)
        @test length(constraints) == 1 && constraints[1] isa Forbidden
    end

    @testset "a + a ≡ 2 × a" begin
        variables=Dict([16 => :a])
        lhs = RuleNode(13, [RuleNode(16), RuleNode(16)]) # a+a
        rhs = RuleNode(15, [RuleNode(5), RuleNode(16)]) # 2*a
        e = EquivalenceSpecification(lhs, rhs)

        constraints = specs2constraints([e], variables)
        @test length(constraints) == 1 && constraints[1] isa Forbidden
    end

    @testset "(a + b) + c ≡ a + (b + c)" begin
        variables = Dict([16 => :a, 17 => :b, 18 => :c])
        lhs = RuleNode(13, [RuleNode(13, [RuleNode(16), RuleNode(17)]), RuleNode(18)]) # (a + b) + c
        rhs = RuleNode(13, [RuleNode(16), RuleNode(13, [RuleNode(17), RuleNode(18)])]) # a + (b + c)
        e = EquivalenceSpecification(lhs, rhs)

        constraints = specs2constraints([e], variables)
        @test length(constraints) == 1 && constraints[1] isa Forbidden
    end

    @testset "6 + a ≡ a + 6" begin
        # Should not be a Forbidden constraint, since that removes 6 + 6
        variables = Dict([16 => :a])
        lhs = RuleNode(13, [RuleNode(9), RuleNode(16)]) # 6 + a
        rhs = RuleNode(13, [RuleNode(16), RuleNode(9)]) # a + 6
        e = EquivalenceSpecification(lhs, rhs)

        constraints = specs2constraints([e], variables)
        @test length(constraints) == 0 || !(constraints[1] isa Forbidden)
    end

    @testset "(3 + 2) + a ≡ a + (3 + 2)" begin
        # Should not be a Forbidden constraint, since that removes (3 + 2) + (3 + 2)
        variables = Dict([16 => :a])
        lhs = RuleNode(13, [RuleNode(13, [RuleNode(6), RuleNode(5)]), RuleNode(16)]) # (3 + 2) + a
        rhs = RuleNode(13, [RuleNode(16), RuleNode(13, [RuleNode(6), RuleNode(5)])]) # a + (3 + 2)
        e = EquivalenceSpecification(lhs, rhs)

        constraints = specs2constraints([e], variables)
        @test length(constraints) == 0 || !(constraints[1] isa Forbidden)
    end

    @testset "(3 + 2) × 0 ≡ a × 0" begin
        # This scenario isn't likely to occur, but it is a good edge case.
        variables = Dict([16 => :a])
        lhs = RuleNode(15, [RuleNode(13, [RuleNode(6), RuleNode(5)]), RuleNode(3)]) # (3 + 2) × 0
        rhs = RuleNode(15, [RuleNode(16), RuleNode(3)]) # a × 0
        e = EquivalenceSpecification(lhs, rhs)

        constraints = specs2constraints([e], variables)
        @test length(constraints) == 0 || !(constraints[1] isa Forbidden)
        # TODO: Update with what it should be instead 
    end

    @testset "a + b ≡ b + a" begin
        variables = Dict([16 => :a, 17 => :b])

        lhs = RuleNode(13, [RuleNode(16), RuleNode(17)]) # a + b
        rhs = RuleNode(13, [RuleNode(17), RuleNode(16)]) # b + a
        e = EquivalenceSpecification(lhs, rhs)

        constraints = specs2constraints([e], variables)
        @test length(constraints) == 1 && constraints[1] isa Ordered
    end
end 
