package dev.moklev.mathproof.algebra

import dev.moklev.mathproof.algebra.tactics.ring.RingCoefficients
import dev.moklev.mathproof.algebra.tactics.ring.ring
import dev.moklev.mathproof.algebra.tactics.ring.ringSimplify
import dev.moklev.mathproof.algebra.theories.Commutative
import dev.moklev.mathproof.algebra.theories.SemiringTheory
import dev.moklev.mathproof.core.constant
import dev.moklev.mathproof.core.function
import dev.moklev.mathproof.core.statement
import dev.moklev.mathproof.equality.eq
import dev.moklev.mathproof.kernel.DerivationFact
import dev.moklev.mathproof.kernel.DerivationScope
import dev.moklev.mathproof.kernel.ProofEvidence
import dev.moklev.mathproof.kernel.ProofVerifier
import dev.moklev.mathproof.kernel.StatementDefinition
import dev.moklev.mathproof.kernel.trusted
import dev.moklev.mathproof.model.Expr
import dev.moklev.mathproof.model.NamedSort
import kotlin.test.assertFailsWith
import kotlin.test.assertTrue
import kotlin.test.Test

class RingSimplifyTest {
    companion object {
        private val scalar = NamedSort("RingSimplifyScalar")
        private val constants = (0..64).associateWith { value ->
            constant("ring-simplify-c$value", scalar)
        }
        private val constantValuesByExpr = constants.entries.associate { (value, expr) -> expr to value }
        private val zero = coefficientExpr(0)
        private val one = coefficientExpr(1)
        private val add = function("add", scalar, scalar, returns = scalar)
        private val mul = function("mul", scalar, scalar, returns = scalar)
        private val pow = function("pow", scalar, scalar, returns = scalar)
        private val coefficientAddStatements = mutableMapOf<Pair<Int, Int>, StatementDefinition>()
        private val coefficientMulStatements = mutableMapOf<Pair<Int, Int>, StatementDefinition>()

        private val semiring = object : SemiringTheory(
            name = "semiring",
            carrier = scalar,
            zero = zero,
            one = one,
            add = add,
            mul = mul,
        ) {
            override val semiringEvidence = object : Evidence {
                override fun addAssociativeEvidence(x: Expr, y: Expr, z: Expr): ProofEvidence = trusted()
                override fun addCommutativeEvidence(x: Expr, y: Expr): ProofEvidence = trusted()
                override fun addZeroRightEvidence(x: Expr): ProofEvidence = trusted()
                override fun mulAssociativeEvidence(x: Expr, y: Expr, z: Expr): ProofEvidence = trusted()
                override fun mulZeroLeftEvidence(x: Expr): ProofEvidence = trusted()
                override fun mulZeroRightEvidence(x: Expr): ProofEvidence = trusted()
                override fun mulOneLeftEvidence(x: Expr): ProofEvidence = trusted()
                override fun mulOneRightEvidence(x: Expr): ProofEvidence = trusted()
                override fun mulDistributesOverAddLeftEvidence(x: Expr, y: Expr, z: Expr): ProofEvidence = trusted()
                override fun mulDistributesOverAddRightEvidence(x: Expr, y: Expr, z: Expr): ProofEvidence = trusted()
            }
        }

        private val commutativeSemiring = object : SemiringTheory(
            name = "commutative-semiring",
            carrier = scalar,
            zero = zero,
            one = one,
            add = add,
            mul = mul,
        ), Commutative<SemiringTheory> {
            override val semiringEvidence = object : Evidence {
                override fun addAssociativeEvidence(x: Expr, y: Expr, z: Expr): ProofEvidence = trusted()
                override fun addCommutativeEvidence(x: Expr, y: Expr): ProofEvidence = trusted()
                override fun addZeroRightEvidence(x: Expr): ProofEvidence = trusted()
                override fun mulAssociativeEvidence(x: Expr, y: Expr, z: Expr): ProofEvidence = trusted()
                override fun mulZeroLeftEvidence(x: Expr): ProofEvidence = trusted()
                override fun mulZeroRightEvidence(x: Expr): ProofEvidence = trusted()
                override fun mulOneLeftEvidence(x: Expr): ProofEvidence = trusted()
                override fun mulOneRightEvidence(x: Expr): ProofEvidence = trusted()
                override fun mulDistributesOverAddLeftEvidence(x: Expr, y: Expr, z: Expr): ProofEvidence = trusted()
                override fun mulDistributesOverAddRightEvidence(x: Expr, y: Expr, z: Expr): ProofEvidence = trusted()
            }

            override val commutativeTheory: SemiringTheory get() = this
            override val commutativeEvidence = object : Commutative.Evidence {
                override fun mulCommutativeEvidence(a: Expr, b: Expr): ProofEvidence = trusted()
            }
        }

        private val coefficients = object : RingCoefficients {
            override fun isConstant(expr: Expr): Boolean = expr in constantValuesByExpr

            context(scope: DerivationScope)
            override fun add(left: Expr, right: Expr): DerivationFact {
                val leftValue = coefficientValue(left)
                val rightValue = coefficientValue(right)
                return scope.infer(coefficientAddStatement(leftValue, rightValue))
            }

            context(scope: DerivationScope)
            override fun mul(left: Expr, right: Expr): DerivationFact {
                val leftValue = coefficientValue(left)
                val rightValue = coefficientValue(right)
                return scope.infer(coefficientMulStatement(leftValue, rightValue))
            }
        }

        private fun coefficientExpr(value: Int): Expr = requireNotNull(constants[value]) {
            "No coefficient expression registered for value $value."
        }

        private fun coefficientValue(expr: Expr): Int = requireNotNull(constantValuesByExpr[expr]) {
            "Expression '$expr' is not a registered test coefficient."
        }

        private fun coefficientAddStatement(left: Int, right: Int): StatementDefinition =
            coefficientAddStatements.getOrPut(left to right) {
                val sum = left + right
                statement("coeff-add-$left-$right") {
                    conclusion(semiring.add(coefficientExpr(left), coefficientExpr(right)) eq coefficientExpr(sum))
                    assumed("Test-only trusted coefficient addition oracle.")
                }
            }

        private fun coefficientMulStatement(left: Int, right: Int): StatementDefinition =
            coefficientMulStatements.getOrPut(left to right) {
                val product = left * right
                statement("coeff-mul-$left-$right") {
                    conclusion(semiring.mul(coefficientExpr(left), coefficientExpr(right)) eq coefficientExpr(product))
                    assumed("Test-only trusted coefficient multiplication oracle.")
                }
            }
    }

    private val verifier = ProofVerifier(failOnWarnings = true)

    private fun assertVerifies(statement: StatementDefinition) {
        val result = verifier.verify(statement)
        assertTrue(result.isValid, result.describeIssues())
    }

    @Test
    fun ringSimplifyCollapsesRepeatedTermsIntoTimesEight() {
        val theorem = statement("ring-simplify-many-identical-subexpressions-to-times-eight") {
            val x = parameter("x", scalar)
            val y = parameter("y", scalar)

            val repeated = semiring.mul(x, y)
            val expression = semiring.add(
                semiring.add(semiring.add(repeated, repeated), semiring.add(repeated, repeated)),
                semiring.add(semiring.add(repeated, repeated), semiring.add(repeated, repeated)),
            )
            val expected = semiring.mul(repeated, coefficientExpr(8))

            conclusion(expression eq expected)
            proof {
                semiring.ringSimplify(expression, coefficients)
            }
        }

        assertVerifies(theorem)
    }

    @Test
    fun ringSimplifyRemovesTrailingOneInLongMonoid() {
        val theorem = statement("ring-simplify-trailing-one-long-monoid") {
            val x = parameter("x", scalar)
            val y = parameter("y", scalar)

            val expression = semiring.mul(semiring.mul(x, y), coefficientExpr(1))
            val expected = semiring.mul(x, y)

            conclusion(expression eq expected)
            proof {
                semiring.ringSimplify(expression, coefficients)
            }
        }

        assertVerifies(theorem)
    }

    @Test
    fun ringSimplifyFoldsTrailingConstantPairInsideLongMonoid() {
        val theorem = statement("ring-simplify-folds-trailing-constant-pair-inside-long-monoid") {
            val x = parameter("x", scalar)

            val expression = semiring.mul(semiring.mul(x, coefficientExpr(2)), coefficientExpr(3))
            val expected = semiring.mul(x, coefficientExpr(6))

            conclusion(expression eq expected)
            proof {
                semiring.ringSimplify(expression, coefficients)
            }
        }

        assertVerifies(theorem)
    }

    @Test
    fun ringSimplifySortAtomsInMonoidUsesNonFirstSwapPath() {
        val theorem = statement("ring-simplify-sort-atoms-in-monoid-uses-non-first-swap-path") {
            val x = parameter("x", scalar)
            val y = parameter("y", scalar)
            val z = parameter("z", scalar)

            val needsInnerSwap = commutativeSemiring.mul(commutativeSemiring.mul(x, z), y)
            val sorted = commutativeSemiring.mul(commutativeSemiring.mul(x, y), z)

            conclusion(sorted eq sorted)
            proof {
                commutativeSemiring.ringSimplify(needsInnerSwap)
                commutativeSemiring.ringSimplify(sorted)
            }
        }

        assertVerifies(theorem)
    }

    @Test
    fun ringSimplifyRemovesTrailingZeroInLongMonoid() {
        val theorem = statement("ring-simplify-trailing-zero-long-monoid") {
            val x = parameter("x", scalar)
            val y = parameter("y", scalar)

            val expression = semiring.mul(semiring.mul(x, y), coefficientExpr(0))
            val expected = coefficientExpr(0)

            conclusion(expression eq expected)
            proof {
                semiring.ringSimplify(expression, coefficients)
            }
        }

        assertVerifies(theorem)
    }

    @Test
    fun ringSimplifyCollapsesComplexRepeatedAtomsIntoTimesEight() {
        val theorem = statement("ring-simplify-complex-repeated-atoms-to-times-eight") {
            val x = parameter("x", scalar)
            val y = parameter("y", scalar)

            val powXY = pow(x, y)
            val termA = commutativeSemiring.mul(powXY, x)
            val termB = commutativeSemiring.mul(x, powXY)
            val expression = commutativeSemiring.add(
                commutativeSemiring.add(termA, termB),
                commutativeSemiring.add(
                    commutativeSemiring.add(termB, termA),
                    commutativeSemiring.add(
                        commutativeSemiring.add(termA, termB),
                        commutativeSemiring.add(termB, termA),
                    ),
                ),
            )
            val normalizedTerm = commutativeSemiring.mul(powXY, x)
            val expected = commutativeSemiring.mul(normalizedTerm, coefficientExpr(8))

            conclusion(expression eq expected)
            proof {
                commutativeSemiring.ringSimplify(expression, coefficients)
            }
        }

        assertVerifies(theorem)
    }

    @Test
    fun ringSimplifyFoldMulConstantsBranchMatrix() {
        data class Case(
            val id: String,
            val expression: (Expr, Expr) -> Expr,
            val expected: (Expr, Expr) -> Expr,
        )

        val cases = listOf(
            Case(
                id = "x-times-one",
                expression = { x, _ -> semiring.mul(x, coefficientExpr(1)) },
                expected = { x, _ -> x },
            ),
            Case(
                id = "x-times-zero",
                expression = { x, _ -> semiring.mul(x, coefficientExpr(0)) },
                expected = { _, _ -> coefficientExpr(0) },
            ),
            Case(
                id = "xy-times-one",
                expression = { x, y -> semiring.mul(semiring.mul(x, y), coefficientExpr(1)) },
                expected = { x, y -> semiring.mul(x, y) },
            ),
            Case(
                id = "xy-times-zero",
                expression = { x, y -> semiring.mul(semiring.mul(x, y), coefficientExpr(0)) },
                expected = { _, _ -> coefficientExpr(0) },
            ),
            Case(
                id = "x-times-two-unchanged",
                expression = { x, _ -> semiring.mul(x, coefficientExpr(2)) },
                expected = { x, _ -> semiring.mul(x, coefficientExpr(2)) },
            ),
            Case(
                id = "xy-times-two-unchanged",
                expression = { x, y -> semiring.mul(semiring.mul(x, y), coefficientExpr(2)) },
                expected = { x, y -> semiring.mul(semiring.mul(x, y), coefficientExpr(2)) },
            ),
            Case(
                id = "xy-times-two-times-three-folds",
                expression = { x, y ->
                    semiring.mul(
                        semiring.mul(semiring.mul(x, y), coefficientExpr(2)),
                        coefficientExpr(3),
                    )
                },
                expected = { x, y -> semiring.mul(semiring.mul(x, y), coefficientExpr(6)) },
            ),
        )

        cases.forEach { testCase ->
            val theorem = statement("ring-simplify-fold-mul-const-${testCase.id}") {
                val x = parameter("x", scalar)
                val y = parameter("y", scalar)

                val expression = testCase.expression(x, y)
                val expected = testCase.expected(x, y)

                conclusion(expression eq expected)
                proof {
                    semiring.ringSimplify(expression, coefficients)
                }
            }

            assertVerifies(theorem)
        }
    }

    @Test
    fun ringSimplifyFoldMonoidsReplaceMulOneMatrix() {
        data class Case(
            val id: String,
            val expression: (Expr, Expr) -> Expr,
            val expected: (Expr, Expr) -> Expr,
        )

        val cases = listOf(
            Case(
                id = "x-plus-x-times-two",
                expression = { x, _ -> semiring.add(x, semiring.mul(x, coefficientExpr(2))) },
                expected = { x, _ -> semiring.mul(x, coefficientExpr(3)) },
            ),
            Case(
                id = "x-times-two-plus-x",
                expression = { x, _ -> semiring.add(semiring.mul(x, coefficientExpr(2)), x) },
                expected = { x, _ -> semiring.mul(x, coefficientExpr(3)) },
            ),
            Case(
                id = "y-plus-x-plus-x-times-two",
                expression = { x, y -> semiring.add(semiring.add(y, x), semiring.mul(x, coefficientExpr(2))) },
                expected = { x, y -> semiring.add(y, semiring.mul(x, coefficientExpr(3))) },
            ),
            Case(
                id = "y-plus-x-times-two-plus-x",
                expression = { x, y -> semiring.add(semiring.add(y, semiring.mul(x, coefficientExpr(2))), x) },
                expected = { x, y -> semiring.add(y, semiring.mul(x, coefficientExpr(3))) },
            ),
            Case(
                id = "y-plus-x-times-two-plus-x-times-three",
                expression = { x, y ->
                    semiring.add(
                        semiring.add(y, semiring.mul(x, coefficientExpr(2))),
                        semiring.mul(x, coefficientExpr(3)),
                    )
                },
                expected = { x, y -> semiring.add(y, semiring.mul(x, coefficientExpr(5))) },
            ),
        )

        cases.forEach { testCase ->
            val theorem = statement("ring-simplify-fold-monoids-${testCase.id}") {
                val x = parameter("x", scalar)
                val y = parameter("y", scalar)

                val expression = testCase.expression(x, y)
                val expected = testCase.expected(x, y)

                conclusion(expression eq expected)
                proof {
                    semiring.ring(expression, expected, coefficients)
                }
            }

            assertVerifies(theorem)
        }
    }

    @Test
    fun ringSimplifyKeepsComplexAtomFamiliesSeparated() {
        val theorem = statement("ring-simplify-keeps-complex-atom-families-separated") {
            val x = parameter("x", scalar)
            val y = parameter("y", scalar)

            val powXY = pow(x, y)
            val powYX = pow(y, x)
            val familyA1 = commutativeSemiring.mul(powXY, x)
            val familyA2 = commutativeSemiring.mul(x, powXY)
            val familyB1 = commutativeSemiring.mul(powYX, x)
            val familyB2 = commutativeSemiring.mul(x, powYX)

            val expression = commutativeSemiring.add(
                commutativeSemiring.add(familyA1, familyA2),
                commutativeSemiring.add(
                    commutativeSemiring.add(familyB1, familyB2),
                    commutativeSemiring.add(
                        commutativeSemiring.add(familyA2, familyA1),
                        commutativeSemiring.add(familyB2, familyB1),
                    ),
                ),
            )

            val normalizedFamilyA = commutativeSemiring.mul(powXY, x)
            val normalizedFamilyB = commutativeSemiring.mul(powYX, x)
            val expected = commutativeSemiring.add(
                commutativeSemiring.mul(normalizedFamilyA, coefficientExpr(4)),
                commutativeSemiring.mul(normalizedFamilyB, coefficientExpr(4)),
            )

            conclusion(expression eq expected)
            proof {
                commutativeSemiring.ring(expression, expected, coefficients)
            }
        }

        assertVerifies(theorem)
    }

    @Test
    fun ringSimplifyNormalizesBinomialDistribution() {
        val theorem = statement("ring-simplify-normalizes-binomial-distribution") {
            val a = parameter("a", scalar)
            val b = parameter("b", scalar)
            val c = parameter("c", scalar)
            val d = parameter("d", scalar)

            val left = commutativeSemiring.mul(
                commutativeSemiring.add(a, b),
                commutativeSemiring.add(c, d),
            )
            val right = commutativeSemiring.add(
                commutativeSemiring.add(
                    commutativeSemiring.mul(a, c),
                    commutativeSemiring.mul(a, d),
                ),
                commutativeSemiring.add(
                    commutativeSemiring.mul(b, c),
                    commutativeSemiring.mul(b, d),
                ),
            )

            conclusion(left eq right)
            proof {
                commutativeSemiring.ring(left, right)
            }
        }

        assertVerifies(theorem)
    }

    @Test
    fun ringFailsOnAtomSwapForNonCommutativeTheory() {
        assertFailsWith<IllegalStateException> {
            statement("ring-non-commutative-does-not-swap-atoms") {
                val x = parameter("x", scalar)
                val z = parameter("z", scalar)

                val left = semiring.mul(x, z)
                val right = semiring.mul(z, x)

                conclusion(left eq right)
                proof {
                    semiring.ring(left, right, coefficients)
                }
            }
        }
    }

    @Test
    fun ringFailsWhenNormalFormsDiffer() {
        assertFailsWith<IllegalStateException> {
            statement("ring-different-normal-forms-fail") {
                val x = parameter("x", scalar)

                val left = semiring.mul(x, coefficientExpr(2))
                val right = semiring.mul(x, coefficientExpr(3))

                conclusion(left eq right)
                proof {
                    semiring.ring(left, right, coefficients)
                }
            }
        }
    }

    @Test
    fun ringSimplifyIsIdempotentOnNormalForm() {
        val firstPass = statement("ring-simplify-idempotence-first-pass") {
            val x = parameter("x", scalar)
            val y = parameter("y", scalar)

            val repeated = semiring.mul(x, y)
            val expression = semiring.add(
                semiring.add(repeated, repeated),
                semiring.add(repeated, repeated),
            )
            val normalForm = semiring.mul(repeated, coefficientExpr(4))

            conclusion(expression eq normalForm)
            proof {
                semiring.ringSimplify(expression, coefficients)
            }
        }
        assertVerifies(firstPass)

        val secondPass = statement("ring-simplify-idempotence-second-pass") {
            val x = parameter("x", scalar)
            val y = parameter("y", scalar)

            val normalForm = semiring.mul(semiring.mul(x, y), coefficientExpr(4))

            conclusion(normalForm eq normalForm)
            proof {
                semiring.ringSimplify(normalForm, coefficients)
            }
        }
        assertVerifies(secondPass)
    }

    @Test
    fun ringSimplifyWithoutCoefficientsDoesNotFoldRepeatedTerms() {
        val theorem = statement("ring-simplify-without-coeff-keeps-x-plus-x") {
            val x = parameter("x", scalar)
            val expression = semiring.add(x, x)

            conclusion(expression eq expression)
            proof {
                semiring.ringSimplify(expression, coefficients = null)
            }
        }
        assertVerifies(theorem)

        assertFailsWith<IllegalStateException> {
            statement("ring-without-coeff-does-not-prove-x-plus-x-eq-two-x") {
                val x = parameter("x", scalar)
                val left = semiring.add(x, x)
                val right = semiring.mul(x, coefficientExpr(2))

                conclusion(left eq right)
                proof {
                    semiring.ring(left, right, coefficients = null)
                }
            }
        }
    }
}
