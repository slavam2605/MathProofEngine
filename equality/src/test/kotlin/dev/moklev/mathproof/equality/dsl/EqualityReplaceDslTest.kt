package dev.moklev.mathproof.equality.dsl

import dev.moklev.mathproof.core.constant
import dev.moklev.mathproof.core.function
import dev.moklev.mathproof.core.functionSort
import dev.moklev.mathproof.core.lambda
import dev.moklev.mathproof.core.statement
import dev.moklev.mathproof.dsl.Occurences
import dev.moklev.mathproof.equality.eq
import dev.moklev.mathproof.kernel.ProofVerifier
import dev.moklev.mathproof.kernel.StatementDefinition
import dev.moklev.mathproof.logic.assume
import dev.moklev.mathproof.logic.implies
import dev.moklev.mathproof.model.CoreSorts
import dev.moklev.mathproof.dsl.ExprPath
import dev.moklev.mathproof.dsl.ExprPathStep
import dev.moklev.mathproof.model.NamedSort
import kotlin.test.Test
import kotlin.test.assertFailsWith
import kotlin.test.assertTrue

class EqualityReplaceDslTest {
    private val verifier = ProofVerifier(failOnWarnings = true)

    private val scalar = NamedSort("Scalar")
    private val x = constant("x", scalar)
    private val y = constant("y", scalar)
    private val zero = constant("zero", scalar)
    private val mul = function("mul", scalar, scalar, returns = scalar)

    private val yTimesZero = mul(y, zero)
    private val baseClaim = (mul(mul(x, y), zero) eq zero)
    private val rewriteFactClaim = (zero eq yTimesZero)

    private fun assertVerifies(statement: StatementDefinition) {
        val result = verifier.verify(statement)
        assertTrue(result.isValid, result.describeIssues())
    }

    @Test
    fun replacesAllOccurrencesByDefault() {
        val theorem = statement("replace-all-occurrences") {
            val base = premise(baseClaim)
            val rewrite = premise(rewriteFactClaim)

            conclusion(mul(mul(x, y), yTimesZero) eq yTimesZero)
            proof {
                val baseFact = given(base)
                val rewriteFact = given(rewrite)
                baseFact.replace(using = rewriteFact)
            }
        }

        assertVerifies(theorem)
    }

    @Test
    fun replacesFirstAndLastOccurrence() {
        val theoremFirst = statement("replace-first-occurrence") {
            val base = premise(baseClaim)
            val rewrite = premise(rewriteFactClaim)

            conclusion(mul(mul(x, y), yTimesZero) eq zero)
            proof {
                val baseFact = given(base)
                val rewriteFact = given(rewrite)
                baseFact.replace(using = rewriteFact, at = Occurences.First)
            }
        }
        assertVerifies(theoremFirst)

        val theoremLast = statement("replace-last-occurrence") {
            val base = premise(baseClaim)
            val rewrite = premise(rewriteFactClaim)

            conclusion(mul(mul(x, y), zero) eq yTimesZero)
            proof {
                val baseFact = given(base)
                val rewriteFact = given(rewrite)
                baseFact.replace(using = rewriteFact, at = Occurences.Last)
            }
        }
        assertVerifies(theoremLast)
    }

    @Test
    fun replacesOnlyRequestedOccurrences() {
        val theorem = statement("replace-selected-occurrences") {
            val base = premise(baseClaim)
            val rewrite = premise(rewriteFactClaim)

            conclusion(mul(mul(x, y), yTimesZero) eq zero)
            proof {
                val baseFact = given(base)
                val rewriteFact = given(rewrite)
                baseFact.replace(
                    using = rewriteFact,
                    at = Occurences.Only(0),
                )
            }
        }

        assertVerifies(theorem)
    }

    @Test
    fun replacesInsideAssumptionScopeUsingOuterFact() {
        val theorem = statement("replace-scoped-using-outer-fact") {
            val rewrite = premise(rewriteFactClaim)

            conclusion(baseClaim implies (mul(mul(x, y), zero) eq yTimesZero))
            proof {
                val rewriteFact = given(rewrite)
                assume(baseClaim) { baseScoped ->
                    baseScoped.replace(using = rewriteFact, at = Occurences.Last)
                }
            }
        }

        assertVerifies(theorem)
    }

    @Test
    fun replacesLambdaSubexpressionOccurrences() {
        val nat = NamedSort("Nat")
        val zeroNat = constant("zeroNat", nat)
        val ss0 = constant("SS0", nat)
        val mulNat = function("mulNat", nat, nat, returns = nat)
        val sumNat = function(
            "sumNat",
            nat,
            functionSort(nat, returns = nat),
            returns = nat,
        )
        val idLambda = lambda("i", nat) { i -> i }
        val sumExpr = sumNat(zeroNat, idLambda)

        val theorem = statement("replace-lambda-subexpression-occurrence") {
            val base = premise(mulNat(ss0, sumExpr) eq mulNat(ss0, sumExpr))
            val rewrite = premise(sumExpr eq zeroNat)

            conclusion(mulNat(ss0, zeroNat) eq mulNat(ss0, sumExpr))
            proof {
                val baseFact = given(base)
                val rewriteFact = given(rewrite)
                baseFact.replace(using = rewriteFact, at = Occurences.First)
            }
        }

        assertVerifies(theorem)
    }

    @Test
    fun replacesOnlyOccurrenceAtGivenPath() {
        val firstOccurrence = mul(y, zero)
        val secondOccurrence = mul(y, zero)
        val baseExpression = mul(firstOccurrence, secondOccurrence)
        val exactRewriteFact = (yTimesZero eq x)
        val secondOccurrencePath = ExprPath.Root /
            ExprPathStep.Function /
            ExprPathStep.BinRight /
            ExprPathStep.BinRight

        val theorem = statement("replace-occurrence-at-given-path") {
            val base = premise(baseExpression eq zero)
            val rewrite = premise(exactRewriteFact)

            conclusion(mul(firstOccurrence, x) eq zero)
            proof {
                val baseFact = given(base)
                val rewriteFact = given(rewrite)
                baseFact.replace(
                    using = rewriteFact,
                    at = Occurences.Path(secondOccurrencePath),
                )
            }
        }

        assertVerifies(theorem)
    }

    @Test
    fun rejectsPathWhenItDoesNotPointToTargetOccurrence() {
        val firstOccurrence = mul(y, zero)
        val secondOccurrence = mul(y, zero)
        val baseExpression = mul(firstOccurrence, secondOccurrence)
        val exactRewriteFact = (yTimesZero eq x)
        val rhsPath = ExprPath.Root / ExprPathStep.BinRight

        val error = assertFailsWith<IllegalArgumentException> {
            statement("replace-path-does-not-point-to-target-occurrence") {
                val base = premise(baseExpression eq zero)
                val rewrite = premise(exactRewriteFact)

                conclusion(baseExpression eq zero)
                proof {
                    val baseFact = given(base)
                    val rewriteFact = given(rewrite)
                    baseFact.replace(
                        using = rewriteFact,
                        at = Occurences.Path(rhsPath),
                    )
                }
            }
        }

        assertTrue(error.message!!.contains("not an occurrence"))
    }

    @Test
    fun rejectsReplaceWhenUsingClaimIsNotEquality() {
        val proposition = constant("p", CoreSorts.Proposition)

        val error = assertFailsWith<IllegalArgumentException> {
            statement("replace-rejects-non-equality-using-claim") {
                val base = premise(proposition)
                val nonEquality = premise(proposition implies proposition)

                conclusion(proposition)
                proof {
                    val baseFact = given(base)
                    val invalidUsing = given(nonEquality)
                    baseFact.replace(using = invalidUsing)
                }
            }
        }

        assertTrue(error.message!!.contains("expects 'using' to be an equality fact"))
    }
}
