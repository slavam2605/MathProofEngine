package dev.moklev.mathproof.equality.dsl

import dev.moklev.mathproof.core.constant
import dev.moklev.mathproof.core.function
import dev.moklev.mathproof.core.statement
import dev.moklev.mathproof.dsl.Occurences
import dev.moklev.mathproof.equality.eq
import dev.moklev.mathproof.kernel.ProofVerifier
import dev.moklev.mathproof.kernel.StatementDefinition
import dev.moklev.mathproof.logic.assume
import dev.moklev.mathproof.logic.implies
import dev.moklev.mathproof.model.CoreSorts
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
