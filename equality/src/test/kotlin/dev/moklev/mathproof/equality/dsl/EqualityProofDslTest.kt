package dev.moklev.mathproof.equality.dsl

import dev.moklev.mathproof.core.constant
import dev.moklev.mathproof.core.statement
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

class EqualityProofDslTest {
    private val verifier = ProofVerifier(failOnWarnings = true)

    private fun assertVerifies(statement: StatementDefinition) {
        val result = verifier.verify(statement)
        assertTrue(result.isValid, result.describeIssues())
    }

    @Test
    fun flipsEqualityAtTopLevelProofBuilder() {
        val scalar = NamedSort("Scalar")
        val x = constant("x", scalar)
        val y = constant("y", scalar)

        val theorem = statement("flip-eq-top-level") {
            val xy = premise(x eq y)
            conclusion(y eq x)
            proof {
                val givenXy = given(xy)
                givenXy.flipEq()
            }
        }

        assertVerifies(theorem)
    }

    @Test
    fun flipsEqualityInsideAssumptionScope() {
        val scalar = NamedSort("Scalar")
        val x = constant("x", scalar)
        val y = constant("y", scalar)

        val theorem = statement("flip-eq-scoped") {
            conclusion((x eq y) implies (y eq x))
            proof {
                assume(x eq y) { assumption ->
                    assumption.flipEq()
                }
            }
        }

        assertVerifies(theorem)
    }

    @Test
    fun rejectsFlipEqOnNonEqualityClaim() {
        val p = constant("p", CoreSorts.Proposition)

        val error = assertFailsWith<IllegalArgumentException> {
            statement("flip-eq-rejects-non-equality") {
                val premiseP = premise(p)
                conclusion(p)
                proof {
                    val givenP = given(premiseP)
                    givenP.flipEq()
                }
            }
        }

        assertTrue(error.message!!.contains("equality-symmetric"))
    }
}
