package dev.moklev.mathproof.fol.dsl

import dev.moklev.mathproof.core.constant
import dev.moklev.mathproof.core.function
import dev.moklev.mathproof.core.statement
import dev.moklev.mathproof.dsl.Occurences
import dev.moklev.mathproof.fol.exists
import dev.moklev.mathproof.fol.firstOrderJustificationValidators
import dev.moklev.mathproof.kernel.ProofVerifier
import dev.moklev.mathproof.kernel.StatementDefinition
import dev.moklev.mathproof.logic.assume
import dev.moklev.mathproof.logic.implies
import dev.moklev.mathproof.model.CoreSorts
import dev.moklev.mathproof.model.NamedSort
import kotlin.test.Test
import kotlin.test.assertFailsWith
import kotlin.test.assertTrue

class FirstOrderExistsIntroductionDslTest {
    private val verifier = ProofVerifier(
        externalJustificationValidators = firstOrderJustificationValidators,
        failOnWarnings = true,
    )
    private val element = NamedSort("Element")
    private val other = NamedSort("Other")
    private val p = function("P", element, returns = CoreSorts.Proposition)

    private fun assertVerifies(statement: StatementDefinition) {
        val result = verifier.verify(statement)
        assertTrue(result.isValid, result.describeIssues())
    }

    @Test
    fun introducesExistsWithDeducedSortFromMatchedStructure() {
        val x = constant("x", element)

        val theorem = statement("exists-intro-deduced-sort") {
            val px = premise(p(x))
            conclusion(exists("u", element) { p(it) })
            proof {
                val givenPx = given(px)
                givenPx.introduceExists(
                    witness = x,
                    variableName = "u",
                )
            }
        }

        assertVerifies(theorem)
    }

    @Test
    fun introducesExistsWithSelectedOccurrences() {
        val x = constant("x", element)

        val theorem = statement("exists-intro-first-occurrence") {
            val px = premise(p(x) implies p(x))
            conclusion(exists("u", element) { p(it) implies p(x) })
            proof {
                val givenPx = given(px)
                givenPx.introduceExists(
                    x,
                    Occurences.First,
                    "u",
                )
            }
        }

        assertVerifies(theorem)
    }

    @Test
    fun introducesExistsInsideAssumptionScope() {
        val x = constant("x", element)

        val theorem = statement("exists-intro-scoped") {
            conclusion(p(x) implies exists("u", element) { p(it) })
            proof {
                assume(p(x)) { assumption ->
                    assumption.introduceExists(
                        witness = x,
                        variableName = "u",
                    )
                }
            }
        }

        assertVerifies(theorem)
    }

    @Test
    fun rejectsExplicitSortThatDoesNotMatchMatchedStructure() {
        val x = constant("x", element)

        val error = assertFailsWith<IllegalArgumentException> {
            statement("exists-intro-explicit-sort-mismatch") {
                val px = premise(p(x))
                conclusion(exists("u", element) { p(it) })
                proof {
                    val givenPx = given(px)
                    givenPx.introduceExists(
                        witness = x,
                        variableName = "u",
                        sort = other,
                    )
                }
            }
        }

        assertTrue(error.message!!.contains("selected witness occurrences have sort"))
    }
}
