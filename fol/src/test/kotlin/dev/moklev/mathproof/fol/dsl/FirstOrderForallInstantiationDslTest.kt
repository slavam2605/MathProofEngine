package dev.moklev.mathproof.fol.dsl

import dev.moklev.mathproof.core.constant
import dev.moklev.mathproof.core.function
import dev.moklev.mathproof.core.statement
import dev.moklev.mathproof.fol.forall
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

class FirstOrderForallInstantiationDslTest {
    private val verifier = ProofVerifier(
        externalJustificationValidators = firstOrderJustificationValidators,
        failOnWarnings = true,
    )
    private val element = NamedSort("Element")

    private fun assertVerifies(statement: StatementDefinition) {
        val result = verifier.verify(statement)
        assertTrue(result.isValid, result.describeIssues())
    }

    @Test
    fun instantiatesForallAtTopLevel() {
        val p = function("P", element, returns = CoreSorts.Proposition)
        val a = constant("a", element)

        val theorem = statement("dsl-forall-instantiation-top-level") {
            val premiseAll = premise(forall("x", element) { p(it) })
            conclusion(p(a))
            proof {
                val universal = given(premiseAll)
                universal.instantiateForall(a)
            }
        }

        assertVerifies(theorem)
    }

    @Test
    fun instantiatesForallInsideAssumptionScope() {
        val p = function("P", element, returns = CoreSorts.Proposition)
        val a = constant("a", element)

        val theorem = statement("dsl-forall-instantiation-scoped") {
            conclusion(forall("x", element) { p(it) } implies p(a))
            proof {
                assume(forall("x", element) { p(it) }) { universal ->
                    universal.instantiateForall(a)
                }
            }
        }

        assertVerifies(theorem)
    }

    @Test
    fun rejectsInstantiationWhenClaimIsNotForall() {
        val p = constant("p", CoreSorts.Proposition)
        val a = constant("a", element)

        val error = assertFailsWith<IllegalArgumentException> {
            statement("dsl-forall-instantiation-rejects-non-forall") {
                val premiseP = premise(p)
                conclusion(p)
                proof {
                    val givenP = given(premiseP)
                    givenP.instantiateForall(a)
                }
            }
        }

        assertTrue(error.message!!.contains("forall("))
    }
}
