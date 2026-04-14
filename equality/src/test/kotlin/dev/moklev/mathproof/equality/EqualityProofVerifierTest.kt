package dev.moklev.mathproof.equality

import dev.moklev.mathproof.core.constant
import dev.moklev.mathproof.core.function
import dev.moklev.mathproof.core.statement
import dev.moklev.mathproof.kernel.ProofVerifier
import dev.moklev.mathproof.kernel.StatementDefinition
import dev.moklev.mathproof.kernel.auto
import dev.moklev.mathproof.logic.applyMp
import dev.moklev.mathproof.model.NamedSort
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFailsWith
import kotlin.test.assertTrue

class EqualityProofVerifierTest {
    private val verifier = ProofVerifier(failOnWarnings = true)

    private fun assertVerifies(statement: StatementDefinition) {
        val result = verifier.verify(statement)
        assertTrue(result.isValid, result.describeIssues())
    }

    @Test
    fun rendersEqualityExpressionsWithRegisteredNotation() {
        val scalar = NamedSort("Scalar")
        val x = constant("x", scalar)
        val y = constant("y", scalar)

        assertEquals("x = y", (x eq y).toString())
    }

    @Test
    fun infersParametersForApplyByMpChainAtTopLevel() {
        val carrier = NamedSort("Carrier")
        val a = constant("a", carrier)
        val b = constant("b", carrier)

        val theorem = statement("auto-parameter-symmetry-chain") {
            val abPremise = premise(a eq b)
            conclusion(b eq a)
            proof {
                val givenAb = given(abPremise)
                applyMp(EqualityLibrary.symmetry, givenAb)
            }
        }

        assertVerifies(theorem)
    }

    @Test
    fun infersCongruenceFromFactWhenFunctionIsProvidedInArgs() {
        val carrier = NamedSort("Carrier")
        val f = function("f", carrier, returns = carrier)
        val a = constant("a", carrier)
        val b = constant("b", carrier)

        val theorem = statement("auto-parameter-congruence-with-explicit-function-arg") {
            val abPremise = premise(a eq b)
            conclusion(f(a) eq f(b))
            proof {
                val givenAb = given(abPremise)
                applyMp(
                    EqualityLibrary.congruence(f, auto(), auto()),
                    givenAb,
                )
            }
        }

        assertVerifies(theorem)
    }

    @Test
    fun rejectsArgsThatConflictWithDerivedBindings() {
        val carrier = NamedSort("Carrier")
        val a = constant("a", carrier)
        val b = constant("b", carrier)

        val error = assertFailsWith<IllegalArgumentException> {
            statement("auto-parameter-conflicting-args") {
                val abPremise = premise(a eq b)
                conclusion(b eq a)
                proof {
                    val givenAb = given(abPremise)
                    applyMp(
                        EqualityLibrary.symmetry(b, auto()),
                        givenAb,
                    )
                }
            }
        }

        assertTrue(error.message!!.contains("expression mismatch"))
    }
}
