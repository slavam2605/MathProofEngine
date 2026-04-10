package dev.moklev.mathproof.logic

import dev.moklev.mathproof.core.constant
import dev.moklev.mathproof.core.statement
import dev.moklev.mathproof.kernel.Fact
import dev.moklev.mathproof.kernel.ProofVerifier
import dev.moklev.mathproof.kernel.StatementDefinition
import dev.moklev.mathproof.kernel.prettyPrint
import dev.moklev.mathproof.model.CoreSorts
import dev.moklev.mathproof.testutils.discoverStatementsChecked
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertFailsWith
import kotlin.test.assertTrue

class LogicProofVerifierTest {
    private val verifier = ProofVerifier(failOnWarnings = true)

    private fun assertVerifies(statement: StatementDefinition) {
        val result = verifier.verify(statement)
        assertTrue(result.isValid, result.describeIssues())
    }

    private fun assertAllDiscoveredStatementsVerify(holder: Any) {
        discoverStatementsChecked(holder).forEach { statement ->
            assertVerifies(statement)
        }
    }

    @Test
    fun verifiesDerivedLogicLibraryStatements() {
        assertAllDiscoveredStatementsVerify(LogicLibrary)
    }

    @Test
    fun prettyPrintsStatementStructureAndProofSteps() {
        val rendered = LogicLibrary.implicationIdentity.prettyPrint()

        assertTrue(rendered.contains("implication-identity"))
        assertTrue(rendered.contains("parameters:\n- p: Proposition"))
        assertTrue(rendered.contains("premises:\n- none"))
        assertTrue(rendered.contains("conclusion: p -> p"))
        assertTrue(rendered.contains("1. p -> (p -> p) -> p (hilbert-a1)"))
        assertTrue(rendered.contains("4. p -> p (chain-modus-ponens-2 1, 2, 3)"))
    }

    @Test
    fun rendersLogicExpressionsWithRegisteredNotation() {
        val p = constant("p", CoreSorts.Proposition)
        val q = constant("q", CoreSorts.Proposition)
        val r = constant("r", CoreSorts.Proposition)

        assertEquals("p -> q", (p implies q).toString())
        assertEquals("p and q", (p and q).toString())
        assertEquals("p or q", (p or q).toString())
        assertEquals("!p", (!p).toString())
        assertEquals("p -> q -> r", (p implies (q implies r)).toString())
        assertEquals("(p -> q) -> r", ((p implies q) implies r).toString())
        assertEquals("p and q and r", ((p and q) and r).toString())
        assertEquals("p and (q and r)", (p and (q and r)).toString())
        assertEquals("p or q and r", (p or (q and r)).toString())
        assertEquals("(p or q) and r", ((p or q) and r).toString())
    }

    @Test
    fun explainsWhenAPremiseStepFailedEarlier() {
        val p = constant("p", CoreSorts.Proposition)
        val q = constant("q", CoreSorts.Proposition)

        val broken = statement("failed-step-cascade") {
            val pPremise = premise(p)
            conclusion(p)
            proof {
                val givenP = given(pPremise)
                val bad = infer("bad", LogicAxioms.modusPonens(p, q), givenP)
                infer("after-bad", LogicAxioms.modusPonens(q, p), bad, givenP)
            }
        }

        val result = verifier.verify(broken)

        assertFalse(result.isValid)
        assertTrue(result.issues.any { it.message.contains("failed earlier") })
        assertFalse(result.issues.any { it.message.contains("Unknown premise step 'bad'") })
    }

    @Test
    fun rejectsDetachedFactsInsideInference() {
        val p = constant("p", CoreSorts.Proposition)
        val q = constant("q", CoreSorts.Proposition)
        var foreignImplication: Fact? = null

        statement("source-proof") {
            val pqPremise = premise("pq", p implies q)
            conclusion(p implies q)
            proof {
                foreignImplication = given(pqPremise)
            }
        }

        assertFailsWith<IllegalArgumentException> {
            statement("foreign-fact-proof") {
                val pPremise = premise("p", p)
                conclusion(q)
                proof {
                    val givenP = given(pPremise)
                    infer("q", LogicAxioms.modusPonens(p, q), givenP, foreignImplication!!)
                }
            }
        }
    }

    @Test
    fun infersModusPonensParametersFromPremisesInProofBuilder() {
        val p = constant("p", CoreSorts.Proposition)
        val q = constant("q", CoreSorts.Proposition)

        val theorem = statement("auto-parameter-modus-ponens") {
            val pPremise = premise("p", p)
            val pqPremise = premise("pq", p implies q)
            conclusion(q)
            proof {
                val givenP = given(pPremise)
                val givenPq = given(pqPremise)
                infer(LogicAxioms.modusPonens, givenP, givenPq)
            }
        }

        assertVerifies(theorem)
    }

    @Test
    fun rejectsAutoMpChainWhenAParameterCannotBeDerived() {
        val p = constant("p", CoreSorts.Proposition)
        val q = constant("q", CoreSorts.Proposition)

        val error = assertFailsWith<IllegalArgumentException> {
            statement("auto-parameter-underconstrained-chain") {
                val notPPremise = premise(!p)
                val pPremise = premise(p)
                conclusion(q)
                proof {
                    val givenNotP = given(notPPremise)
                    val givenP = given(pPremise)
                    applyByMpChain(LogicLibrary.exFalso, givenNotP, givenP)
                }
            }
        }

        assertTrue(error.message!!.contains("unresolved parameter"))
        assertTrue(error.message!!.contains("q"))
    }
}
