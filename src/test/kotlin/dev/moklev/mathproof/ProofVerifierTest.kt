package dev.moklev.mathproof

import dev.moklev.mathproof.core.constant
import dev.moklev.mathproof.core.functionSort
import dev.moklev.mathproof.core.sortVariable
import dev.moklev.mathproof.core.statement
import dev.moklev.mathproof.examples.SampleProofs
import dev.moklev.mathproof.kernel.*
import dev.moklev.mathproof.logic.LogicAxioms
import dev.moklev.mathproof.logic.LogicLibrary
import dev.moklev.mathproof.logic.and
import dev.moklev.mathproof.logic.implies
import dev.moklev.mathproof.logic.not
import dev.moklev.mathproof.logic.or
import dev.moklev.mathproof.model.CoreSorts
import dev.moklev.mathproof.testutils.discoverStatements
import kotlin.test.*

class ProofVerifierTest {
    private val verifier = ProofVerifier(
        failOnWarnings = true,
    )

    private fun assertVerifies(statement: StatementDefinition) {
        val result = verifier.verify(statement)
        assertTrue(result.isValid, result.describeIssues())
    }

    private fun assertAllDiscoveredStatementsVerify(holder: Any) {
        discoverStatements(holder).forEach { statement ->
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
    fun prettyPrintsPremiseReferencesByStepNumber() {
        val rendered = SampleProofs.commutedConjunction.prettyPrint()

        assertTrue(rendered.contains("1. p and q (premise 1)"))
        assertTrue(rendered.contains("2. q (conjunction-right-projection 1)"))
        assertTrue(rendered.contains("3. p (conjunction-left-projection 1)"))
        assertTrue(rendered.contains("4. q and p (conjunction-from-premises 2, 3)"))
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
    fun keepsFallbackRenderingForUnknownFunctions() {
        val p = constant("p", CoreSorts.Proposition)
        val q = constant("q", CoreSorts.Proposition)
        val custom = constant(
            "custom",
            functionSort(CoreSorts.Proposition, CoreSorts.Proposition, returns = CoreSorts.Proposition),
        )

        assertEquals("custom(p, q)", custom(p, q).toString())
    }

    @Test
    fun verifiesDiscoveredSampleProofs() {
        assertAllDiscoveredStatementsVerify(SampleProofs)
    }

    @Test
    fun rejectsUnknownPremiseReference() {
        val p = constant("p", CoreSorts.Proposition)
        val broken = statement("broken-premise-reference") {
            conclusion(p)
            proof { }
        }.copy(
            support = ProofProvided(
                ProofScript(
                    listOf(
                        ProofStep(
                            label = "ghost",
                            claim = p,
                            justification = PremiseReference(0),
                        ),
                    ),
                ),
            ),
        )

        val result = verifier.verify(broken)
        assertFalse(result.isValid)
        assertTrue(result.issues.any { it.message.contains("does not exist") })
    }

    @Test
    fun rejectsDuplicateLabelsEvenWhenProofScriptIsBuiltManually() {
        val p = constant("p", CoreSorts.Proposition)
        val broken = statement("duplicate-labels") {
            premise(p)
            conclusion(p)
            proof { }
        }.copy(
            support = ProofProvided(
                ProofScript(
                    listOf(
                        ProofStep("dup", p, PremiseReference(0)),
                        ProofStep("dup", p, PremiseReference(0)),
                    ),
                ),
            ),
        )

        val result = verifier.verify(broken)
        assertFalse(result.isValid)
        assertTrue(result.issues.any { it.message.contains("Duplicate proof step label") })
    }

    @Test
    fun reportsStatementLevelIssuesWithoutFakeStepZero() {
        val invalidConclusion = constant(
            "f",
            functionSort(CoreSorts.Proposition, returns = CoreSorts.Proposition),
        )
        val broken = StatementDefinition(
            name = "non-proposition-conclusion",
            parameters = emptyList(),
            premises = emptyList(),
            conclusion = invalidConclusion,
            support = AssumedTrue(),
        )

        val result = verifier.verify(broken)

        assertFalse(result.isValid)
        assertTrue(result.describeIssues().contains("statement: Conclusion"))
        assertFalse(result.describeIssues().contains("step 0"))
    }

    @Test
    fun supportsHigherOrderFunctionSorts() {
        val s = sortVariable("S")
        val endomorphism = functionSort(s, returns = s)
        val higherOrder = functionSort(endomorphism, returns = s)

        assertEquals("(S -> S) -> S", higherOrder.toString())
    }

    @Test
    fun rejectsPremiseHandlesFromAnotherStatement() {
        val p = constant("p", CoreSorts.Proposition)
        var foreignPremise: StatementPremise? = null

        statement("source") {
            foreignPremise = premise("p", p)
            conclusion(p)
            assumed()
        }

        assertFailsWith<IllegalArgumentException> {
            statement("target") {
                conclusion(p)
                proof {
                    given(foreignPremise!!)
                }
            }
        }
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
}
