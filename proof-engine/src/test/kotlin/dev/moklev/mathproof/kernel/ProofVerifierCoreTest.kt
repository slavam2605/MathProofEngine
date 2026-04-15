package dev.moklev.mathproof.kernel

import dev.moklev.mathproof.core.*
import dev.moklev.mathproof.model.CoreSorts
import kotlin.test.*

class ProofVerifierCoreTest {
    private val verifier = ProofVerifier(failOnWarnings = true)

    private fun assertVerifies(statement: StatementDefinition) {
        val result = verifier.verify(statement)
        assertTrue(result.isValid, result.describeIssues())
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
    fun acceptsPremiseReferenceWhenClaimIsBetaEquivalent() {
        val p = constant("p", CoreSorts.Proposition)
        val idRedex = lambda("x", CoreSorts.Proposition) { x -> x }(p)

        val statement = StatementDefinition(
            name = "manual-beta-premise-reference",
            parameters = emptyList(),
            premises = listOf(idRedex),
            conclusion = p,
            support = ProofProvided(
                proof = ProofScript(
                    steps = listOf(
                        ProofStep(
                            label = "step1",
                            claim = p,
                            justification = PremiseReference(premiseIndex = 0),
                        ),
                    ),
                ),
            ),
        )

        assertVerifies(statement)
    }

    @Test
    fun acceptsStatementApplicationWhenConclusionIsBetaEquivalent() {
        val p = constant("p", CoreSorts.Proposition)
        val idRedex = lambda("x", CoreSorts.Proposition) { x -> x }(p)

        val lemma = StatementDefinition(
            name = "manual-beta-conclusion-lemma",
            parameters = emptyList(),
            premises = emptyList(),
            conclusion = idRedex,
            support = AssumedTrue("trusted for verifier normalization check"),
        )
        val statement = StatementDefinition(
            name = "manual-beta-conclusion-consumer",
            parameters = emptyList(),
            premises = emptyList(),
            conclusion = p,
            support = ProofProvided(
                proof = ProofScript(
                    steps = listOf(
                        ProofStep(
                            label = "step1",
                            claim = p,
                            justification = StatementApplication(
                                statement = lemma,
                                arguments = emptyList(),
                                premiseLabels = emptyList(),
                            ),
                        ),
                    ),
                ),
            ),
        )

        assertVerifies(statement)
    }

    @Test
    fun rejectsUnknownPremiseReference() {
        val p = constant("p", CoreSorts.Proposition)
        val base = statement("broken-premise-reference") {
            conclusion(p)
            proof { }
        }
        val broken = StatementDefinition(
            name = base.name,
            parameters = base.parameters,
            premises = base.premises,
            conclusion = base.conclusion,
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
            instantiationCheck = base.instantiationCheck,
        )

        val result = verifier.verify(broken)
        assertFalse(result.isValid)
        assertTrue(result.issues.any { it.message.contains("does not exist") })
    }

    @Test
    fun rejectsDuplicateLabelsEvenWhenProofScriptIsBuiltManually() {
        val p = constant("p", CoreSorts.Proposition)
        val base = statement("duplicate-labels") {
            premise(p)
            conclusion(p)
            proof { }
        }
        val broken = StatementDefinition(
            name = base.name,
            parameters = base.parameters,
            premises = base.premises,
            conclusion = base.conclusion,
            support = ProofProvided(
                ProofScript(
                    listOf(
                        ProofStep("dup", p, PremiseReference(0)),
                        ProofStep("dup", p, PremiseReference(0)),
                    ),
                ),
            ),
            instantiationCheck = base.instantiationCheck,
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
}
