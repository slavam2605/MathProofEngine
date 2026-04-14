package dev.moklev.mathproof.logic

import dev.moklev.mathproof.core.constant
import dev.moklev.mathproof.core.statement
import dev.moklev.mathproof.kernel.ProofVerifier
import dev.moklev.mathproof.kernel.StatementDefinition
import dev.moklev.mathproof.kernel.auto
import dev.moklev.mathproof.model.CoreSorts
import kotlin.test.Test
import kotlin.test.assertFailsWith
import kotlin.test.assertTrue

class ScopedProofDslTest {
    private val verifier = ProofVerifier(failOnWarnings = true)

    private fun assertVerifies(statement: StatementDefinition) {
        val result = verifier.verify(statement)
        assertTrue(result.isValid, result.describeIssues())
    }

    @Test
    fun verifiesDerivedClaviusStatement() {
        assertVerifies(LogicLibrary.clavius)
    }

    @Test
    fun dischargesSimpleIdentityAssumption() {
        val p = constant("p", CoreSorts.Proposition)

        val theorem = statement("scoped-assume-identity") {
            conclusion(p implies p)
            proof {
                assume(p) { assumption ->
                    given(assumption)
                }
            }
        }

        assertVerifies(theorem)
    }

    @Test
    fun rejectsEmptyAssumeBlock() {
        val p = constant("p", CoreSorts.Proposition)

        val error = assertFailsWith<IllegalArgumentException> {
            statement("scoped-assume-empty-block") {
                conclusion(p implies p)
                proof {
                    assume(p) { _ -> }
                }
            }
        }

        assertTrue(error.message!!.contains("must contain at least one proof step"))
    }

    @Test
    fun dischargesModusPonensInsideAssumptionBlock() {
        val p = constant("p", CoreSorts.Proposition)
        val q = constant("q", CoreSorts.Proposition)

        val theorem = statement("scoped-assume-mp") {
            val pqPremise = premise(p implies q)
            conclusion(p implies q)
            proof {
                val givenPq = given(pqPremise)
                assume(p) { assumption ->
                    val givenAssumption = given(assumption)
                    val liftedPremise = given(givenPq)
                    infer(LogicAxioms.modusPonens(p, q), givenAssumption, liftedPremise)
                }
            }
        }

        assertVerifies(theorem)
    }

    @Test
    fun infersModusPonensParametersInsideAssumptionBlock() {
        val p = constant("p", CoreSorts.Proposition)
        val q = constant("q", CoreSorts.Proposition)

        val theorem = statement("scoped-assume-mp-auto-parameters") {
            val pqPremise = premise(p implies q)
            conclusion(p implies q)
            proof {
                val givenPq = given(pqPremise)
                assume(p) { assumption ->
                    val givenAssumption = given(assumption)
                    val liftedPremise = given(givenPq)
                    infer(LogicAxioms.modusPonens, givenAssumption, liftedPremise)
                }
            }
        }

        assertVerifies(theorem)
    }

    @Test
    fun supportsScopedInferenceWithExplicitArgsPlusDerivedBindings() {
        val p = constant("p", CoreSorts.Proposition)
        val q = constant("q", CoreSorts.Proposition)

        val theorem = statement("scoped-assume-mp-with-explicit-arg") {
            val pqPremise = premise(p implies q)
            conclusion(p implies q)
            proof {
                val givenPq = given(pqPremise)
                assume(p) { assumption ->
                    val givenAssumption = given(assumption)
                    val liftedPremise = given(givenPq)
                    infer(
                        LogicAxioms.modusPonens(auto(), q),
                        givenAssumption,
                        liftedPremise,
                    )
                }
            }
        }

        assertVerifies(theorem)
    }

    @Test
    fun appliesTheoremByMpChainAtTopLevel() {
        val p = constant("p", CoreSorts.Proposition)
        val q = constant("q", CoreSorts.Proposition)

        val theorem = statement("apply-by-mp-chain-top-level") {
            val pPremise = premise(p)
            val notPPremise = premise(!p)
            conclusion(q)
            proof {
                val givenP = given(pPremise)
                val givenNotP = given(notPPremise)
                applyMp(LogicLibrary.exFalso(p, q), givenNotP, givenP)
            }
        }

        assertVerifies(theorem)
    }

    @Test
    fun appliesTheoremByMpChainInsideAssumeBlock() {
        val p = constant("p", CoreSorts.Proposition)

        val theorem = statement("apply-by-mp-chain-inside-assume") {
            conclusion(p implies p)
            proof {
                assume(p) { assumption ->
                    val givenP = given(assumption)
                    applyMp(LogicLibrary.implicationIdentity(p), givenP)
                }
            }
        }

        assertVerifies(theorem)
    }

    @Test
    fun infersApplyByMpChainParametersInsideAssumeBlock() {
        val p = constant("p", CoreSorts.Proposition)

        val theorem = statement("apply-by-mp-chain-inside-assume-auto-parameters") {
            conclusion(p implies p)
            proof {
                assume(p) { assumption ->
                    val givenP = given(assumption)
                    applyMp(LogicLibrary.implicationIdentity, givenP)
                }
            }
        }

        assertVerifies(theorem)
    }

    @Test
    fun supportsNestedAssumptionsWithIterativeDischarge() {
        val p = constant("p", CoreSorts.Proposition)
        val q = constant("q", CoreSorts.Proposition)

        val theorem = statement("nested-scoped-assume") {
            conclusion(p implies (q implies p))
            proof {
                assume(p) { assumption ->
                    val givenP = given(assumption)
                    assume(q) { _ ->
                        given(givenP)
                    }
                }
            }
        }

        assertVerifies(theorem)
    }

    @Test
    fun contradictionSugarProducesTargetClaim() {
        val p = constant("p", CoreSorts.Proposition)

        val theorem = statement("scoped-contradiction-with-premise") {
            val premiseP = premise(p)
            conclusion(p)
            proof {
                val givenP = given(premiseP)
                contradiction(assume = !p) { _ ->
                    given(givenP)
                }
            }
        }

        assertVerifies(theorem)
    }

    @Test
    fun rejectsAssumptionDependentNonModusPonensStepInScopedCompiler() {
        val p = constant("p", CoreSorts.Proposition)
        val q = constant("q", CoreSorts.Proposition)
        val implicationFromConsequent = statement("test-implication-from-consequent") {
            val pPremise = premise(p)
            conclusion(q implies p)
            proof {
                val givenP = given(pPremise)
                val lift = infer(LogicAxioms.hilbertAxiom1(p, q))
                infer(LogicAxioms.modusPonens(p, q implies p), givenP, lift)
            }
        }

        val error = assertFailsWith<IllegalArgumentException> {
            statement("scoped-assume-rejects-non-mp-dependent-step") {
                conclusion(p implies (q implies p))
                proof {
                    assume(p) { assumption ->
                        val givenAssumption = given(assumption)
                        infer(implicationFromConsequent(), givenAssumption)
                    }
                }
            }
        }

        assertTrue(error.message!!.contains("supports assumption-dependent steps only through modus ponens"))
    }

    @Test
    fun contradictionRequiresNegatedAssumption() {
        val p = constant("p", CoreSorts.Proposition)

        val error = assertFailsWith<IllegalArgumentException> {
            statement("scoped-contradiction-requires-negated-assumption") {
                conclusion(p)
                proof {
                    contradiction(assume = p) { assumption ->
                        given(assumption)
                    }
                }
            }
        }

        assertTrue(error.message!!.contains("requires a negated assumption"))
    }
}
