package dev.moklev.mathproof.fol

import dev.moklev.mathproof.core.constant
import dev.moklev.mathproof.core.function
import dev.moklev.mathproof.core.functionSort
import dev.moklev.mathproof.core.lambda
import dev.moklev.mathproof.core.statement
import dev.moklev.mathproof.kernel.ArbitraryVariable
import dev.moklev.mathproof.kernel.PremiseReference
import dev.moklev.mathproof.kernel.ProofVerifier
import dev.moklev.mathproof.kernel.ProofProvided
import dev.moklev.mathproof.kernel.ProofScript
import dev.moklev.mathproof.kernel.ProofStep
import dev.moklev.mathproof.kernel.StatementDefinition
import dev.moklev.mathproof.logic.LogicAxioms
import dev.moklev.mathproof.logic.LogicLibrary
import dev.moklev.mathproof.logic.applyByMpChain
import dev.moklev.mathproof.logic.assume
import dev.moklev.mathproof.logic.and
import dev.moklev.mathproof.logic.implies
import dev.moklev.mathproof.logic.not
import dev.moklev.mathproof.model.Bound
import dev.moklev.mathproof.model.CoreSorts
import dev.moklev.mathproof.model.Free
import dev.moklev.mathproof.model.NamedSort
import dev.moklev.mathproof.testutils.discoverStatements
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertFailsWith
import kotlin.test.assertTrue

class FirstOrderModuleTest {
    private val verifier = ProofVerifier(firstOrderJustificationValidators)
    private val elementSort = NamedSort("Element")

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
    fun verifiesFirstOrderAxioms() {
        assertAllDiscoveredStatementsVerify(FirstOrderAxioms)
    }

    @Test
    fun verifiesDerivedFirstOrderLibraryStatements() {
        assertAllDiscoveredStatementsVerify(FirstOrderLibrary)
    }

    @Test
    fun rendersQuantifierExpressionsWithRegisteredNotation() {
        val predicate = function("P", elementSort, returns = CoreSorts.Proposition)
        val q = function("Q", elementSort, returns = CoreSorts.Proposition)
        val result = constant("result", CoreSorts.Proposition)
        val quantifier = forall("x", elementSort) { predicate(it) }

        assertEquals("∀x. P(x)", quantifier.toString())
        assertEquals("∃x. P(x)", exists("x", elementSort) { predicate(it) }.toString())
        assertEquals("!!∀x. P(x)", (!(!quantifier)).toString())
        assertEquals("(∀x. P(x)) -> result", (quantifier implies result).toString())
        assertEquals("(∀x. P(x)) -> ∀x. Q(x)", (quantifier implies forall("x", elementSort) { q(it) }).toString())
        assertEquals("(∀x. P(x)) and (∀x. Q(x))", (quantifier and forall("x", elementSort) { q(it) }).toString())
        assertEquals(
            "(!∃x. !P(x)) -> !∃x. !Q(x)",
            (
                !exists("x", elementSort) { !predicate(it) } implies
                    !exists("x", elementSort) { !q(it) }
                ).toString()
        )
    }

    @Test
    fun reportsUniversalInstantiationMismatchClearly() {
        val predicate = function("P", elementSort, returns = CoreSorts.Proposition)
        val witness = constant("a", elementSort)

        val error = assertFailsWith<IllegalArgumentException> {
            statement("broken-forall-instantiation") {
                val somePredicate = premise(FirstOrderFunctions.Exists(predicate))
                conclusion(predicate(witness))
                proof {
                    val existential = given(somePredicate)
                    applyByMpChain(FirstOrderAxioms.forallInstantiation(predicate, witness), existential)
                }
            }
        }

        assertTrue(error.message!!.contains("forall("))
        assertTrue(error.message!!.contains("exists("))
    }

    @Test
    fun appliesForallDistributionAxiom() {
        val guard = constant("guard", CoreSorts.Proposition)
        val predicate = function("P", elementSort, returns = CoreSorts.Proposition)

        val theorem = statement("uses-forall-distribution") {
            val premiseAll = premise(forall("x", elementSort) { guard implies predicate(it) })
            conclusion(guard implies FirstOrderFunctions.ForAll(predicate))
            proof {
                val universal = given(premiseAll)
                applyByMpChain(FirstOrderAxioms.forallDistribution(guard, predicate), universal)
            }
        }

        assertVerifies(theorem)
    }

    @Test
    fun rejectsForallDistributionWhenQuantifiedVariableIsFreeInPhi() {
        val predicate = function("P", elementSort, returns = CoreSorts.Proposition)
        val invalidPhi = Bound(index = 0, sort = CoreSorts.Proposition)

        val error = assertFailsWith<IllegalArgumentException> {
            FirstOrderAxioms.forallDistribution(invalidPhi, predicate)
        }

        assertTrue(error.message!!.contains("must not be free in phi"))
    }

    @Test
    fun appliesExistsEliminationSchemaAxiom() {
        val predicate = function("P", elementSort, returns = CoreSorts.Proposition)
        val result = constant("result", CoreSorts.Proposition)

        val theorem = statement("uses-exists-elimination-schema") {
            val implicationPremise = premise(forall("x", elementSort) { predicate(it) implies result })
            val existencePremise = premise(FirstOrderFunctions.Exists(predicate))
            conclusion(result)
            proof {
                val universalImplication = given(implicationPremise)
                val existential = given(existencePremise)
                val implicationToResult = applyByMpChain(
                    FirstOrderAxioms.existsElimination(predicate, result),
                    universalImplication,
                )
                infer(LogicAxioms.modusPonens(FirstOrderFunctions.Exists(predicate), result), existential, implicationToResult)
            }
        }

        assertVerifies(theorem)
    }

    @Test
    fun rejectsExistsEliminationSchemaWhenQuantifiedVariableIsFreeInPsi() {
        val predicate = function("P", elementSort, returns = CoreSorts.Proposition)
        val invalidPsi = Bound(index = 0, sort = CoreSorts.Proposition)

        val error = assertFailsWith<IllegalArgumentException> {
            FirstOrderAxioms.existsElimination(predicate, invalidPsi)
        }

        assertTrue(error.message!!.contains("must not be free in psi"))
    }

    @Test
    fun eliminatesExistentialPremiseWithHelper() {
        val predicate = function("P", elementSort, returns = CoreSorts.Proposition)
        val result = constant("result", CoreSorts.Proposition)
        val implicationPredicate = lambda("x", elementSort) { x -> predicate(x) implies result }

        val theorem = statement("uses-exists-elimination-helper") {
            val implicationPremise = premise(forall("x", elementSort) { predicate(it) implies result })
            val existencePremise = premise(FirstOrderFunctions.Exists(predicate))
            conclusion(result)
            proof {
                val universalImplication = given(implicationPremise)
                val existential = given(existencePremise)
                eliminateExists(existential) { x, witness ->
                    val implicationAtWitness = applyByMpChain(
                        FirstOrderAxioms.forallInstantiation(implicationPredicate, x),
                        given(universalImplication),
                    )
                    infer(LogicAxioms.modusPonens(predicate(x), result), witness, implicationAtWitness)
                }
            }
        }

        assertVerifies(theorem)
    }

    @Test
    fun buildsExistsImplicationWithExpressionForm() {
        val predicate = function("P", elementSort, returns = CoreSorts.Proposition)
        val result = constant("result", CoreSorts.Proposition)
        val implicationPredicate = lambda("x", elementSort) { x -> predicate(x) implies result }

        val theorem = statement("exists-elimination-expression-form") {
            val implicationPremise = premise(forall("x", elementSort) { predicate(it) implies result })
            conclusion(FirstOrderFunctions.Exists(predicate) implies result)
            proof {
                val universalImplication = given(implicationPremise)
                eliminateExists(FirstOrderFunctions.Exists(predicate)) { x, witness ->
                    val implicationAtWitness = applyByMpChain(
                        FirstOrderAxioms.forallInstantiation(implicationPredicate, x),
                        given(universalImplication),
                    )
                    infer(LogicAxioms.modusPonens(predicate(x), result), witness, implicationAtWitness)
                }
            }
        }

        assertVerifies(theorem)
    }

    @Test
    fun rejectsExistsEliminationHelperWhenResultDependsOnWitness() {
        val predicate = function("P", elementSort, returns = CoreSorts.Proposition)
        val witness = constant("a", elementSort)

        val error = assertFailsWith<IllegalArgumentException> {
            statement("broken-exists-elimination-helper-captures-witness") {
                val existencePremise = premise(FirstOrderFunctions.Exists(predicate))
                conclusion(predicate(witness))
                proof {
                    val existential = given(existencePremise)
                    eliminateExists(existential) { _, witnessFact ->
                        given(witnessFact)
                    }
                }
            }
        }

        assertTrue(error.message!!.contains("independent from the chosen witness"))
    }

    @Test
    fun derivesExistentialFromUniversalUsingConcreteWitness() {
        val predicate = function("P", elementSort, returns = CoreSorts.Proposition)
        val witness = constant("a", elementSort)

        val theorem = statement("derive-exists-from-forall") {
            val universalPremise = premise(FirstOrderFunctions.ForAll(predicate))
            conclusion(FirstOrderFunctions.Exists(predicate))
            proof {
                val universal = given(universalPremise)
                val witnessFact = applyByMpChain(FirstOrderAxioms.forallInstantiation(predicate, witness), universal)
                applyByMpChain(FirstOrderAxioms.existsIntroduction(predicate, witness), witnessFact)
            }
        }

        assertVerifies(theorem)
    }

    @Test
    fun derivesUniversalFromGuardAndQuantifiedImplication() {
        val guard = constant("guard", CoreSorts.Proposition)
        val predicate = function("P", elementSort, returns = CoreSorts.Proposition)

        val theorem = statement("derive-universal-from-guard") {
            val implicationPremise = premise(forall("x", elementSort) { guard implies predicate(it) })
            val guardPremise = premise(guard)
            conclusion(FirstOrderFunctions.ForAll(predicate))
            proof {
                val universalImplication = given(implicationPremise)
                val guardFact = given(guardPremise)
                val implicationToUniversal = applyByMpChain(FirstOrderAxioms.forallDistribution(guard, predicate), universalImplication)
                infer(LogicAxioms.modusPonens(guard, FirstOrderFunctions.ForAll(predicate)), guardFact, implicationToUniversal)
            }
        }

        assertVerifies(theorem)
    }

    @Test
    fun reportsExistsEliminationSchemaPremiseMismatchClearly() {
        val p = function("P", elementSort, returns = CoreSorts.Proposition)
        val q = function("Q", elementSort, returns = CoreSorts.Proposition)
        val result = constant("result", CoreSorts.Proposition)

        val error = assertFailsWith<IllegalArgumentException> {
            statement("broken-exists-elimination-premise") {
                val implicationPremise = premise(forall("x", elementSort) { q(it) implies result })
                val existencePremise = premise(FirstOrderFunctions.Exists(p))
                conclusion(result)
                proof {
                    val universalImplication = given(implicationPremise)
                    val existential = given(existencePremise)
                    val implicationToResult = applyByMpChain(
                        FirstOrderAxioms.existsElimination(p, result),
                        universalImplication,
                    )
                    infer(LogicAxioms.modusPonens(FirstOrderFunctions.Exists(p), result), existential, implicationToResult)
                }
            }
        }

        assertTrue(error.message!!.contains("P("))
        assertTrue(error.message!!.contains("Q("))
    }

    @Test
    fun appliesUniversalGeneralizationWithProofLocalArbitraryVariableWithoutPremises() {
        val predicate = function("P", elementSort, returns = CoreSorts.Proposition)

        val theorem = statement("forall-generalization-with-no-premises") {
            conclusion(forall("u", elementSort) { predicate(it) implies predicate(it) })
            proof {
                forAllByGeneralization("x", elementSort) { x ->
                    infer(LogicLibrary.implicationIdentity(predicate(x)))
                }
            }
        }

        assertVerifies(theorem)
    }

    @Test
    fun appliesUniversalGeneralizationWithUnrelatedPremise() {
        val predicate = function("P", elementSort, returns = CoreSorts.Proposition)
        val guard = constant("guard", CoreSorts.Proposition)

        val theorem = statement("forall-generalization-with-unrelated-premise") {
            val guardPremise = premise(guard)
            conclusion(forall("u", elementSort) { predicate(it) implies predicate(it) })
            proof {
                given(guardPremise)
                forAllByGeneralization("x", elementSort) { x ->
                    infer(LogicLibrary.implicationIdentity(predicate(x)))
                }
            }
        }

        assertVerifies(theorem)
    }

    @Test
    fun appliesUniversalGeneralizationInsideAssumeWithAssumptionDependentSource() {
        val guard = constant("guard", CoreSorts.Proposition)

        val theorem = statement("forall-generalization-inside-assume") {
            conclusion(guard implies forall("u", elementSort) { guard })
            proof {
                assume(guard) { assumption ->
                    forAllByGeneralization("x", elementSort) { _ ->
                        given(assumption)
                    }
                }
            }
        }

        assertVerifies(theorem)
    }

    @Test
    fun rejectsScopedGeneralizationWhenVariableAppearsInOpenAssumption() {
        val predicate = function("P", elementSort, returns = CoreSorts.Proposition)
        val goal = constant("goal", CoreSorts.Proposition)

        val error = assertFailsWith<IllegalArgumentException> {
            statement("bad-scoped-forall-generalization-open-assumption-capture") {
                conclusion(goal implies goal)
                proof {
                    val x = arbitrary("x", elementSort)
                    assume(predicate(x)) { assumption ->
                        generalizeForAll(x, given(assumption))
                    }
                }
            }
        }

        assertTrue(error.message!!.contains("open assumption"))
    }

    @Test
    fun rejectsScopedGeneralizationWhenVariableAppearsInStatementPremise() {
        val x = Free(
            symbol = "#manual-premise-x",
            sort = elementSort,
            displayName = "x",
        )
        val predicate = function("P", elementSort, returns = CoreSorts.Proposition)
        val guard = constant("guard", CoreSorts.Proposition)

        val error = assertFailsWith<IllegalArgumentException> {
            statement("bad-scoped-forall-generalization-premise-capture") {
                premise(predicate(x))
                conclusion(guard implies guard)
                proof {
                    assume(guard) { assumption ->
                        generalizeForAll(x, given(assumption))
                    }
                }
            }
        }

        assertTrue(error.message!!.contains("statement premise"))
    }

    @Test
    fun rejectsDuplicateArbitraryVariableNamesInsideOneProof() {
        val proposition = constant("phi", CoreSorts.Proposition)

        val error = assertFailsWith<IllegalArgumentException> {
            statement("duplicate-arbitrary-names") {
                conclusion(proposition implies proposition)
                proof {
                    arbitrary("x", elementSort)
                    arbitrary("x", elementSort)
                }
            }
        }

        assertTrue(error.message!!.contains("already declared"))
    }

    @Test
    fun rejectsArbitraryVariableNameThatConflictsWithStatementParameter() {
        val proposition = constant("phi", CoreSorts.Proposition)

        val error = assertFailsWith<IllegalArgumentException> {
            statement("arbitrary-name-conflicts-with-parameter") {
                parameter("x", elementSort)
                conclusion(proposition implies proposition)
                proof {
                    arbitrary("x", elementSort)
                }
            }
        }

        assertTrue(error.message!!.contains("conflicts with statement parameter"))
    }

    @Test
    fun rejectsUniversalGeneralizationWithoutRegisteredExtension() {
        val baseVerifier = ProofVerifier()
        val predicate = function("P", elementSort, returns = CoreSorts.Proposition)

        val theorem = statement("forall-generalization-requires-extension") {
            conclusion(forall("u", elementSort) { predicate(it) implies predicate(it) })
            proof {
                val x = arbitrary("x", elementSort)
                val identityAtX = infer(LogicLibrary.implicationIdentity(predicate(x)))
                generalizeForAll(x, identityAtX)
            }
        }

        val result = baseVerifier.verify(theorem)

        assertFalse(result.isValid)
        assertTrue(result.issues.any { it.message.contains("No verifier extension registered for justification") })
    }

    @Test
    fun rejectsUniversalGeneralizationOverStatementParameter() {
        val predicate = function("P", elementSort, returns = CoreSorts.Proposition)

        val broken = statement("bad-forall-generalization-parameter-origin") {
            val x = parameter("x", elementSort)
            conclusion(forall("u", elementSort) { predicate(it) implies predicate(it) })
            proof {
                val identityAtX = infer(LogicLibrary.implicationIdentity(predicate(x)))
                generalizeForAll(x, identityAtX)
            }
        }

        val result = verifier.verify(broken)

        assertFalse(result.isValid)
        assertTrue(result.issues.any { it.message.contains("statement parameter") })
    }

    @Test
    fun rejectsUniversalGeneralizationOverConstant() {
        val predicate = function("P", elementSort, returns = CoreSorts.Proposition)
        val a = constant("a", elementSort)

        val broken = statement("bad-forall-generalization-constant-origin") {
            conclusion(forall("u", elementSort) { predicate(it) implies predicate(it) })
            proof {
                val identityAtA = infer(LogicLibrary.implicationIdentity(predicate(a)))
                generalizeForAll(a, identityAtA)
            }
        }

        val result = verifier.verify(broken)

        assertFalse(result.isValid)
        assertTrue(result.issues.any { it.message.contains("constant/untracked symbol") && it.message.contains("'a'") })
    }

    @Test
    fun rejectsUniversalGeneralizationOverFunctionConstant() {
        val predicate = function("P", elementSort, returns = CoreSorts.Proposition)
        val witness = constant("a", elementSort)

        val broken = statement("bad-forall-generalization-function-constant-origin") {
            conclusion(forall("f", functionSort(elementSort, returns = CoreSorts.Proposition)) { it(witness) implies it(witness) })
            proof {
                val identityAtWitness = infer(LogicLibrary.implicationIdentity(predicate(witness)))
                generalizeForAll(predicate, identityAtWitness)
            }
        }

        val result = verifier.verify(broken)

        assertFalse(result.isValid)
        assertTrue(result.issues.any { it.message.contains("constant/untracked symbol") && it.message.contains("P") })
    }

    @Test
    fun rejectsUniversalGeneralizationWhenVariableAppearsInPremise() {
        val x = Free(
            symbol = "#manual-arbitrary-x",
            sort = elementSort,
            displayName = "x",
        )
        val predicate = function("P", elementSort, returns = CoreSorts.Proposition)
        val generalized = forall("u", elementSort) { predicate(it) }

        val broken = StatementDefinition(
            name = "bad-forall-generalization-premise-capture",
            parameters = emptyList(),
            premises = listOf(predicate(x)),
            conclusion = generalized,
            support = ProofProvided(
                proof = ProofScript(
                    steps = listOf(
                        ProofStep(
                            label = "givenPx",
                            claim = predicate(x),
                            justification = PremiseReference(0),
                        ),
                        ProofStep(
                            label = "allPx",
                            claim = generalized,
                            justification = UniversalGeneralization(
                                sourceLabel = "givenPx",
                                variable = x,
                            ),
                        ),
                    ),
                    arbitraryVariables = listOf(
                        ArbitraryVariable(
                            symbol = x.symbol,
                            displayName = x.displayName,
                            sort = x.sort,
                        ),
                    ),
                ),
            ),
        )

        val result = verifier.verify(broken)

        assertFalse(result.isValid)
        assertTrue(result.issues.any { it.message.contains("Universal generalization over") && it.message.contains("statement premise") })
    }

    @Test
    fun rejectsUniversalGeneralizationWhenBinderSortMismatchesVariableSort() {
        val proposition = constant("phi", CoreSorts.Proposition)
        val otherSort = NamedSort("Other")

        val broken = statement("bad-forall-generalization-binder-sort-mismatch") {
            val wrongClaim = forall("u", otherSort) { proposition implies proposition }
            conclusion(wrongClaim)
            proof {
                val x = arbitrary("x", elementSort)
                val identity = infer(LogicLibrary.implicationIdentity(proposition))
                justify(
                    claim = wrongClaim,
                    justification = UniversalGeneralization(
                        sourceLabel = identity.label,
                        variable = x,
                    ),
                    identity,
                )
            }
        }

        val result = verifier.verify(broken)

        assertFalse(result.isValid)
        assertTrue(result.issues.any { it.message.contains("binder sort") && it.message.contains("does not match") })
    }
}
