package dev.moklev.mathproof.fol

import dev.moklev.mathproof.core.constant
import dev.moklev.mathproof.core.function
import dev.moklev.mathproof.core.statement
import dev.moklev.mathproof.kernel.ProofVerifier
import dev.moklev.mathproof.kernel.StatementDefinition
import dev.moklev.mathproof.logic.LogicAxioms
import dev.moklev.mathproof.logic.implies
import dev.moklev.mathproof.model.Bound
import dev.moklev.mathproof.model.CoreSorts
import dev.moklev.mathproof.model.NamedSort
import dev.moklev.mathproof.testutils.discoverStatements
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertFailsWith
import kotlin.test.assertTrue

class FirstOrderModuleTest {
    private val verifier = ProofVerifier()
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

        assertEquals("forall(\\x. P(x))", forall("x", elementSort) { predicate(it) }.toString())
        assertEquals("exists(\\x. P(x))", exists("x", elementSort) { predicate(it) }.toString())
    }

    @Test
    fun reportsUniversalInstantiationMismatchClearly() {
        val predicate = function("P", elementSort, returns = CoreSorts.Proposition)
        val witness = constant("a", elementSort)

        val broken = statement("broken-forall-instantiation") {
            val somePredicate = premise(FirstOrderFunctions.Exists(predicate))
            conclusion(predicate(witness))
            proof {
                val existential = given(somePredicate)
                infer(FirstOrderAxioms.forallInstantiation(predicate, witness), existential)
            }
        }

        val result = verifier.verify(broken)

        assertFalse(result.isValid)
        assertTrue(result.issues.any { it.message.contains("forall(") && it.message.contains("exists(") })
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
                infer(FirstOrderAxioms.forallDistribution(guard, predicate), universal)
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
                val implicationToResult = infer(
                    FirstOrderAxioms.existsEliminationSchema(predicate, result),
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
            FirstOrderAxioms.existsEliminationSchema(predicate, invalidPsi)
        }

        assertTrue(error.message!!.contains("must not be free in psi"))
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
                val witnessFact = infer(FirstOrderAxioms.forallInstantiation(predicate, witness), universal)
                infer(FirstOrderAxioms.existsIntroduction(predicate, witness), witnessFact)
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
                val implicationToUniversal = infer(FirstOrderAxioms.forallDistribution(guard, predicate), universalImplication)
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

        val broken = statement("broken-exists-elimination-premise") {
            val implicationPremise = premise(forall("x", elementSort) { q(it) implies result })
            val existencePremise = premise(FirstOrderFunctions.Exists(p))
            conclusion(result)
            proof {
                val universalImplication = given(implicationPremise)
                val existential = given(existencePremise)
                val implicationToResult = infer(
                    FirstOrderAxioms.existsEliminationSchema(p, result),
                    universalImplication,
                )
                infer(LogicAxioms.modusPonens(FirstOrderFunctions.Exists(p), result), existential, implicationToResult)
            }
        }

        val resultCheck = verifier.verify(broken)

        assertFalse(resultCheck.isValid)
        assertTrue(resultCheck.issues.any { it.message.contains("P(") && it.message.contains("Q(") })
    }
}
