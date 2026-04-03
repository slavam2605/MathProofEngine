package dev.moklev.mathproof.equality

import dev.moklev.mathproof.core.constant
import dev.moklev.mathproof.core.statement
import dev.moklev.mathproof.kernel.ProofVerifier
import dev.moklev.mathproof.kernel.StatementDefinition
import dev.moklev.mathproof.model.NamedSort
import dev.moklev.mathproof.testutils.discoverStatements
import kotlin.test.Test
import kotlin.test.assertFalse
import kotlin.test.assertTrue

class EqualityModuleTest {
    private val verifier = ProofVerifier()

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
    fun verifiesEqualityAxioms() {
        assertAllDiscoveredStatementsVerify(EqualityAxioms)
    }

    @Test
    fun verifiesDerivedEqualityLibraryStatements() {
        assertAllDiscoveredStatementsVerify(EqualityLibrary)
    }

    @Test
    fun reportsEqualityBridgeMismatchClearly() {
        val scalar = NamedSort("Scalar")
        val x = constant("x", scalar)
        val y = constant("y", scalar)
        val z = constant("z", scalar)

        val broken = statement("broken-equality-bridge") {
            val xy = premise(x eq y)
            val zy = premise(z eq y)
            conclusion(x eq z)
            proof {
                val givenXy = given(xy)
                val givenZy = given(zy)
                infer("bad", EqualityLibrary.transitivity(x, y, z), givenXy, givenZy)
            }
        }

        val result = verifier.verify(broken)

        assertFalse(result.isValid)
        assertTrue(result.issues.any { it.message.contains("Premise 2") && it.message.contains("y = z") })
    }

    @Test
    fun reportsEqualityTransitivePremiseMismatchClearly() {
        val scalar = NamedSort("Scalar")
        val x = constant("x", scalar)
        val y = constant("y", scalar)
        val z = constant("z", scalar)

        val broken = statement("broken-equality-transitive-premises") {
            val xy = premise(x eq y)
            conclusion(x eq z)
            proof {
                val givenXy = given(xy)
                infer(EqualityLibrary.transitivity(x, y, z), givenXy, givenXy)
            }
        }

        val result = verifier.verify(broken)

        assertFalse(result.isValid)
        assertTrue(result.issues.any { it.message.contains("expected 'y = z'") && it.message.contains("x = y") })
    }
}
