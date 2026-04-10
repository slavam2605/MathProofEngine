package dev.moklev.mathproof.equality

import dev.moklev.mathproof.core.constant
import dev.moklev.mathproof.core.statement
import dev.moklev.mathproof.kernel.ProofVerifier
import dev.moklev.mathproof.kernel.StatementDefinition
import dev.moklev.mathproof.logic.applyByMpChain
import dev.moklev.mathproof.model.NamedSort
import dev.moklev.mathproof.testutils.discoverStatementsChecked
import kotlin.test.Test
import kotlin.test.assertFailsWith
import kotlin.test.assertTrue

class EqualityModuleTest {
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

        val error = assertFailsWith<IllegalArgumentException> {
            statement("broken-equality-bridge") {
                val xy = premise(x eq y)
                val zy = premise(z eq y)
                conclusion(x eq z)
                proof {
                    val givenXy = given(xy)
                    val givenZy = given(zy)
                    applyByMpChain(EqualityLibrary.transitivity(x, y, z), givenXy, givenZy)
                }
            }
        }

        assertTrue(error.message!!.contains("applyByMpChain fact 2 mismatch"))
        assertTrue(error.message!!.contains("expected 'y = z'"))
        assertTrue(error.message!!.contains("got 'z = y'"))
    }

    @Test
    fun reportsEqualityTransitivePremiseMismatchClearly() {
        val scalar = NamedSort("Scalar")
        val x = constant("x", scalar)
        val y = constant("y", scalar)
        val z = constant("z", scalar)

        val error = assertFailsWith<IllegalArgumentException> {
            statement("broken-equality-transitive-premises") {
                val xy = premise(x eq y)
                conclusion(x eq z)
                proof {
                    val givenXy = given(xy)
                    applyByMpChain(EqualityLibrary.transitivity(x, y, z), givenXy, givenXy)
                }
            }
        }

        assertTrue(error.message!!.contains("applyByMpChain fact 2 mismatch"))
        assertTrue(error.message!!.contains("expected 'y = z'"))
        assertTrue(error.message!!.contains("got 'x = y'"))
    }
}
