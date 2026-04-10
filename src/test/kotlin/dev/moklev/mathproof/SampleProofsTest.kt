package dev.moklev.mathproof

import dev.moklev.mathproof.examples.SampleProofs
import dev.moklev.mathproof.kernel.ProofVerifier
import dev.moklev.mathproof.kernel.StatementDefinition
import dev.moklev.mathproof.kernel.prettyPrint
import dev.moklev.mathproof.testutils.discoverStatementsChecked
import kotlin.test.Test
import kotlin.test.assertTrue

class SampleProofsTest {
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
    fun prettyPrintsPremiseReferencesByStepNumber() {
        val rendered = SampleProofs.commutedConjunction.prettyPrint()

        assertTrue(rendered.contains("1. p and q (premise 1)"))
        assertTrue(rendered.contains("2. p and q -> q (and-elimination-right)"))
        assertTrue(rendered.contains("3. q (modus-ponens 1, 2)"))
        assertTrue(rendered.contains("4. p and q -> p (and-elimination-left)"))
        assertTrue(rendered.contains("5. p (modus-ponens 1, 4)"))
        assertTrue(rendered.contains("6. q -> p -> q and p (and-introduction)"))
        assertTrue(rendered.contains("7. p -> q and p (modus-ponens 3, 6)"))
        assertTrue(rendered.contains("8. q and p (modus-ponens 5, 7)"))
    }

    @Test
    fun verifiesDiscoveredSampleProofs() {
        assertAllDiscoveredStatementsVerify(SampleProofs)
    }
}
