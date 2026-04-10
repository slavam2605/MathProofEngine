package dev.moklev.mathproof.nat

import dev.moklev.mathproof.algebra.AlgebraLibrary
import dev.moklev.mathproof.core.constant
import dev.moklev.mathproof.core.statement
import dev.moklev.mathproof.equality.eq
import dev.moklev.mathproof.fol.firstOrderJustificationValidators
import dev.moklev.mathproof.kernel.ProofVerifier
import dev.moklev.mathproof.kernel.StatementDefinition
import dev.moklev.mathproof.testutils.discoverStatementsChecked
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertTrue

class NatModuleTest {
    private val verifier = ProofVerifier(
        externalJustificationValidators = firstOrderJustificationValidators,
        failOnWarnings = true,
    )

    private fun assertVerifies(statement: StatementDefinition) {
        val result = verifier.verify(statement)
        assertTrue(result.isValid, result.describeIssues())
    }

    private fun assertAllDiscoveredStatementsVerify(holder: Any) {
        val discovered = discoverStatementsChecked(holder)
        discovered.forEach { statement ->
            assertVerifies(statement)
        }
    }

    @Test
    fun verifiesNatTheoryStatements() {
        assertAllDiscoveredStatementsVerify(NatTheory)
    }

    @Test
    fun verifiesNatAxiomsStatements() {
        assertAllDiscoveredStatementsVerify(NatAxioms)
    }

    @Test
    fun verifiesNatLibraryStatements() {
        assertAllDiscoveredStatementsVerify(NatLibrary)
    }

    @Test
    fun verifiesAlgebraLibraryStatementBuiltFromTrustedNatTheory() {
        assertVerifies(AlgebraLibrary.expandAdditiveZeroRight(NatTheory))
    }

    @Test
    fun verifiesCommutativityForNatTheory() {
        assertVerifies(NatTheory.addCommutative)
        assertVerifies(NatTheory.mulCommutative)
    }

    @Test
    fun verifiesMultiplicativeIdentityAxiomsForNatTheory() {
        assertVerifies(NatTheory.mulOneLeft)
        assertVerifies(NatTheory.mulOneRight)
    }

    @Test
    fun verifiesSemiringCoreAxiomsForNatTheory() {
        assertVerifies(NatTheory.addAssociative)
        assertVerifies(NatTheory.mulAssociative)
        assertVerifies(NatTheory.mulZeroLeft)
        assertVerifies(NatTheory.mulZeroRight)
        assertVerifies(NatTheory.mulDistributesOverAddLeft)
        assertVerifies(NatTheory.mulDistributesOverAddRight)
    }

    @Test
    fun verifiesOrderCompatibilityAxiomsForNatTheory() {
        assertVerifies(NatTheory.orderReflexive)
        assertVerifies(NatTheory.orderTransitive)
        assertVerifies(NatTheory.orderAntisymmetric)
        assertVerifies(NatTheory.orderTotal)
        assertVerifies(NatTheory.addPreservesOrderRight)
        assertVerifies(NatTheory.mulPreservesNonNegative)
    }

    @Test
    fun rendersNatExpressionsWithRegisteredNotation() {
        val n = constant("n", NatSorts.Nat)

        assertEquals("n + S0", NatFunctions.Add(n, succ(NatFunctions.Zero)).toString())
    }

    @Test
    fun reportsNaturalNumberAxiomMismatchClearly() {
        val x = constant("x", NatSorts.Nat)

        val broken = statement("broken-nat-add-zero") {
            conclusion(NatFunctions.Add(NatFunctions.Zero, x) eq x)
            proof {
                infer(NatTheory.addZeroRight(x))
            }
        }

        val result = verifier.verify(broken)

        assertFalse(result.isValid)
        assertTrue(result.issues.any { it.message.contains("x + 0") && it.message.contains("0 + x") })
    }
}
