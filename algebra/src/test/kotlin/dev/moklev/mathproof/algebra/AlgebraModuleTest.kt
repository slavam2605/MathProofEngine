package dev.moklev.mathproof.algebra

import dev.moklev.mathproof.algebra.theories.SemiringTheory
import dev.moklev.mathproof.core.constant
import dev.moklev.mathproof.core.function
import dev.moklev.mathproof.kernel.ProofEvidence
import dev.moklev.mathproof.kernel.trusted
import dev.moklev.mathproof.model.CoreSorts
import dev.moklev.mathproof.model.Expr
import dev.moklev.mathproof.model.NamedSort
import kotlin.test.Test
import kotlin.test.assertFailsWith
import kotlin.test.assertTrue

class AlgebraModuleTest {
    @Test
    fun validatesTheoryObjectConstructionGuards() {
        val scalar = NamedSort("Scalar")
        val zero = constant("zero", scalar)
        val one = constant("one", scalar)
        val mul = function("mul", scalar, scalar, returns = scalar)

        val error = assertFailsWith<IllegalArgumentException> {
            object : SemiringTheory(
                name = "broken",
                carrier = scalar,
                zero = zero,
                one = one,
                add = function("bad-add", scalar, scalar, returns = CoreSorts.Proposition),
                mul = mul,
            ) {
                override val semiringEvidence = object : Evidence {
                    override fun addAssociativeEvidence(x: Expr, y: Expr, z: Expr): ProofEvidence = trusted()

                    override fun addCommutativeEvidence(x: Expr, y: Expr): ProofEvidence = trusted()

                    override fun addZeroRightEvidence(x: Expr): ProofEvidence = trusted()

                    override fun mulAssociativeEvidence(x: Expr, y: Expr, z: Expr): ProofEvidence = trusted()

                    override fun mulZeroLeftEvidence(x: Expr): ProofEvidence = trusted()

                    override fun mulZeroRightEvidence(x: Expr): ProofEvidence = trusted()

                    override fun mulOneLeftEvidence(x: Expr): ProofEvidence = trusted()

                    override fun mulOneRightEvidence(x: Expr): ProofEvidence = trusted()

                    override fun mulDistributesOverAddLeftEvidence(x: Expr, y: Expr, z: Expr): ProofEvidence = trusted()

                    override fun mulDistributesOverAddRightEvidence(x: Expr, y: Expr, z: Expr): ProofEvidence = trusted()
                }
            }
        }

        assertTrue(error.message!!.contains("Addition for theory 'broken'"))
    }
}
