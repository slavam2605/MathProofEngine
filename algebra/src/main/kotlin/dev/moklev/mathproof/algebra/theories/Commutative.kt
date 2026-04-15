package dev.moklev.mathproof.algebra.theories

import dev.moklev.mathproof.core.registry
import dev.moklev.mathproof.equality.eq
import dev.moklev.mathproof.kernel.ProofEvidence
import dev.moklev.mathproof.kernel.byEvidence
import dev.moklev.mathproof.model.Expr

/**
 * Orthogonal structure trait for multiplication commutativity.
 *
 * This is intentionally separated from the base theory-class chain so concrete theories can compose
 * `Commutative` with different levels (`SemiringTheory`, `RingTheory`, `FieldTheory`) without
 * introducing cross-product base classes.
 */
interface Commutative<T : SemiringTheory> {
    /**
     * The concrete theory instance this commutativity trait is attached to.
     */
    val commutativeTheory: T

    /**
     * Evidence provider for multiplicative commutativity.
     */
    val commutativeEvidence: Evidence

    /**
     * `a, b: T`
     *
     * `a * b == b * a`
     */
    val mulCommutative get() = registry.cachedStatement("${commutativeTheory.name}-mul-commutative") {
        val a = parameter("a", commutativeTheory.carrier)
        val b = parameter("b", commutativeTheory.carrier)

        conclusion(commutativeTheory.mul(a, b) eq commutativeTheory.mul(b, a))
        byEvidence(commutativeEvidence.mulCommutativeEvidence(a, b))
    }

    /**
     * Proof evidence contract behind multiplicative commutativity.
     */
    interface Evidence {
        /**
         * `a, b: T`
         *
         * `a * b == b * a`
         */
        fun mulCommutativeEvidence(a: Expr, b: Expr): ProofEvidence
    }
}
