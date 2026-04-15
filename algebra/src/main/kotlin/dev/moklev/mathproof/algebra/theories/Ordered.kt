package dev.moklev.mathproof.algebra.theories

import dev.moklev.mathproof.core.functionSort
import dev.moklev.mathproof.core.registry
import dev.moklev.mathproof.equality.eq
import dev.moklev.mathproof.kernel.ProofEvidence
import dev.moklev.mathproof.kernel.byEvidence
import dev.moklev.mathproof.logic.implies
import dev.moklev.mathproof.logic.or
import dev.moklev.mathproof.model.CoreSorts
import dev.moklev.mathproof.model.Expr

/**
 * Orthogonal structure trait for ordered algebraic theories.
 *
 * The current contract models a total order (`reflexive`, `transitive`, `antisymmetric`, `total`)
 * plus compatibility with addition and multiplication of non-negative elements.
 */
interface Ordered<T : SemiringTheory> {
    /**
     * The concrete ordered theory instance this trait is attached to.
     */
    val orderedTheory: T

    /**
     * Order relation symbol with expected sort `T -> T -> Proposition`.
     */
    val leq: Expr

    /**
     * Evidence provider for all ordered statements.
     */
    val orderedEvidence: Evidence

    /**
     * Validates that [leq] has the expected order-relation sort for [orderedTheory].
     */
    fun requireOrderRelation() {
        val carrier = orderedTheory.carrier
        val expectedSort = functionSort(carrier, carrier, returns = CoreSorts.Proposition)
        require(leq.sort == expectedSort) {
            "Order relation for theory '${orderedTheory.name}' must have sort '$expectedSort', but got '${leq.sort}'."
        }
    }

    /**
     * `a: T`
     *
     * `a <= a`
     */
    val orderReflexive get() = registry.cachedStatement("${orderedTheory.name}-order-reflexive") {
        val a = parameter("a", orderedTheory.carrier)

        conclusion(leq(a, a))
        byEvidence(orderedEvidence.orderReflexiveEvidence(a))
    }

    /**
     * `a, b, c: T`
     *
     * `(a <= b) -> (b <= c) -> (a <= c)`
     */
    val orderTransitive get() = registry.cachedStatement("${orderedTheory.name}-order-transitive") {
        val a = parameter("a", orderedTheory.carrier)
        val b = parameter("b", orderedTheory.carrier)
        val c = parameter("c", orderedTheory.carrier)

        conclusion(leq(a, b) implies (leq(b, c) implies leq(a, c)))
        byEvidence(orderedEvidence.orderTransitiveEvidence(a, b, c))
    }

    /**
     * `a, b: T`
     *
     * `(a <= b) -> (b <= a) -> (a == b)`
     */
    val orderAntisymmetric get() = registry.cachedStatement("${orderedTheory.name}-order-antisymmetric") {
        val a = parameter("a", orderedTheory.carrier)
        val b = parameter("b", orderedTheory.carrier)

        conclusion((leq(a, b) implies (leq(b, a) implies (a eq b))))
        byEvidence(orderedEvidence.orderAntisymmetricEvidence(a, b))
    }

    /**
     * `a, b: T`
     *
     * `(a <= b) or (b <= a)`
     */
    val orderTotal get() = registry.cachedStatement("${orderedTheory.name}-order-total") {
        val a = parameter("a", orderedTheory.carrier)
        val b = parameter("b", orderedTheory.carrier)

        conclusion(leq(a, b) or leq(b, a))
        byEvidence(orderedEvidence.orderTotalEvidence(a, b))
    }

    /**
     * `x, y, z: T`
     *
     * `(x <= y) -> (x + z <= y + z)`
     */
    val addPreservesOrderRight get() = registry.cachedStatement("${orderedTheory.name}-addition-preserves-order-right") {
        val x = parameter("x", orderedTheory.carrier)
        val y = parameter("y", orderedTheory.carrier)
        val z = parameter("z", orderedTheory.carrier)

        conclusion(
            leq(x, y) implies leq(orderedTheory.add(x, z), orderedTheory.add(y, z)),
        )
        byEvidence(orderedEvidence.addPreservesOrderRightEvidence(x, y, z))
    }

    /**
     * `a, b: T`
     *
     * `(0 <= a) -> (0 <= b) -> (0 <= a * b)`
     */
    val mulPreservesNonNegative get() = registry.cachedStatement("${orderedTheory.name}-mul-preserves-non-negative") {
        val a = parameter("a", orderedTheory.carrier)
        val b = parameter("b", orderedTheory.carrier)

        conclusion(
            leq(orderedTheory.zero, a) implies
                    (leq(orderedTheory.zero, b) implies
                            leq(orderedTheory.zero, orderedTheory.mul(a, b)))
        )
        byEvidence(orderedEvidence.mulPreservesNonNegativeEvidence(a, b))
    }

    /**
     * Proof evidence contract behind ordered statements.
     */
    interface Evidence {
        /**
         * `a: T`
         *
         * `a <= a`
         */
        fun orderReflexiveEvidence(a: Expr): ProofEvidence

        /**
         * `a, b, c: T`
         *
         * `(a <= b) -> (b <= c) -> (a <= c)`
         */
        fun orderTransitiveEvidence(a: Expr, b: Expr, c: Expr): ProofEvidence

        /**
         * `a, b: T`
         *
         * `(a <= b) -> (b <= a) -> (a == b)`
         */
        fun orderAntisymmetricEvidence(a: Expr, b: Expr): ProofEvidence

        /**
         * `a, b: T`
         *
         * `(a <= b) or (b <= a)`
         */
        fun orderTotalEvidence(a: Expr, b: Expr): ProofEvidence

        /**
         * `x, y, z: T`
         *
         * `(x <= y) -> (x + z <= y + z)`
         */
        fun addPreservesOrderRightEvidence(x: Expr, y: Expr, z: Expr): ProofEvidence

        /**
         * `a, b: T`
         *
         * `(0 <= a) -> (0 <= b) -> (0 <= a * b)`
         */
        fun mulPreservesNonNegativeEvidence(a: Expr, b: Expr): ProofEvidence
    }
}
