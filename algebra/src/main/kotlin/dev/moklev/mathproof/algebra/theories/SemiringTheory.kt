package dev.moklev.mathproof.algebra.theories

import dev.moklev.mathproof.core.functionSort
import dev.moklev.mathproof.core.statement
import dev.moklev.mathproof.equality.eq
import dev.moklev.mathproof.kernel.ProofEvidence
import dev.moklev.mathproof.kernel.byEvidence
import dev.moklev.mathproof.model.Expr
import dev.moklev.mathproof.model.Sort

/**
 * Symbol-and-rule bundle for a concrete semiring-like structure.
 *
 * A `SemiringTheory` fixes a carrier sort plus the primitive constants/operations (`0`, `1`, `+`, `*`),
 * validates their sorts at construction time, and exposes semiring statements through a separate
 * [Evidence] provider.
 *
 * Keeping evidence in a dedicated interface makes the trust boundary explicit: implementations can
 * either provide proof-backed evidence (`proved { ... }`) or trusted evidence (`trusted()`), but the
 * statement surface remains uniform for downstream modules.
 */
abstract class SemiringTheory(
    val name: String,
    val carrier: Sort,
    val zero: Expr,
    val one: Expr,
    val add: Expr,
    val mul: Expr,
) {
    /**
     * Evidence provider for all semiring statements exposed by this theory instance.
     */
    abstract val semiringEvidence: Evidence

    init {
        require(zero.sort == carrier) {
            "Zero for theory '$name' must have sort '$carrier', but got '${zero.sort}'."
        }
        require(one.sort == carrier) {
            "One for theory '$name' must have sort '$carrier', but got '${one.sort}'."
        }

        val binaryCarrierOperation = functionSort(carrier, carrier, returns = carrier)
        require(add.sort == binaryCarrierOperation) {
            "Addition for theory '$name' must have sort '$binaryCarrierOperation', but got '${add.sort}'."
        }
        require(mul.sort == binaryCarrierOperation) {
            "Multiplication for theory '$name' must have sort '$binaryCarrierOperation', but got '${mul.sort}'."
        }
    }

    /**
     * `x, y, z: T`
     *
     * `(x + y) + z == x + (y + z)`
     */
    val addAssociative get() = statement("${name}-add-associative") {
        val x = parameter("x", carrier)
        val y = parameter("y", carrier)
        val z = parameter("z", carrier)

        conclusion(add(add(x, y), z) eq add(x, add(y, z)))
        byEvidence(semiringEvidence.addAssociativeEvidence(x, y, z))
    }

    /**
     * `x, y: T`
     *
     * `x + y == y + x`
     */
    val addCommutative get() = statement("${name}-add-commutative") {
        val x = parameter("x", carrier)
        val y = parameter("y", carrier)

        conclusion(add(x, y) eq add(y, x))
        byEvidence(semiringEvidence.addCommutativeEvidence(x, y))
    }

    /**
     * `x: T`
     *
     * `x + 0 == x`
     */
    val addZeroRight get() = statement("${name}-add-zero-right") {
        val x = parameter("x", carrier)

        conclusion(add(x, zero) eq x)
        byEvidence(semiringEvidence.addZeroRightEvidence(x))
    }

    /**
     * `x, y, z: T`
     *
     * `(x * y) * z == x * (y * z)`
     */
    val mulAssociative get() = statement("${name}-mul-associative") {
        val x = parameter("x", carrier)
        val y = parameter("y", carrier)
        val z = parameter("z", carrier)

        conclusion(mul(mul(x, y), z) eq mul(x, mul(y, z)))
        byEvidence(semiringEvidence.mulAssociativeEvidence(x, y, z))
    }

    /**
     * `x: T`
     *
     * `0 * x == 0`
     */
    val mulZeroLeft get() = statement("${name}-mul-zero-left") {
        val x = parameter("x", carrier)

        conclusion(mul(zero, x) eq zero)
        byEvidence(semiringEvidence.mulZeroLeftEvidence(x))
    }

    /**
     * `x: T`
     *
     * `x * 0 == 0`
     */
    val mulZeroRight get() = statement("${name}-mul-zero-right") {
        val x = parameter("x", carrier)

        conclusion(mul(x, zero) eq zero)
        byEvidence(semiringEvidence.mulZeroRightEvidence(x))
    }

    /**
     * `x: T`
     *
     * `1 * x == x`
     */
    val mulOneLeft get() = statement("${name}-mul-one-left") {
        val x = parameter("x", carrier)

        conclusion(mul(one, x) eq x)
        byEvidence(semiringEvidence.mulOneLeftEvidence(x))
    }

    /**
     * `x: T`
     *
     * `x * 1 == x`
     */
    val mulOneRight get() = statement("${name}-mul-one-right") {
        val x = parameter("x", carrier)

        conclusion(mul(x, one) eq x)
        byEvidence(semiringEvidence.mulOneRightEvidence(x))
    }

    /**
     * `x, y, z: T`
     *
     * `x * (y + z) == (x * y) + (x * z)`
     */
    val mulDistributesOverAddLeft get() = statement("${name}-mul-distributes-over-add-left") {
        val x = parameter("x", carrier)
        val y = parameter("y", carrier)
        val z = parameter("z", carrier)

        conclusion(mul(x, add(y, z)) eq add(mul(x, y), mul(x, z)))
        byEvidence(semiringEvidence.mulDistributesOverAddLeftEvidence(x, y, z))
    }

    /**
     * `x, y, z: T`
     *
     * `(x + y) * z == (x * z) + (y * z)`
     */
    val mulDistributesOverAddRight get() = statement("${name}-mul-distributes-over-add-right") {
        val x = parameter("x", carrier)
        val y = parameter("y", carrier)
        val z = parameter("z", carrier)

        conclusion(mul(add(x, y), z) eq add(mul(x, z), mul(y, z)))
        byEvidence(semiringEvidence.mulDistributesOverAddRightEvidence(x, y, z))
    }

    /**
     * Proof evidence contract behind semiring statements.
     */
    interface Evidence {
        /**
         * `x, y, z: T`
         *
         * `(x + y) + z == x + (y + z)`
         */
        fun addAssociativeEvidence(x: Expr, y: Expr, z: Expr): ProofEvidence

        /**
         * `x, y: T`
         *
         * `x + y == y + x`
         */
        fun addCommutativeEvidence(x: Expr, y: Expr): ProofEvidence

        /**
         * `x: T`
         *
         * `x + 0 == x`
         */
        fun addZeroRightEvidence(x: Expr): ProofEvidence

        /**
         * `x, y, z: T`
         *
         * `(x * y) * z == x * (y * z)`
         */
        fun mulAssociativeEvidence(x: Expr, y: Expr, z: Expr): ProofEvidence

        /**
         * `x: T`
         *
         * `0 * x == 0`
         */
        fun mulZeroLeftEvidence(x: Expr): ProofEvidence

        /**
         * `x: T`
         *
         * `x * 0 == 0`
         */
        fun mulZeroRightEvidence(x: Expr): ProofEvidence

        /**
         * `x: T`
         *
         * `1 * x == x`
         */
        fun mulOneLeftEvidence(x: Expr): ProofEvidence

        /**
         * `x: T`
         *
         * `x * 1 == x`
         */
        fun mulOneRightEvidence(x: Expr): ProofEvidence

        /**
         * `x, y, z: T`
         *
         * `x * (y + z) == (x * y) + (x * z)`
         */
        fun mulDistributesOverAddLeftEvidence(x: Expr, y: Expr, z: Expr): ProofEvidence

        /**
         * `x, y, z: T`
         *
         * `(x + y) * z == (x * z) + (y * z)`
         */
        fun mulDistributesOverAddRightEvidence(x: Expr, y: Expr, z: Expr): ProofEvidence
    }
}
