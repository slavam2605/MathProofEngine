package dev.moklev.mathproof.algebra.tactics.ring

import dev.moklev.mathproof.algebra.theories.SemiringTheory
import dev.moklev.mathproof.equality.EqualityAxioms
import dev.moklev.mathproof.equality.EqualityLibrary
import dev.moklev.mathproof.equality.dsl.flipEq
import dev.moklev.mathproof.kernel.DerivationFact
import dev.moklev.mathproof.kernel.DerivationScope
import dev.moklev.mathproof.logic.applyMp
import dev.moklev.mathproof.model.Apply
import dev.moklev.mathproof.model.Expr

/**
 * Proves `left == right` by normalizing both expressions with [ringSimplify] steps
 * and composing the two equalities via transitivity.
 *
 * If [coefficients] is provided, constant folding and coefficient-based monoid folding
 * are enabled during normalization.
 *
 * Throws when normalized right-hand sides are different.
 */
context(scope: DerivationScope)
fun SemiringTheory.ring(left: Expr, right: Expr, coefficients: RingCoefficients? = null): DerivationFact {
    val ringHelper = RingSimplify(
        scope = scope,
        theory = this,
        coefficients = coefficients,
    )

    val leftNormalForm = ringHelper.simplify(left) // left == leftNormalForm
    val rightNormalForm = ringHelper.simplify(right) // right == rightNormalForm

    val lhsNormalExpr = (leftNormalForm.claim as Apply).argument
    val rhsNormalExpr = (rightNormalForm.claim as Apply).argument

    if (lhsNormalExpr != rhsNormalExpr) {
        error("Left and right normal forms are not equal: $lhsNormalExpr != $rhsNormalExpr")
    }

    return scope.applyMp(
        EqualityLibrary.transitivity,
        leftNormalForm,
        rightNormalForm.flipEq()
    )
}

/**
 * Normalizes [expr] inside the current [DerivationScope] and returns a derivation fact
 * proving `expr == normalizedExpr`.
 *
 * The normalization pipeline performs distribution, reassociation, atom/monoid sorting,
 * and optional coefficient folding when [coefficients] is provided.
 */
context(scope: DerivationScope)
fun SemiringTheory.ringSimplify(expr: Expr, coefficients: RingCoefficients? = null): DerivationFact {
    return RingSimplify(
        scope = scope,
        theory = this,
        coefficients = coefficients,
    ).simplify(expr)
}

internal class RingSimplify(
    private val scope: DerivationScope,
    private val theory: SemiringTheory,
    private val coefficients: RingCoefficients?,
) {
    internal val facts = mutableListOf<DerivationFact>()
    internal val lastFact get() = facts.last()
    internal val lastEqRhs get() = (lastFact.claim as Apply).argument

    private val distributeHelper = MulDistributor(this, scope, theory)
    private val leftAssocHelper = LeftAssociator(this, scope, theory)
    private val sortHelper = MonoidSorter(this, scope, theory, coefficients)
    private val foldHelper = coefficients?.let { MonoidFolder(this, scope, theory, coefficients) }

    fun simplify(expr: Expr): DerivationFact {
        facts.add(scope.infer(EqualityAxioms.reflexivity(expr)))

        // Distribute all parentheses
        distributeHelper.distributeAddMul()

        // Turn additions to left-assoc form => now getMonoids() works
        leftAssocHelper.transformAdd()

        // Turn multiplications to left-assoc form => now getAtoms() works
        leftAssocHelper.transformMul()

        // Sort atoms in each monoid => now all constants are in the end
        sortHelper.sortAtoms()

        // Fold multiplication constants
        foldHelper?.foldConstants()

        // Sort monoids => all `expr * const` go continuously for the same `expr`
        sortHelper.sortMonoids()

        // Fold monoids + fold constants again (because 1 + 1 -> 1 * 2, and now we need to compute 1 * 2)
        foldHelper?.foldMonoids()
        foldHelper?.foldConstants()

        return lastFact
    }
}
