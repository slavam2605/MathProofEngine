package dev.moklev.mathproof.algebra.tactics.ring

import dev.moklev.mathproof.algebra.theories.SemiringTheory
import dev.moklev.mathproof.dsl.ExprPath
import dev.moklev.mathproof.dsl.ExprPathStep
import dev.moklev.mathproof.model.Apply
import dev.moklev.mathproof.model.Expr

internal object RingUtils {
    // TODO implement stable Expr order
    private fun Expr.baseLess(other: Expr): Boolean {
        return this.toString() < other.toString()
    }

    private fun Expr.stripRightConstMul(theory: SemiringTheory, coefficients: RingCoefficients?): Expr {
        if (coefficients == null) return this
        this.unpackMul(theory)?.let { (a, b) ->
            if (coefficients.isConstant(b)) {
                return a
            }
        }
        return this
    }

    /**
     * Sorts coefficients last, then sorts expressions ignoring the rightmost constant multiplication.
     */
    fun Expr.isLess(other: Expr, theory: SemiringTheory, coefficients: RingCoefficients?): Boolean {
        if (coefficients != null) {
            val thisIsConst = coefficients.isConstant(this)
            val otherIsConst = coefficients.isConstant(other)
            if (thisIsConst != otherIsConst) {
                return thisIsConst < otherIsConst
            }
        }

        val thisNoConst = stripRightConstMul(theory, coefficients)
        val otherNoConst = other.stripRightConstMul(theory, coefficients)
        return thisNoConst.baseLess(otherNoConst)
    }

    fun Expr.unpackAdd(theory: SemiringTheory): Pair<Expr, Expr>? {
        val leftApply = (this as? Apply)?.function as? Apply ?: return null
        if (leftApply.function != theory.add) return null
        return leftApply.argument to this.argument
    }

    fun Expr.unpackMul(theory: SemiringTheory): Pair<Expr, Expr>? {
        val leftApply = (this as? Apply)?.function as? Apply ?: return null
        if (leftApply.function != theory.mul) return null
        return leftApply.argument to this.argument
    }

    fun Expr.getMonoids(theory: SemiringTheory, path: ExprPath): List<Pair<Expr, ExprPath>> {
        val result = mutableListOf<Pair<Expr, ExprPath>>()

        fun walkDown(e: Expr, path: ExprPath) {
            val (left, right) = e.unpackAdd(theory) ?: run {
                result.add(e to path)
                return
            }

            walkDown(left, path / ExprPathStep.BinLeft)
            result.add(right to path / ExprPathStep.BinRight)
        }

        walkDown(this, path)
        return result
    }

    fun Expr.getAtoms(theory: SemiringTheory, path: ExprPath): List<Pair<Expr, ExprPath>> {
        val result = mutableListOf<Pair<Expr, ExprPath>>()

        fun walkDown(e: Expr, path: ExprPath) {
            val (left, right) = e.unpackMul(theory) ?: run {
                result.add(e to path)
                return
            }

            walkDown(left, path / ExprPathStep.BinLeft)
            result.add(right to path / ExprPathStep.BinRight)
        }

        walkDown(this, path)
        return result
    }

    fun SemiringTheory.foldAdd(exprList: List<Pair<Expr, ExprPath>>, to: Int): Expr {
        return exprList.asSequence().take(to).map { it.first }.reduce { acc, expr -> add(acc, expr) }
    }

    fun SemiringTheory.foldMul(exprList: List<Pair<Expr, ExprPath>>, to: Int): Expr {
        return exprList.asSequence().take(to).map { it.first }.reduce { acc, expr -> mul(acc, expr) }
    }

    fun repeatWhile(predicate: () -> Boolean) {
        while (predicate()) { /* continue */ }
    }
}