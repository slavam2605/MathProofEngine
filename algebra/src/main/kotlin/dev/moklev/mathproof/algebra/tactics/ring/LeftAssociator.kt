package dev.moklev.mathproof.algebra.tactics.ring

import dev.moklev.mathproof.algebra.tactics.ring.RingUtils.getMonoids
import dev.moklev.mathproof.algebra.tactics.ring.RingUtils.repeatWhile
import dev.moklev.mathproof.algebra.tactics.ring.RingUtils.unpackAdd
import dev.moklev.mathproof.algebra.tactics.ring.RingUtils.unpackMul
import dev.moklev.mathproof.algebra.theories.SemiringTheory
import dev.moklev.mathproof.dsl.ExprPath
import dev.moklev.mathproof.dsl.ExprPathStep
import dev.moklev.mathproof.dsl.Occurences
import dev.moklev.mathproof.equality.dsl.flipEq
import dev.moklev.mathproof.equality.dsl.replace
import dev.moklev.mathproof.kernel.DerivationScope
import dev.moklev.mathproof.kernel.StatementDefinition
import dev.moklev.mathproof.model.Expr

internal class LeftAssociator(
    val helper: RingSimplify,
    val scope: DerivationScope,
    val theory: SemiringTheory
) {
    fun transformAdd() {
        repeatWhile {
            transformAddOnce(helper.lastEqRhs)
        }
    }

    fun transformMul() {
        repeatWhile {
            val monoids = helper.lastEqRhs.getMonoids(theory, ExprPath.Root / ExprPathStep.BinRight)
            monoids.any { (expr, path) -> transformMulOnce(expr, path) }
        }
    }

    private fun transformAddOnce(expr: Expr) = transformOnce(
        expr = expr,
        path = ExprPath.Root / ExprPathStep.BinRight,
        unpack = { unpackAdd(it) },
        assocAxiom = theory.addAssociative
    )

    private fun transformMulOnce(expr: Expr, path: ExprPath) = transformOnce(
        expr = expr,
        path = path,
        unpack = { unpackMul(it) },
        assocAxiom = theory.mulAssociative
    )

    private fun transformOnce(
        expr: Expr,
        path: ExprPath,
        unpack: Expr.(SemiringTheory) -> Pair<Expr, Expr>?,
        assocAxiom: StatementDefinition
    ): Boolean {
        val (left, right) = expr.unpack(theory) ?: return false

        right.unpack(theory)?.let { (b, c) ->
            with(scope) {
                val assoc = infer(assocAxiom(left, b, c)).flipEq() // (a + b) + c == a + (b + c)
                helper.facts.add(helper.lastFact.replace(assoc, Occurences.Path(path)))
            }

            return true
        }

        if (transformOnce(left, path / ExprPathStep.BinLeft, unpack, assocAxiom)) return true
        if (transformOnce(right, path / ExprPathStep.BinRight, unpack, assocAxiom)) return true
        return false
    }
}