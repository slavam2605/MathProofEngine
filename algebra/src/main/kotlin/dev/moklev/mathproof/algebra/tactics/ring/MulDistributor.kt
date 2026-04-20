package dev.moklev.mathproof.algebra.tactics.ring

import dev.moklev.mathproof.algebra.tactics.ring.RingUtils.repeatWhile
import dev.moklev.mathproof.algebra.tactics.ring.RingUtils.unpackAdd
import dev.moklev.mathproof.algebra.tactics.ring.RingUtils.unpackMul
import dev.moklev.mathproof.algebra.theories.SemiringTheory
import dev.moklev.mathproof.dsl.ExprPath
import dev.moklev.mathproof.dsl.ExprPath.Companion.Root
import dev.moklev.mathproof.dsl.ExprPathStep.Argument
import dev.moklev.mathproof.dsl.ExprPathStep.BinRight
import dev.moklev.mathproof.dsl.ExprPathStep.Function
import dev.moklev.mathproof.dsl.Occurences
import dev.moklev.mathproof.equality.dsl.replace
import dev.moklev.mathproof.kernel.DerivationScope
import dev.moklev.mathproof.model.Apply
import dev.moklev.mathproof.model.Expr

internal class MulDistributor(
    val helper: RingSimplify,
    val scope: DerivationScope,
    val theory: SemiringTheory
) {
    fun distributeAddMul() {
        repeatWhile {
            distributeOnce(helper.lastEqRhs, Root / BinRight)
        }
    }

    private fun distributeOnce(expr: Expr, path: ExprPath): Boolean {
        expr.unpackMul(theory)?.let { (left, right) ->
            left.unpackAdd(theory)?.let { (a, b) ->
                with(scope) {
                    val step1 = infer(theory.mulDistributesOverAddRight(a, b, right)) // (a + b) * right == a * right + b * right
                    helper.facts.add(helper.lastFact.replace(step1, Occurences.Path(path)))
                }
                return true
            }
            right.unpackAdd(theory)?.let { (a, b) ->
                with(scope) {
                    val step1 = infer(theory.mulDistributesOverAddLeft(left, a, b)) // left * (a + b) == left * a + left * b
                    helper.facts.add(helper.lastFact.replace(step1, Occurences.Path(path)))
                }
                return true
            }
        }

        if (expr is Apply) {
            if (distributeOnce(expr.function, path / Function)) return true
            if (distributeOnce(expr.argument, path / Argument)) return true
        }
        return false
    }
}