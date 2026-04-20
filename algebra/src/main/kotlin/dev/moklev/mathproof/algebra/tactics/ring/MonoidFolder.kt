package dev.moklev.mathproof.algebra.tactics.ring

import dev.moklev.mathproof.algebra.tactics.ring.RingUtils.foldAdd
import dev.moklev.mathproof.algebra.tactics.ring.RingUtils.foldMul
import dev.moklev.mathproof.algebra.tactics.ring.RingUtils.getAtoms
import dev.moklev.mathproof.algebra.tactics.ring.RingUtils.getMonoids
import dev.moklev.mathproof.algebra.tactics.ring.RingUtils.repeatWhile
import dev.moklev.mathproof.algebra.tactics.ring.RingUtils.unpackMul
import dev.moklev.mathproof.algebra.theories.SemiringTheory
import dev.moklev.mathproof.dsl.ExprPath
import dev.moklev.mathproof.dsl.ExprPath.Companion.Root
import dev.moklev.mathproof.dsl.ExprPathStep.BinLeft
import dev.moklev.mathproof.dsl.ExprPathStep.BinRight
import dev.moklev.mathproof.dsl.Occurences
import dev.moklev.mathproof.equality.EqualityAxioms
import dev.moklev.mathproof.equality.dsl.flipEq
import dev.moklev.mathproof.equality.dsl.replace
import dev.moklev.mathproof.kernel.DerivationFact
import dev.moklev.mathproof.kernel.DerivationScope
import dev.moklev.mathproof.model.Expr

internal class MonoidFolder(
    val helper: RingSimplify,
    val scope: DerivationScope,
    val theory: SemiringTheory,
    val coefficients: RingCoefficients,
) {
    fun foldMonoids() {
        repeatWhile {
            foldMonoidsOnce()
        }
    }

    fun foldConstants() {
        repeatWhile {
            foldMulConstantsOnce()
        }
    }

    private fun foldMulConstantsOnce(): Boolean {
        helper.lastEqRhs.getMonoids(theory, Root / BinRight).forEach { (monoid, path) ->
            val atoms = monoid.getAtoms(theory, path)
            if (atoms.size < 2) return@forEach

            val (left, _) = atoms[atoms.size - 2]
            val (right, rightPath) = atoms[atoms.size - 1]

            val leftConst = coefficients.isConstant(left)
            val rightConst = coefficients.isConstant(right)
            if (!leftConst && rightConst) {
                if (right == theory.one || right == theory.zero) {
                    val mulFact = when (right) {
                        theory.one -> scope.infer(theory.mulOneRight(left)) // left * 1 == left
                        theory.zero -> scope.infer(theory.mulZeroRight(left)) // left * 0 == 0
                        else -> error("Unexpected constant value: $right")
                    }

                    with(scope) {
                        val replaceFact = if (atoms.size > 2) {
                            val prefix = theory.foldMul(atoms, atoms.size - 2)
                            val assoc = infer(theory.mulAssociative(prefix, left, right)) // (prefix * left) * right == prefix * (left * right)
                            assoc.replace(mulFact, Occurences.Path(Root / BinRight / BinRight))
                        } else mulFact
                        helper.facts.add(helper.lastFact.replace(replaceFact, Occurences.Path(path)))
                    }
                    return true
                }
            }

            if (!leftConst || !rightConst) return@forEach

            with(scope) {
                val mulFact = coefficients.mul(left, right)
                val replaceFact = if (atoms.size > 2) {
                    val prefix = theory.foldMul(atoms, atoms.size - 2)
                    val assoc = infer(theory.mulAssociative(prefix, left, right)) // (prefix * left) * right == prefix * (left * right)
                    assoc.replace(mulFact, Occurences.Path(Root / BinRight / BinRight))
                } else mulFact
                helper.facts.add(helper.lastFact.replace(replaceFact, Occurences.Path(rightPath.parent())))
            }

            return true
        }
        return false
    }

    context(scope: DerivationScope)
    private fun DerivationFact.replaceMulOne(expr: Expr, path: ExprPath): DerivationFact {
        val mulOne = scope.infer(theory.mulOneRight(expr)).flipEq() // expr = expr * 1
        return replace(mulOne, Occurences.Path(path))
    }

    private fun foldMonoidsOnce(): Boolean {
        val monoids = helper.lastEqRhs.getMonoids(theory, Root / BinRight)

        for (i in 0 until monoids.size - 1) {
            val (left, _) = monoids[i]
            val (right, rightPath) = monoids[i + 1]

            val (cur, a) = left.unpackConstMul()
            val (next, b) = right.unpackConstMul()
            if (cur != next) continue

            with(scope) {
                var base: DerivationFact
                val basePath: ExprPath
                if (i == 0) {
                    base = infer(EqualityAxioms.reflexivity(theory.add(left, right))) // left + right == left + right
                    basePath = Root / BinRight
                } else {
                    val prefix = theory.foldAdd(monoids, i)
                    base = infer(theory.addAssociative(prefix, left, right)) // (prefix + left) + right == prefix + (left + right)
                    basePath = Root / BinRight / BinRight
                }

                if (left == cur) {
                    base = base.replaceMulOne(left, basePath / BinLeft)
                }
                if (right == next) {
                    base = base.replaceMulOne(right, basePath / BinRight)
                }

                val distribute = infer(theory.mulDistributesOverAddLeft(cur, a, b)).flipEq() // cur * a + cur * b == cur * (a + b)
                val addFact = coefficients.add(a, b) // a + b == coeff[a + b]
                val step1 = distribute.replace(addFact, Occurences.Path(Root / BinRight / BinRight)) // cur * a + cur * b == cur * coeff[a + b]
                val step2 = base.replace(step1, Occurences.Path(basePath))
                helper.facts.add(helper.lastFact.replace(step2, Occurences.Path(rightPath.parent())))
            }

            return true
        }

        return false
    }

    private fun Expr.unpackConstMul(): Pair<Expr, Expr> {
        val (left, right) = unpackMul(theory) ?: return this to theory.one
        if (coefficients.isConstant(right)) return left to right
        return this to theory.one
    }
}
