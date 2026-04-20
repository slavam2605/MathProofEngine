package dev.moklev.mathproof.algebra.tactics.ring

import dev.moklev.mathproof.algebra.tactics.ring.RingUtils.getMonoids
import dev.moklev.mathproof.algebra.tactics.ring.RingUtils.isLess
import dev.moklev.mathproof.algebra.tactics.ring.RingUtils.foldMul
import dev.moklev.mathproof.algebra.tactics.ring.RingUtils.foldAdd
import dev.moklev.mathproof.algebra.tactics.ring.RingUtils.getAtoms
import dev.moklev.mathproof.algebra.tactics.ring.RingUtils.repeatWhile
import dev.moklev.mathproof.algebra.theories.Commutative
import dev.moklev.mathproof.algebra.theories.SemiringTheory
import dev.moklev.mathproof.dsl.ExprPath
import dev.moklev.mathproof.dsl.ExprPath.Companion.Root
import dev.moklev.mathproof.dsl.ExprPathStep.BinRight
import dev.moklev.mathproof.dsl.Occurences
import dev.moklev.mathproof.equality.EqualityAxioms
import dev.moklev.mathproof.equality.dsl.flipEq
import dev.moklev.mathproof.equality.dsl.replace
import dev.moklev.mathproof.kernel.DerivationScope
import dev.moklev.mathproof.model.Expr

internal class MonoidSorter(
    val helper: RingSimplify,
    val scope: DerivationScope,
    val theory: SemiringTheory,
    val coefficients: RingCoefficients?,
) {
    fun sortMonoids() {
        var monoids = helper.lastEqRhs.getMonoids(theory, Root / BinRight)

        repeat(monoids.size - 1) { pass ->
            for (i in 0 until monoids.size - 1 - pass) {
                val (cur, _) = monoids[i]
                val (next, rightPath) = monoids[i + 1]
                if (!next.isLess(cur, theory, coefficients)) continue

                with(scope) {
                    val swap = infer(theory.addCommutative(cur, next)) // cur + next == next + cur
                    val replaceStep = if (i != 0) {
                        val left = theory.foldAdd(monoids, i)
                        val step1 = infer(theory.addAssociative(left, cur, next)) // (left + cur) + next == left + (cur + next)
                        val step2 = step1.replace(swap, Occurences.Path(Root / BinRight / BinRight)) // (left + cur) + next == left + (next + cur)
                        val step3 = infer(theory.addAssociative(left, next, cur)).flipEq() // left + (next + cur) == (left + next) + cur
                        step2.replace(step3, Occurences.Path(Root / BinRight)) // (left + cur) + next == (left + next) + cur
                    } else swap
                    helper.facts.add(helper.lastFact.replace(replaceStep, Occurences.Path(rightPath.parent())))
                }

                monoids = helper.lastEqRhs.getMonoids(theory, Root / BinRight)
            }
        }
    }

    fun sortAtoms() {
        if (theory !is Commutative<*>) {
            return
        }

        repeatWhile {
            val monoids = helper.lastEqRhs.getMonoids(theory, Root / BinRight)
            monoids.any { (monoid, path) -> sortAtomsInMonoid(monoid, path) }
        }
    }

    private fun sortAtomsInMonoid(monoid: Expr, path: ExprPath): Boolean {
        check(theory is Commutative<*>)

        val lastFinalFact = helper.lastFact
        var changed = false
        var atoms = monoid.getAtoms(theory, Root / BinRight) // here path is to new root in reflexivity `monoid == monoid`

        repeat(atoms.size - 1) { pass ->
            for (i in 0 until atoms.size - 1 - pass) {
                val (cur, _) = atoms[i]
                val (next, rightPath) = atoms[i + 1]
                if (!next.isLess(cur, theory, coefficients)) continue

                if (!changed) {
                    helper.facts.add(scope.infer(EqualityAxioms.reflexivity(monoid)))
                    changed = true
                }

                with(scope) {
                    val swap = infer(theory.mulCommutative(cur, next))
                    val replaceStep = if (i != 0) {
                        val left = theory.foldMul(atoms, i)
                        val step1 = infer(theory.mulAssociative(left, cur, next)) // (left * cur) * next == left * (cur * next)
                        val step2 = step1.replace(swap, Occurences.Path(Root / BinRight / BinRight)) // (left * cur) * next == left * (next * cur)
                        val step3 = infer(theory.mulAssociative(left, next, cur)).flipEq() // left * (next * cur) == (left * next) * cur
                        step2.replace(step3, Occurences.Path(Root / BinRight)) // (left * cur) * next == (left * next) * cur
                    } else swap
                    helper.facts.add(helper.lastFact.replace(replaceStep, Occurences.Path(rightPath.parent())))
                }

                atoms = helper.lastEqRhs.getAtoms(theory, Root / BinRight)
            }
        }

        if (!changed) {
            return false
        }

        with(scope) {
            helper.facts.add(lastFinalFact.replace(helper.lastFact, Occurences.Path(path)))
        }
        return true
    }
}