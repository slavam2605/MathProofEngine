package dev.moklev.mathproof.nat

import dev.moklev.mathproof.algebra.theories.SemiringTheory
import dev.moklev.mathproof.core.lambda
import dev.moklev.mathproof.dsl.Occurences
import dev.moklev.mathproof.equality.EqualityAxioms
import dev.moklev.mathproof.equality.EqualityLibrary
import dev.moklev.mathproof.equality.dsl.flipEq
import dev.moklev.mathproof.equality.dsl.replace
import dev.moklev.mathproof.equality.eq
import dev.moklev.mathproof.fol.dsl.instantiateForall
import dev.moklev.mathproof.fol.forAllByGeneralization
import dev.moklev.mathproof.kernel.auto
import dev.moklev.mathproof.kernel.proved
import dev.moklev.mathproof.logic.applyMp
import dev.moklev.mathproof.logic.assume
import dev.moklev.mathproof.model.Expr
import dev.moklev.mathproof.nat.NatFunctions.Succ
import dev.moklev.mathproof.nat.NatSorts.Nat

class NatSemiringEvidence : SemiringTheory.Evidence {
    override fun addAssociativeEvidence(x: Expr, y: Expr, z: Expr) = proved {
        val base = run {
            val step1 = infer(NatAxioms.addDefinitionZero(x + y)) // (x + y) + 0 == x + y
            val step2 = infer(NatAxioms.addDefinitionZero(y)) // y + 0 == y
            val step3 = applyMp(EqualityLibrary.symmetry, step2) // y == y + 0
            val step4 = applyMp(EqualityLibrary.congruence(
                lambda("t", Nat) { t -> x + t }, auto(), auto()
            ), step3) // x + y == x + (y + 0)
            applyMp(EqualityLibrary.transitivity, step1, step4)
        }

        val step = forAllByGeneralization("u", Nat) { u ->
            assume((x + y) + u eq x + (y + u)) { prevStep -> // (x + y) + u == x + (y + u)
                val step1 = infer(NatAxioms.addDefinitionSucc(x + y, u)) // (x + y) + S(u) == S((x + y) + u)
                val step2 = applyMp(EqualityLibrary.congruence(
                    Succ, auto(), auto()
                ), prevStep) // S((x + y) + u) == S(x + (y + u))
                val step3 = applyMp(EqualityLibrary.transitivity, step1, step2) // (x + y) + S(u) == S(x + (y + u))
                val step4 = applyMp(EqualityLibrary.symmetry,
                    infer(NatAxioms.addDefinitionSucc(x, y + u))) // S(x + (y + u)) == x + S(y + u)
                val step5 = applyMp(EqualityLibrary.transitivity, step3, step4) // (x + y) + S(u) == x + S(y + u)
                val step6 = applyMp(EqualityLibrary.symmetry,
                    infer(NatAxioms.addDefinitionSucc(y, u))) // S(y + u) == y + S(u)
                val step7 = applyMp(EqualityLibrary.congruence(
                    lambda("t", Nat) { t -> x + t }, auto(), auto()
                ), step6) // x + S(y + u) == x + (y + S(u))
                applyMp(EqualityLibrary.transitivity, step5, step7)
            }
        }

        applyMp(NatAxioms.induction, base, step).instantiateForall(z)
    }

    override fun addCommutativeEvidence(x: Expr, y: Expr) = proved {
        val base = run {
            val step1 = infer(NatTheory.addZeroRight(x)) // x + 0 == x
            val step2 = infer(NatLibrary.addZeroLeft(x)) // 0 + x == x
            val step3 = applyMp(EqualityLibrary.symmetry, step2) // x == 0 + x
            applyMp(EqualityLibrary.transitivity, step1, step3) // x + 0 == 0 + x
        }

        val step = forAllByGeneralization("z", Nat) { z ->
            assume((x + z) eq (z + x)) { prevStep -> // x + z == z + x
                val step1 = infer(NatAxioms.addDefinitionSucc(x, z)) // x + S(z) == S(x + z)
                val step2 = infer(NatLibrary.addSuccLeft(z, x)) // S(z) + x == S(z + x)
                val step3 = applyMp(EqualityLibrary.congruence(
                    Succ, auto(), auto()
                ), prevStep) // S(x + z) == S(z + x)
                val step4 = applyMp(EqualityLibrary.transitivity, step1, step3) // x + S(z) == S(z + x)
                val step5 = applyMp(EqualityLibrary.symmetry, step2) // S(z + x) == S(z) + x
                applyMp(EqualityLibrary.transitivity, step4, step5) // x + S(z) == S(z) + x
            }
        }

        applyMp(NatAxioms.induction, base, step).instantiateForall(y)
    }

    override fun addZeroRightEvidence(x: Expr) = proved {
        infer(NatAxioms.addDefinitionZero(x))
    }

    override fun mulAssociativeEvidence(x: Expr, y: Expr, z: Expr) = proved {
        val base = run {
            val step1 = infer(NatAxioms.mulDefinitionZero(x * y)) // (x * y) * 0 == 0
            val step2 = infer(NatAxioms.mulDefinitionZero(y)).flipEq() // 0 == y * 0
            val step3 = infer(NatAxioms.mulDefinitionZero(x)).flipEq() // 0 == x * 0
            val step4 = step1.replace(step3, Occurences.Last) // (x * y) * 0 == x * 0
            step4.replace(step2, Occurences.Last) // (x * y) * 0 == x * (y * 0)
        }

        val step = forAllByGeneralization("u", Nat) { u ->
            assume((x * y) * u eq x * (y * u)) { prevStep -> // (x * y) * u == x * (y * u)
                val step1 = infer(NatAxioms.mulDefinitionSucc(x * y, u)) // (x * y) * S(u) == x * y + (x * y) * u
                val step2 = step1.replace(prevStep) // (x * y) * S(u) == x * y + x * (y * u)
                val step3 = infer(NatTheory.mulDistributesOverAddLeft(x, y, y * u)).flipEq() // x * y + x * (y * u) == x * (y + y * u)
                val step4 = applyMp(EqualityLibrary.transitivity, step2, step3) // (x * y) * S(u) == x * (y + y * u)
                val step5 = infer(NatTheory.mulOneRight(y)).flipEq() // y == y * S(0)
                val step6 = step4.replace(step5, Occurences.Only(1)) // (x * y) * S(u) == x * (y * S(0) + y * u)
                val step7 = infer(NatTheory.mulDistributesOverAddLeft(y, 1.n, u)).flipEq() // y * S(0) + y * u == y * (S(0) + u)
                val step8 = step6.replace(step7) // (x * y) * S(u) == x * (y * (S(0) + u))
                val step9 = infer(NatLibrary.addOneLeft(u)) // S(0) + u == S(u)
                step8.replace(step9)
            }
        }

        applyMp(NatAxioms.induction, base, step).instantiateForall(z)
    }

    override fun mulZeroLeftEvidence(x: Expr) = proved {
        val base = infer(NatAxioms.mulDefinitionZero(0.n)) // 0 * 0 == 0

        val step = forAllByGeneralization("y", Nat) { y ->
            assume(0.n * y eq 0.n) { prevStep -> // 0 * y == 0
                val step1 = infer(NatAxioms.mulDefinitionSucc(0.n, y)) // 0 * S(y) == 0 + 0 * y
                val step2 = step1.replace(prevStep) // 0 * S(y) == 0 + 0
                val step3 = infer(NatAxioms.addDefinitionZero(0.n)) // 0 + 0 == 0
                step2.replace(step3) // 0 * S(y) == 0
            }
        }

        applyMp(NatAxioms.induction, base, step).instantiateForall(x)
    }

    override fun mulZeroRightEvidence(x: Expr) = proved {
        infer(NatAxioms.mulDefinitionZero(x))
    }

    override fun mulOneLeftEvidence(x: Expr) = proved {
        val base = infer(NatAxioms.mulDefinitionZero(1.n)) // 1 * 0 == 0

        val step = forAllByGeneralization("y", Nat) { y ->
            assume(1.n * y eq y) { prevStep -> // 1 * y == y
                val step1 = infer(NatAxioms.mulDefinitionSucc(1.n, y)) // 1 * S(y) == 1 + 1 * y
                val step2 = step1.replace(prevStep) // 1 * S(y) == 1 + y
                val step3 = infer(NatLibrary.addOneLeft(y)) // 1 + y == S(y)
                step2.replace(step3) // 1 * S(y) == S(y)
            }
        }

        applyMp(NatAxioms.induction, base, step).instantiateForall(x)
    }

    override fun mulOneRightEvidence(x: Expr) = proved {
        val step1 = infer(NatAxioms.mulDefinitionSucc(x, 0.n)) // x * S(0) == x + x * 0
        val step2 = infer(NatAxioms.mulDefinitionZero(x)) // x * 0 == 0
        val step3 = applyMp(EqualityLibrary.congruence(
            lambda("t", Nat) { t -> x + t }, auto(), auto()
        ), step2) // x + x * 0 == x + 0
        val step4 = infer(NatAxioms.addDefinitionZero(x)) // x + 0 == x
        val step5 = applyMp(EqualityLibrary.transitivity, step1, step3) // x * S(0) == x + 0
        applyMp(EqualityLibrary.transitivity, step5, step4) // x * S(0) == x
    }

    override fun mulDistributesOverAddLeftEvidence(x: Expr, y: Expr, z: Expr) = proved {
        val step1 = infer(EqualityAxioms.reflexivity(x * (y + z))) // x * (y + z) == x * (y + z)
        val step2 = infer(NatTheory.addCommutative(y, z)) // y + z == z + y
        val step3 = step1.replace(step2, Occurences.Last) // x * (y + z) == x * (z + y)
        val step4 = infer(NatTheory.mulCommutative(x, z + y)) // x * (z + y) == (z + y) * x
        val step5 = applyMp(EqualityLibrary.transitivity, step3, step4) // x * (y + z) == (z + y) * x
        val step6 = infer(NatTheory.mulDistributesOverAddRight(z, y, x)) // (z + y) * x == z * x + y * x
        val step7 = applyMp(EqualityLibrary.transitivity, step5, step6) // x * (y + z) == z * x + y * x

        val step8 = infer(NatTheory.mulCommutative(z, x)) // z * x == x * z
        val step9 = infer(NatTheory.mulCommutative(y, x)) // y * x == x * y
        val step10 = infer(NatTheory.addCommutative(x * z, x * y)) // x * z + x * y == x * y + x * z

        val step11 = step7.replace(step8) // x * (y + z) == x * z + y * x
        val step12 = step11.replace(step9) // x * (y + z) == x * z + x * y
        step12.replace(step10) // x * (y + z) == x * y + x * z
    }

    override fun mulDistributesOverAddRightEvidence(x: Expr, y: Expr, z: Expr) = proved {
        val base = run {
            val step1 = infer(NatAxioms.mulDefinitionZero(x + y)) // (x + y) * 0 == 0
            val step2 = infer(NatAxioms.mulDefinitionZero(x)).flipEq() // 0 == x * 0
            val step3 = infer(NatAxioms.mulDefinitionZero(y)).flipEq() // 0 == y * 0
            val step4 = infer(NatAxioms.addDefinitionZero(0.n)) // 0 + 0 == 0
            val step5 = step4.replace(step2, Occurences.First) // x * 0 + 0 == 0
            val step6 = step5.replace(step3, Occurences.Only(1)) // x * 0 + y * 0 == 0
            step1.replace(step6.flipEq(), Occurences.Last) // (x + y) * 0 == x * 0 + y * 0
        }

        val step = forAllByGeneralization("t", Nat) { t ->
            assume((x + y) * t eq x * t + y * t) { prevStep -> // (x + y) * t == x * t + y * t
                val step1 = infer(NatAxioms.mulDefinitionSucc(x + y, t)) // (x + y) * S(t) == (x + y) + (x + y) * t
                val step2 = step1.replace(prevStep) // (x + y) * S(t) == (x + y) + (x * t + y * t)

                val step3 = infer(NatTheory.addAssociative(x, y, x * t + y * t)) // (x + y) + (x * t + y * t) == x + (y + (x * t + y * t))
                val step4 = step2.replace(step3) // (x + y) * S(t) == x + (y + (x * t + y * t))
                val step5 = infer(NatTheory.addAssociative(y, x * t, y * t)).flipEq() // y + (x * t + y * t) == (y + x * t) + y * t
                val step6 = step4.replace(step5) // (x + y) * S(t) == x + ((y + x * t) + y * t)
                val step7 = infer(NatTheory.addCommutative(y, x * t)) // y + x * t == x * t + y
                val step8 = step6.replace(step7) // (x + y) * S(t) == x + ((x * t + y) + y * t)
                val step9 = infer(NatTheory.addAssociative(x, x * t + y, y * t)).flipEq() // x + ((x * t + y) + y * t) == (x + (x * t + y)) + y * t
                val step10 = step8.replace(step9) // (x + y) * S(t) == (x + (x * t + y)) + y * t
                val step11 = infer(NatTheory.addAssociative(x, x * t, y)).flipEq() // x + (x * t + y) == (x + x * t) + y
                val step12 = step10.replace(step11) // (x + y) * S(t) == ((x + x * t) + y) + y * t
                val step13 = infer(NatTheory.addAssociative(x + x * t, y, y * t)) // ((x + x * t) + y) + y * t == (x + x * t) + (y + y * t)
                val step14 = step12.replace(step13) // (x + y) * S(t) == (x + x * t) + (y + y * t)

                val step15 = infer(NatAxioms.mulDefinitionSucc(x, t)).flipEq() // x + x * t == x * S(t)
                val step16 = infer(NatAxioms.mulDefinitionSucc(y, t)).flipEq() // y + y * t == y * S(t)
                val step17 = step14.replace(step15) // (x + t) * S(t) == x * S(t) + (y = y * t)
                step17.replace(step16) // (x + t) * S(t) == x * S(t) + y * S(t)
            }
        }

        applyMp(NatAxioms.induction, base, step).instantiateForall(z)
    }
}
