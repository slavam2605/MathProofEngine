package dev.moklev.mathproof.nat

import dev.moklev.mathproof.algebra.theories.Commutative
import dev.moklev.mathproof.core.lambda
import dev.moklev.mathproof.equality.EqualityLibrary
import dev.moklev.mathproof.equality.eq
import dev.moklev.mathproof.fol.FirstOrderAxioms
import dev.moklev.mathproof.fol.forAllByGeneralization
import dev.moklev.mathproof.kernel.ProofEvidence
import dev.moklev.mathproof.kernel.auto
import dev.moklev.mathproof.kernel.proved
import dev.moklev.mathproof.logic.applyMp
import dev.moklev.mathproof.logic.assume
import dev.moklev.mathproof.model.Expr
import dev.moklev.mathproof.nat.NatSorts.Nat

class NatCommutativeEvidence : Commutative.Evidence {
    override fun mulCommutativeEvidence(a: Expr, b: Expr): ProofEvidence = proved {
        val base = run {
            val step1 = infer(NatAxioms.mulDefinitionZero(a)) // a * 0 == 0
            val step2 = infer(NatLibrary.mulZeroLeft(a)) // 0 * a == 0
            val step3 = applyMp(EqualityLibrary.symmetry, step2) // 0 == 0 * a
            applyMp(EqualityLibrary.transitivity, step1, step3) // a * 0 == 0 * a
        }

        val step = forAllByGeneralization("x", Nat) { x ->
            assume(a * x eq x * a) { axXA -> // a * x == x * a
                val step1 = infer(NatAxioms.mulDefinitionSucc(a, x)) // a * S(x) == a + a * x
                val step2 = applyMp(EqualityLibrary.congruence(
                    lambda("t", Nat) { t -> a + t }, auto(), auto()
                ), axXA) // a + a * x == a + x * a
                val step3 = infer(NatLibrary.mulSuccLeft(x, a)) // S(x) * a == a + x * a
                val step4 = applyMp(EqualityLibrary.symmetry, step3) // a + x * a == S(x) * a
                val step5 = applyMp(EqualityLibrary.transitivity, step1, step2) // a * S(x) == a + x * a
                applyMp(EqualityLibrary.transitivity, step5, step4) // a * S(x) == S(x) * a
            }
        }

        val forallX = applyMp(NatAxioms.induction, base, step)
        applyMp(FirstOrderAxioms.forallInstantiation(auto(), b), forallX)
    }
}
