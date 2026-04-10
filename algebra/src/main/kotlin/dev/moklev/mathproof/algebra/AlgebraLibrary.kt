package dev.moklev.mathproof.algebra

import dev.moklev.mathproof.algebra.theories.SemiringTheory
import dev.moklev.mathproof.core.lambda
import dev.moklev.mathproof.core.statement
import dev.moklev.mathproof.equality.EqualityAxioms
import dev.moklev.mathproof.equality.EqualityLibrary
import dev.moklev.mathproof.equality.eq
import dev.moklev.mathproof.logic.applyByMpChain

object AlgebraLibrary {
    fun addZeroLeft(theory: SemiringTheory) = statement("${theory.name}-add-zero-left") {
        val x = parameter("x", theory.carrier)

        conclusion(theory.add(theory.zero, x) eq x)
        proof {
            val xZero = infer(theory.addZeroRight(x)) // x + 0 == x
            val sym = infer(theory.addCommutative(x, theory.zero)) // x + 0 == 0 + x
            applyByMpChain(
                EqualityAxioms.substitution(
                    lambda("t", theory.carrier) { t -> t eq x },
                    theory.add(x, theory.zero), theory.add(theory.zero, x)
                ), sym, xZero
            )
        }
    }

    fun expandAdditiveZeroRight(theory: SemiringTheory) = statement("${theory.name}-expand-additive-zero-right") {
        val x = parameter("x", theory.carrier)

        conclusion(x eq theory.add(x, theory.zero))
        proof {
            val collapsed = infer(theory.addZeroRight(x))
            applyByMpChain(EqualityLibrary.symmetry(theory.add(x, theory.zero), x), collapsed)
        }
    }
}
