package dev.moklev.mathproof.equality

import dev.moklev.mathproof.core.functionSort
import dev.moklev.mathproof.core.lambda
import dev.moklev.mathproof.core.sortVariable
import dev.moklev.mathproof.core.statement
import dev.moklev.mathproof.logic.LogicAxioms.modusPonens

object EqualityLibrary {
    val symmetry = statement("equality-symmetric") {
        val s = sortVariable("S")
        val x = parameter("x", s)
        val y = parameter("y", s)

        val xy = premise(x eq y)
        conclusion(y eq x)
        proof {
            val xy = given(xy)
            val f = lambda("t", s) { t -> t eq x }
            val step1 = infer(EqualityAxioms.substitution(f, x, y), xy)
            val step2 = infer(EqualityAxioms.reflexivity(x))
            infer(modusPonens(x eq x, y eq x), step2, step1)
        }
    }

    val transitivity = statement("equality-transitive") {
        val s = sortVariable("S")
        val x = parameter("x", s)
        val y = parameter("y", s)
        val z = parameter("z", s)

        val xy = premise(x eq y)
        val yz = premise(y eq z)
        conclusion(x eq z)
        proof {
            val xy = given(xy)
            val yz = given(yz)
            val yx = infer(symmetry(x, y), xy)
            val f = lambda("t", s) { t -> t eq z }
            val step4 = infer(EqualityAxioms.substitution(f, y, x), yx)
            infer(modusPonens(y eq z, x eq z), yz, step4)
        }
    }

    val congruence = statement("equality-congruence") {
        val s = sortVariable("S")
        val t = sortVariable("T")
        val f = parameter("f", functionSort(s, returns = t))
        val x = parameter("x", s)
        val y = parameter("y", s)

        val xy = premise(x eq y)
        conclusion(f(x) eq f(y))
        proof {
            val xy = given(xy)
            val fn = lambda("t", s) { t -> f(x) eq f(t) }
            val step2 = infer(EqualityAxioms.substitution(fn, x, y), xy)
            val step3 = infer(EqualityAxioms.reflexivity(f(x)))
            infer(modusPonens(f(x) eq f(x), f(x) eq f(y)), step3, step2)
        }
    }
}
