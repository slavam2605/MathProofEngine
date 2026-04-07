package dev.moklev.mathproof.equality

import dev.moklev.mathproof.core.functionSort
import dev.moklev.mathproof.core.lambda
import dev.moklev.mathproof.core.sortVariable
import dev.moklev.mathproof.core.statement
import dev.moklev.mathproof.logic.LogicAxioms.modusPonens
import dev.moklev.mathproof.logic.assume
import dev.moklev.mathproof.logic.implies

object EqualityLibrary {
    /**
     * `x, y: S`
     *
     * `(x = y) -> (y = x)`
     */
    val symmetry = statement("equality-symmetric") {
        val s = sortVariable("S")
        val x = parameter("x", s)
        val y = parameter("y", s)

        conclusion((x eq y) implies (y eq x))
        proof {
            assume(x eq y) { xy ->
                val f = lambda("t", s) { t -> t eq x }
                val step1 = applyByMpChain(EqualityAxioms.substitution(f, x, y), xy)
                val step2 = infer(EqualityAxioms.reflexivity(x))
                infer(modusPonens(x eq x, y eq x), step2, step1)
            }
        }
    }

    /**
     * `x, y, z: S`
     *
     * `(x = y) -> (y = z) -> (x = z)`
     */
    val transitivity = statement("equality-transitive") {
        val s = sortVariable("S")
        val x = parameter("x", s)
        val y = parameter("y", s)
        val z = parameter("z", s)

        conclusion((x eq y) implies ((y eq z) implies (x eq z)))
        proof {
            assume(x eq y) { xy ->
                assume(y eq z) { yz ->
                    val yx = applyByMpChain(symmetry(x, y), xy)
                    val f = lambda("t", s) { t -> t eq z }
                    val step4 = applyByMpChain(EqualityAxioms.substitution(f, y, x), yx)
                    infer(modusPonens(y eq z, x eq z), yz, step4)
                }
            }
        }
    }

    /**
     * `f: S -> T, x, y: S`
     *
     * `(x = y) -> (f(x) = f(y))`
     */
    val congruence = statement("equality-congruence") {
        val s = sortVariable("S")
        val t = sortVariable("T")
        val f = parameter("f", functionSort(s, returns = t))
        val x = parameter("x", s)
        val y = parameter("y", s)

        conclusion((x eq y) implies (f(x) eq f(y)))
        proof {
            assume(x eq y) { xy ->
                val fn = lambda("t", s) { t -> f(x) eq f(t) }
                val step2 = applyByMpChain(EqualityAxioms.substitution(fn, x, y), xy)
                val step3 = infer(EqualityAxioms.reflexivity(f(x)))
                infer(modusPonens(f(x) eq f(x), f(x) eq f(y)), step3, step2)
            }
        }
    }
}
