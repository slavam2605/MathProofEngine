package dev.moklev.mathproof.equality

import dev.moklev.mathproof.core.functionSort
import dev.moklev.mathproof.core.sortVariable
import dev.moklev.mathproof.core.statement
import dev.moklev.mathproof.logic.implies
import dev.moklev.mathproof.model.CoreSorts

object EqualityAxioms {
    /**
     * `x: S`
     *
     * `x = x`
     */
    val reflexivity = statement("equality-identity") {
        val s = sortVariable("S")
        val x = parameter("x", s)

        conclusion(x eq x)
        assumed("Trusted equality axiom schema: every term is equal to itself.")
    }

    /**
     * `f: S -> Proposition, x, y: S`
     *
     * `(x = y) -> f(x) -> f(y)`
     */
    val substitution = statement("equality-substitution") {
        val s = sortVariable("S")
        val f = parameter("f", functionSort(s, returns = CoreSorts.Proposition))
        val x = parameter("x", s)
        val y = parameter("y", s)

        conclusion((x eq y) implies (f(x) implies f(y)))
        assumed("Trusted equality axiom schema: Leibniz's law")
    }
}
