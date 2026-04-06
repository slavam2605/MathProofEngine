package dev.moklev.mathproof.examples

import dev.moklev.mathproof.core.functionSort
import dev.moklev.mathproof.core.sortVariable
import dev.moklev.mathproof.core.statement
import dev.moklev.mathproof.equality.EqualityLibrary
import dev.moklev.mathproof.equality.eq
import dev.moklev.mathproof.logic.LogicAxioms.andEliminationLeft
import dev.moklev.mathproof.logic.LogicAxioms.andEliminationRight
import dev.moklev.mathproof.logic.LogicAxioms.andIntroduction
import dev.moklev.mathproof.logic.and
import dev.moklev.mathproof.logic.applyByMpChain
import dev.moklev.mathproof.model.CoreSorts

object SampleProofs {
    val commutedConjunction = statement("commuted-conjunction") {
        val p = parameter("p", CoreSorts.Proposition)
        val q = parameter("q", CoreSorts.Proposition)

        val pairPremise = premise(p and q)
        conclusion(q and p)
        proof {
            val pair = given(pairPremise)
            val right = applyByMpChain(andEliminationRight(p, q), pair)
            val left = applyByMpChain(andEliminationLeft(p, q), pair)
            applyByMpChain(andIntroduction(q, p), right, left)
        }
    }

    val functionRespectsSharedEquality = statement("function-respects-shared-equality") {
        val s = sortVariable("S")
        val t = sortVariable("T")
        val f = parameter("f", functionSort(s, returns = t))
        val x = parameter("x", s)
        val y = parameter("y", s)
        val z = parameter("z", s)

        val xy = premise(x eq y)
        val zy = premise(z eq y)
        conclusion(f(x) eq f(z))
        proof {
            val givenXy = given(xy)
            val givenZy = given(zy)
            val yz = infer(EqualityLibrary.symmetry(z, y), givenZy)
            val fxFy = infer(EqualityLibrary.congruence(f, x, y), givenXy)
            val fyFz = infer(EqualityLibrary.congruence(f, y, z), yz)
            infer(EqualityLibrary.transitivity(f(x), f(y), f(z)), fxFy, fyFz)
        }
    }

    val all = listOf(
        commutedConjunction,
        functionRespectsSharedEquality,
    )
}
