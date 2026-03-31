package dev.moklev.mathproof.examples

import dev.moklev.mathproof.core.statement
import dev.moklev.mathproof.logic.LogicLibrary
import dev.moklev.mathproof.logic.and
import dev.moklev.mathproof.model.CoreSorts

object SampleProofs {
    val commutedConjunction = statement("commuted-conjunction") {
        val p = parameter("p", CoreSorts.Proposition)
        val q = parameter("q", CoreSorts.Proposition)

        val pairPremise = premise(p and q)
        conclusion(q and p)
        proof {
            val pair = given(pairPremise)
            val right = infer(LogicLibrary.conjunctionRightProjection(p, q), pair)
            val left = infer(LogicLibrary.conjunctionLeftProjection(p, q), pair)
            infer(
                LogicLibrary.conjunctionFromPremises(q, p),
                right,
                left,
            )
        }
    }

    val all = listOf(
        commutedConjunction,
    )
}
