package dev.moklev.mathproof.fol

import dev.moklev.mathproof.core.functionSort
import dev.moklev.mathproof.core.lambda
import dev.moklev.mathproof.core.sortVariable
import dev.moklev.mathproof.core.statement
import dev.moklev.mathproof.logic.LogicAxioms.modusPonens
import dev.moklev.mathproof.logic.LogicLibrary
import dev.moklev.mathproof.logic.LogicLibrary.contraposition
import dev.moklev.mathproof.logic.LogicLibrary.doubleNegationElimination
import dev.moklev.mathproof.logic.LogicLibrary.hypotheticalSyllogism
import dev.moklev.mathproof.logic.applyByMpChain
import dev.moklev.mathproof.logic.assume
import dev.moklev.mathproof.logic.implies
import dev.moklev.mathproof.logic.not
import dev.moklev.mathproof.model.CoreSorts

object FirstOrderLibrary {
    /**
     * `p: S -> Proposition`
     *
     * `(!∃x. !p(x)) -> ∀x. p(x)`
     */
    val negationExistsNegation = statement("forall-negation") {
        val s = sortVariable("S")
        val p = parameter("p", functionSort(s, returns = CoreSorts.Proposition))

        conclusion(!exists("x", s) { x -> !p(x) } implies forall("x", s) { x -> p(x) })
        proof {
            assume(!exists("x", s) { x -> !p(x) }) { notExists ->
                forAllByGeneralization("a", s) { a ->
                    contradiction(!p(a)) { notPa ->
                        val step1 = applyByMpChain(FirstOrderAxioms.existsIntroduction(
                            lambda("x", s) { x -> !p(x) }, a
                        ), notPa)
                        applyByMpChain(LogicLibrary.exFalso(step1.claim, p(a)), notExists, step1)
                    }
                }
            }

        }
    }

    /**
     * `p: S -> Proposition`
     *
     * `(!∀x. p(x)) -> ∃x. !p(x)`
     */
    val forallNegation = statement("forall-negation") {
        val s = sortVariable("S")
        val p = parameter("p", functionSort(s, returns = CoreSorts.Proposition))

        conclusion(!forall("x", s) { x -> p(x) } implies exists("x", s) { x -> !p(x) })
        proof {
            val fa = forall("x", s) { x -> p(x) }
            val ex = exists("x", s) { x -> !p(x) }

            val notExists = infer(negationExistsNegation(p))
            val contr = infer(contraposition(!ex, fa))
            val nFnnE = infer(modusPonens(notExists.claim, !fa implies !!ex), notExists, contr)
            val doubleN = infer(doubleNegationElimination(ex))
            applyByMpChain(hypotheticalSyllogism(!fa, !!ex, ex), nFnnE, doubleN)
        }
    }
}
