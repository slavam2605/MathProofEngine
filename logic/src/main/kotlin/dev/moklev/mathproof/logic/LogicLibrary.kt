package dev.moklev.mathproof.logic

import dev.moklev.mathproof.core.statement
import dev.moklev.mathproof.logic.LogicAxioms.hilbertAxiom1
import dev.moklev.mathproof.logic.LogicAxioms.hilbertAxiom2
import dev.moklev.mathproof.logic.LogicAxioms.hilbertAxiom3
import dev.moklev.mathproof.logic.LogicAxioms.modusPonens
import dev.moklev.mathproof.model.CoreSorts

object LogicLibrary {
    val chainModusPonens2 = statement("chain-modus-ponens-2") {
        val p = parameter("p", CoreSorts.Proposition)
        val q = parameter("q", CoreSorts.Proposition)
        val r = parameter("r", CoreSorts.Proposition)

        val pPremise = premise(p)
        val qPremise = premise(q)
        val chainPremise = premise(p implies (q implies r))
        conclusion(r)
        proof {
            val givenP = given(pPremise)
            val givenQ = given(qPremise)
            val givenChain = given(chainPremise)
            val bridge = infer(modusPonens(p, q implies r), givenP, givenChain)
            infer(modusPonens(q, r), givenQ, bridge)
        }
    }

    val implicationIdentity = statement("implication-identity") {
        val p = parameter("p", CoreSorts.Proposition)

        conclusion(p implies p)
        proof {
            val liftPremise = infer(hilbertAxiom1(p, p implies p))
            val liftIdentity = infer(hilbertAxiom1(p, p))
            val distributeImplication = infer(hilbertAxiom2(p, p implies p, p))
            infer(
                chainModusPonens2(liftPremise.claim, liftIdentity.claim, p implies p),
                liftPremise,
                liftIdentity,
                distributeImplication,
            )
        }
    }

    val implicationFromConsequent = statement("implication-from-consequent") {
        val p = parameter("p", CoreSorts.Proposition)
        val q = parameter("q", CoreSorts.Proposition)

        val qPremise = premise(q)
        conclusion(p implies q)
        proof {
            val givenQ = given(qPremise)
            val lift = infer(hilbertAxiom1(q, p))
            infer(modusPonens(q, p implies q), givenQ, lift)
        }
    }

    val hypotheticalSyllogism = statement("hypothetical-syllogism") {
        val p = parameter("p", CoreSorts.Proposition)
        val q = parameter("q", CoreSorts.Proposition)
        val r = parameter("r", CoreSorts.Proposition)

        val pqPremise = premise(p implies q)
        val qrPremise = premise(q implies r)
        conclusion(p implies r)
        proof {
            val givenPq = given(pqPremise)
            val givenQr = given(qrPremise)
            val distribution = infer(hilbertAxiom2(p, q, r))
            val liftQr = infer(hilbertAxiom1(q implies r, p))
            val liftedQr = infer(
                modusPonens(q implies r, p implies (q implies r)),
                givenQr,
                liftQr,
            )
            infer(
                chainModusPonens2(p implies (q implies r), p implies q, p implies r),
                liftedQr,
                givenPq,
                distribution,
            )
        }
    }

    val internalizedModusPonens = statement("internalized-modus-ponens") {
        val p = parameter("p", CoreSorts.Proposition)
        val q = parameter("q", CoreSorts.Proposition)

        conclusion(p implies ((p implies q) implies q))
        proof {
            val projectPremise = infer(hilbertAxiom1(p, p implies q))
            val identity = infer(implicationIdentity(p implies q))
            val distribute = infer(hilbertAxiom2(p implies q, p, q))
            val implicationBridge = infer(
                modusPonens(
                    identity.claim,
                    ((p implies q) implies p) implies ((p implies q) implies q),
                ),
                identity,
                distribute,
            )
            infer(
                hypotheticalSyllogism(
                    p,
                    (p implies q) implies p,
                    (p implies q) implies q,
                ),
                projectPremise,
                implicationBridge,
            )
        }
    }

    val doubleNegationElimination = statement("double-negation-elimination") {
        val p = parameter("p", CoreSorts.Proposition)

        conclusion(!!p implies p)
        proof {
            val phi = infer(implicationIdentity(p)) // any tautology is needed here
            val step2 = infer(hilbertAxiom3(!p, !phi.claim))
            val step3 = infer(hilbertAxiom3(phi.claim, p))
            val step4 = infer(hypotheticalSyllogism(
                !!phi.claim implies !!p,
                !p implies !phi.claim,
                phi.claim implies p
            ), step2, step3)
            val step5 = infer(hilbertAxiom1(!!p, !!phi.claim))
            val step6 = infer(hypotheticalSyllogism(
                !!p, !!phi.claim implies !!p, phi.claim implies p
            ), step5, step4)
            val step7 = infer(internalizedModusPonens(phi.claim, p))
            val step8 = infer(modusPonens(phi.claim, (phi.claim implies p) implies p), phi, step7)
            infer(hypotheticalSyllogism(
                !!p, phi.claim implies p, p
            ), step6, step8)
        }
    }

    val doubleNegation = statement("double-negation") {
        val p = parameter("p", CoreSorts.Proposition)

        conclusion(p implies !!p)
        proof {
            val step1 = infer(doubleNegationElimination(!p))
            val step2 = infer(hilbertAxiom3(p, !!p))
            infer(modusPonens(!!!p implies !p, p implies !!p), step1, step2)
        }
    }

    val conjunctionFromPremises = statement("conjunction-from-premises") {
        val p = parameter("p", CoreSorts.Proposition)
        val q = parameter("q", CoreSorts.Proposition)

        val pPremise = premise(p)
        val qPremise = premise(q)
        conclusion(p and q)
        proof {
            val givenP = given(pPremise)
            val givenQ = given(qPremise)
            val intro = infer(LogicAxioms.andIntroduction(p, q))
            infer(
                chainModusPonens2(p, q, p and q),
                givenP,
                givenQ,
                intro,
            )
        }
    }

    val conjunctionLeftProjection = statement("conjunction-left-projection") {
        val p = parameter("p", CoreSorts.Proposition)
        val q = parameter("q", CoreSorts.Proposition)

        val pairPremise = premise(p and q)
        conclusion(p)
        proof {
            val givenPair = given(pairPremise)
            val elimination = infer(LogicAxioms.andEliminationLeft(p, q))
            infer(
                modusPonens(p and q, p),
                givenPair,
                elimination,
            )
        }
    }

    val conjunctionRightProjection = statement("conjunction-right-projection") {
        val p = parameter("p", CoreSorts.Proposition)
        val q = parameter("q", CoreSorts.Proposition)

        val pairPremise = premise(p and q)
        conclusion(q)
        proof {
            val givenPair = given(pairPremise)
            val elimination = infer(LogicAxioms.andEliminationRight(p, q))
            infer(
                modusPonens(p and q, q),
                givenPair,
                elimination,
            )
        }
    }

    /**
     * !p -> p -> q
     */
    val exFalso = statement("ex-falso-quodlibet") {
        val p = parameter("p", CoreSorts.Proposition)
        val q = parameter("q", CoreSorts.Proposition)

        conclusion(!p implies (p implies q))
        proof {
            val step1 = infer(hilbertAxiom1(!p, !q))
            val step2 = infer(hilbertAxiom3(p, q))
            infer(hypotheticalSyllogism(!p, !q implies !p, p implies q), step1, step2)
        }
    }

    /**
     * (!p -> p) -> p
     */
    val clavius = statement("clavius") {
        val p = parameter("p", CoreSorts.Proposition)
        conclusion((!p implies p) implies p)
        proof {
            assume(!p implies p) {
                val a = assumption.claim
                val step2 = infer(exFalso(p, !a))
                val step3 = infer(hilbertAxiom2(!p, p, !a))
                val step4 = infer(modusPonens(step2.claim, a implies (!p implies !a)), step2, step3)
                val step5 = infer(modusPonens(a, !p implies !a), assumption, step4)
                val step6 = infer(hilbertAxiom3(a, p))
                val step7 = infer(modusPonens(!p implies !a, a implies p), step5, step6)
                infer(modusPonens(a, p), assumption, step7)
            }
        }
    }

    val disjunctionLeftInjection = statement("disjunction-left-injection") {
        val p = parameter("p", CoreSorts.Proposition)
        val q = parameter("q", CoreSorts.Proposition)

        val pPremise = premise(p)
        conclusion(p or q)
        proof {
            val givenP = given(pPremise)
            val injection = infer(LogicAxioms.orIntroductionLeft(p, q))
            infer(
                modusPonens(p, p or q),
                givenP,
                injection,
            )
        }
    }

    val disjunctionRightInjection = statement("disjunction-right-injection") {
        val p = parameter("p", CoreSorts.Proposition)
        val q = parameter("q", CoreSorts.Proposition)

        val qPremise = premise(q)
        conclusion(p or q)
        proof {
            val givenQ = given(qPremise)
            val injection = infer(LogicAxioms.orIntroductionRight(p, q))
            infer(
                modusPonens(q, p or q),
                givenQ,
                injection,
            )
        }
    }

    val disjunctionEliminationFromPremises = statement("disjunction-elimination-from-premises") {
        val p = parameter("p", CoreSorts.Proposition)
        val q = parameter("q", CoreSorts.Proposition)
        val r = parameter("r", CoreSorts.Proposition)

        val disjunctionPremise = premise(p or q)
        val leftPremise = premise(p implies r)
        val rightPremise = premise(q implies r)
        conclusion(r)
        proof {
            val givenDisjunction = given(disjunctionPremise)
            val givenLeft = given(leftPremise)
            val givenRight = given(rightPremise)
            val elimination = infer(LogicAxioms.orElimination(p, q, r))
            val disjunctionCase = infer(
                chainModusPonens2(p implies r, q implies r, (p or q) implies r),
                givenLeft,
                givenRight,
                elimination,
            )
            infer(
                modusPonens(p or q, r),
                givenDisjunction,
                disjunctionCase,
            )
        }
    }
}
