package dev.moklev.mathproof.logic

import dev.moklev.mathproof.core.statement
import dev.moklev.mathproof.logic.LogicAxioms.hilbertAxiom1
import dev.moklev.mathproof.logic.LogicAxioms.hilbertAxiom2
import dev.moklev.mathproof.logic.LogicAxioms.hilbertAxiom3
import dev.moklev.mathproof.logic.LogicAxioms.modusPonens
import dev.moklev.mathproof.model.CoreSorts

object LogicLibrary {
    /**
     * `p, q, r: Proposition`
     *
     * `p, q, p -> q -> r ⊢ r`
     */
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

    /**
     * `p: Proposition`
     *
     * `p -> p`
     */
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

    /**
     * `p, q, r: Proposition`
     *
     * `(p -> q) -> (q -> r) -> p -> r`
     */
    val hypotheticalSyllogism = statement("hypothetical-syllogism") {
        val p = parameter("p", CoreSorts.Proposition)
        val q = parameter("q", CoreSorts.Proposition)
        val r = parameter("r", CoreSorts.Proposition)

        val pq = p implies q
        val qr = q implies r
        val pr = p implies r

        conclusion(pq implies (qr implies pr))
        proof {
            assume(pq) { givenPq ->
                assume(qr) { givenQr ->
                    val distribution = infer(hilbertAxiom2(p, q, r))
                    val liftQr = infer(hilbertAxiom1(qr, p))
                    val liftedQr = infer(modusPonens(qr, p implies qr), givenQr, liftQr)
                    val stepX = infer(modusPonens(p implies qr, pq implies pr), liftedQr, distribution)
                    infer(modusPonens(pq, pr), givenPq, stepX)
                }
            }
        }
    }

    /**
     * `p, q: Proposition`
     *
     * `p -> (p -> q) -> q`
     */
    val internalizedModusPonens = statement("internalized-modus-ponens") {
        val p = parameter("p", CoreSorts.Proposition)
        val q = parameter("q", CoreSorts.Proposition)

        val pq = p implies q

        conclusion(p implies (pq implies q))
        proof {
            val projectPremise = infer(hilbertAxiom1(p, pq))
            val identity = infer(implicationIdentity(pq))
            val distribute = infer(hilbertAxiom2(pq, p, q))
            val implicationBridge = infer(
                modusPonens(identity.claim, (pq implies p) implies (pq implies q)),
                identity,
                distribute
            )
            applyByMpChain(
                hypotheticalSyllogism(p, pq implies p, pq implies q),
                projectPremise,
                implicationBridge
            )
        }
    }

    /**
     * `p: Proposition`
     *
     * `!!p -> p`
     */
    val doubleNegationElimination = statement("double-negation-elimination") {
        val p = parameter("p", CoreSorts.Proposition)

        conclusion(!!p implies p)
        proof {
            val phi = infer(implicationIdentity(p)) // any tautology is needed here
            val step2 = infer(hilbertAxiom3(!p, !phi.claim))
            val step3 = infer(hilbertAxiom3(phi.claim, p))
            val step4 = applyByMpChain(hypotheticalSyllogism(
                !!phi.claim implies !!p,
                !p implies !phi.claim,
                phi.claim implies p
            ), step2, step3)
            val step5 = infer(hilbertAxiom1(!!p, !!phi.claim))
            val step6 = applyByMpChain(hypotheticalSyllogism(
                !!p, !!phi.claim implies !!p, phi.claim implies p
            ), step5, step4)
            val step7 = infer(internalizedModusPonens(phi.claim, p))
            val step8 = infer(modusPonens(phi.claim, (phi.claim implies p) implies p), phi, step7)
            applyByMpChain(hypotheticalSyllogism(
                !!p, phi.claim implies p, p
            ), step6, step8)
        }
    }

    /**
     * `p: Proposition`
     *
     * `p -> !!p`
     */
    val doubleNegation = statement("double-negation") {
        val p = parameter("p", CoreSorts.Proposition)

        conclusion(p implies !!p)
        proof {
            val step1 = infer(doubleNegationElimination(!p))
            val step2 = infer(hilbertAxiom3(p, !!p))
            infer(modusPonens(!!!p implies !p, p implies !!p), step1, step2)
        }
    }

    /**
     * `p, q: Proposition`
     *
     * `!p -> p -> q`
     */
    val exFalso = statement("ex-falso-quodlibet") {
        val p = parameter("p", CoreSorts.Proposition)
        val q = parameter("q", CoreSorts.Proposition)

        conclusion(!p implies (p implies q))
        proof {
            val step1 = infer(hilbertAxiom1(!p, !q))
            val step2 = infer(hilbertAxiom3(p, q))
            applyByMpChain(hypotheticalSyllogism(!p, !q implies !p, p implies q), step1, step2)
        }
    }

    /**
     * `p: Proposition`
     *
     * `(!p -> p) -> p`
     */
    val clavius = statement("clavius") {
        val p = parameter("p", CoreSorts.Proposition)
        conclusion((!p implies p) implies p)
        proof {
            assume(!p implies p) { assumption ->
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

    /**
     * `p, q: Proposition`
     *
     * `(p -> q) -> !q -> !p`
     */
    val contraposition = statement("contraposition") {
        val p = parameter("p", CoreSorts.Proposition)
        val q = parameter("q", CoreSorts.Proposition)

        conclusion((p implies q) implies (!q implies !p))
        proof {
            assume(p implies q) { pq ->
                assume(!q) { notQ ->
                    val nnPP = infer(doubleNegationElimination(p)) // !!p -> p
                    val nnPQ = applyByMpChain(hypotheticalSyllogism(!!p, p, q), nnPP, pq) // !!p -> q
                    val qnnQ = infer(doubleNegation(q)) // q -> !!q
                    val nnPnnQ = applyByMpChain(hypotheticalSyllogism(!!p, q, !!q), nnPQ, qnnQ) // !!p -> !!q
                    val h3 = infer(hilbertAxiom3(!q, !p)) // (!!p -> !!q) -> (!q -> !p)
                    val nQnP = infer(modusPonens(!!p implies !!q, !q implies !p), nnPnnQ, h3) // !q -> !p
                    infer(modusPonens(!q, !p), notQ, nQnP) // !p
                }
            }
        }
    }
}
