package dev.moklev.mathproof.logic

import dev.moklev.mathproof.core.statement
import dev.moklev.mathproof.model.CoreSorts

object LogicAxioms {
    /**
     * `p, q: Proposition`
     *
     * `p, p -> q ⊢ q`
     */
    val modusPonens = statement("modus-ponens") {
        val p = parameter("p", CoreSorts.Proposition)
        val q = parameter("q", CoreSorts.Proposition)

        premise(p)
        premise(p implies q)
        conclusion(q)
        assumed("Primitive derivation rule in the trusted logical basis.")
    }

    /**
     * `p, q: Proposition`
     *
     * `p -> q -> p`
     */
    val hilbertAxiom1 = statement("hilbert-a1") {
        val p = parameter("p", CoreSorts.Proposition)
        val q = parameter("q", CoreSorts.Proposition)

        conclusion(p implies (q implies p))
        assumed("Hilbert axiom schema A1 for classical propositional logic. Trusted as an axiom.")
    }

    /**
     * `p, q, r: Proposition`
     *
     * `(p -> q -> r) -> (p -> q) -> p -> r`
     */
    val hilbertAxiom2 = statement("hilbert-a2") {
        val p = parameter("p", CoreSorts.Proposition)
        val q = parameter("q", CoreSorts.Proposition)
        val r = parameter("r", CoreSorts.Proposition)

        conclusion((p implies (q implies r)) implies ((p implies q) implies (p implies r)))
        assumed("Hilbert axiom schema A2 for classical propositional logic. Trusted as an axiom.")
    }

    /**
     * `p, q: Proposition`
     *
     * `(!q -> !p) -> p -> q`
     */
    val hilbertAxiom3 = statement("hilbert-a3") {
        val p = parameter("p", CoreSorts.Proposition)
        val q = parameter("q", CoreSorts.Proposition)

        conclusion(((!q) implies (!p)) implies (p implies q))
        assumed("Hilbert axiom schema A3 for classical propositional logic. Trusted as an axiom.")
    }

    /**
     * `p, q: Proposition`
     *
     * `(p and q) -> p`
     */
    val andEliminationLeft = statement("and-elimination-left") {
        val p = parameter("p", CoreSorts.Proposition)
        val q = parameter("q", CoreSorts.Proposition)

        conclusion((p and q) implies p)
        assumed("Minimal Hilbert-style axiom schema for conjunction. Trusted as an axiom.")
    }

    /**
     * `p, q: Proposition`
     *
     * `(p and q) -> q`
     */
    val andEliminationRight = statement("and-elimination-right") {
        val p = parameter("p", CoreSorts.Proposition)
        val q = parameter("q", CoreSorts.Proposition)

        conclusion((p and q) implies q)
        assumed("Minimal Hilbert-style axiom schema for conjunction. Trusted as an axiom.")
    }

    /**
     * `p, q: Proposition`
     *
     * `p -> q -> (p and q)`
     */
    val andIntroduction = statement("and-introduction") {
        val p = parameter("p", CoreSorts.Proposition)
        val q = parameter("q", CoreSorts.Proposition)

        conclusion(p implies (q implies (p and q)))
        assumed("Minimal Hilbert-style axiom schema for conjunction. Trusted as an axiom.")
    }

    /**
     * `p, q: Proposition`
     *
     * `p -> (p or q)`
     */
    val orIntroductionLeft = statement("or-introduction-left") {
        val p = parameter("p", CoreSorts.Proposition)
        val q = parameter("q", CoreSorts.Proposition)

        conclusion(p implies (p or q))
        assumed("Minimal Hilbert-style axiom schema for disjunction. Trusted as an axiom.")
    }

    /**
     * `p, q: Proposition`
     *
     * `q -> (p or q)`
     */
    val orIntroductionRight = statement("or-introduction-right") {
        val p = parameter("p", CoreSorts.Proposition)
        val q = parameter("q", CoreSorts.Proposition)

        conclusion(q implies (p or q))
        assumed("Minimal Hilbert-style axiom schema for disjunction. Trusted as an axiom.")
    }

    /**
     * `p, q, r: Proposition`
     *
     * `(p -> r) -> (q -> r) -> (p or q) -> r`
     */
    val orElimination = statement("or-elimination") {
        val p = parameter("p", CoreSorts.Proposition)
        val q = parameter("q", CoreSorts.Proposition)
        val r = parameter("r", CoreSorts.Proposition)

        conclusion((p implies r) implies ((q implies r) implies ((p or q) implies r)))
        assumed("Minimal Hilbert-style axiom schema for disjunction. Trusted as an axiom.")
    }
}
