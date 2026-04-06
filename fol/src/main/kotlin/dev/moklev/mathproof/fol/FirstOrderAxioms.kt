package dev.moklev.mathproof.fol

import dev.moklev.mathproof.core.functionSort
import dev.moklev.mathproof.core.lambda
import dev.moklev.mathproof.core.sortVariable
import dev.moklev.mathproof.core.statement
import dev.moklev.mathproof.fol.FirstOrderFunctions.Exists
import dev.moklev.mathproof.fol.FirstOrderFunctions.ForAll
import dev.moklev.mathproof.logic.implies
import dev.moklev.mathproof.model.CoreSorts
import dev.moklev.mathproof.model.Expr
import dev.moklev.mathproof.model.Apply
import dev.moklev.mathproof.model.Bound
import dev.moklev.mathproof.model.Free
import dev.moklev.mathproof.model.Lambda

object FirstOrderAxioms {
    /**
     * `p: S -> Proposition, a: S`
     *
     * `(∀x. p(x)) -> p(a)`
     */
    val forallInstantiation = statement("forall-instantiation") {
        val s = sortVariable("S")
        val predicate = parameter("predicate", functionSort(s, returns = CoreSorts.Proposition))
        val term = parameter("term", s)

        conclusion(ForAll(predicate) implies predicate(term))
        assumed("Trusted quantifier rule: a universal statement can be specialized to any term of the same sort.")
    }

    /**
     * `p: S -> Proposition, a: S`
     *
     * `p(a) -> ∃x. p(x)`
     */
    val existsIntroduction = statement("exists-introduction") {
        val s = sortVariable("S")
        val predicate = parameter("predicate", functionSort(s, returns = CoreSorts.Proposition))
        val witness = parameter("witness", s)

        conclusion(predicate(witness) implies Exists(predicate))
        assumed("Trusted quantifier schema: if a witness satisfies a predicate, then an existential statement holds.")
    }

    /**
     * `p: Proposition, q: S -> Proposition`
     *
     * `(∀x. p -> q(x)) -> p -> ∀x. q(x)`
     */
    val forallDistribution = statement("forall-distribution") {
        val s = sortVariable("S")
        val p = parameter("p", CoreSorts.Proposition)
        val q = parameter("q", functionSort(s, returns = CoreSorts.Proposition))

        conclusion(ForAll(lambda("x", s) { x -> p implies q(x) }) implies (p implies ForAll(q)))
        instantiationCheck { arguments ->
            val actualPhi = arguments[0]
            require(!actualPhi.dependsOnImmediateOuterBinder()) {
                "Side condition for 'forall-distribution' failed: quantified variable 'x' must not be free in phi."
            }
        }
        assumed("Trusted quantifier schema: distribute implication through universal quantification when the quantified variable is not free in the antecedent.")
    }

    /**
     * `p: S -> Proposition, q: Proposition`
     *
     * `(∀x. p(x) -> q) -> (∃x. p(x)) -> q`
     */
    val existsElimination = statement("exists-elimination") {
        val s = sortVariable("S")
        val p = parameter("p", functionSort(s, returns = CoreSorts.Proposition))
        val q = parameter("q", CoreSorts.Proposition)

        conclusion(ForAll(lambda("x", s) { x -> p(x) implies q }) implies (Exists(p) implies q))
        instantiationCheck { arguments ->
            val actualPsi = arguments[1]
            require(!actualPsi.dependsOnImmediateOuterBinder()) {
                "Side condition for 'exists-elimination' failed: quantified variable 'x' must not be free in psi."
            }
        }
        assumed("Trusted quantifier schema: eliminate existential quantification through a universally quantified implication when the quantified variable is not free in the conclusion.")
    }
}

private fun Expr.dependsOnImmediateOuterBinder(depth: Int = 0): Boolean = when (this) {
    is Free -> false
    is Bound -> index == depth
    is Lambda -> body.dependsOnImmediateOuterBinder(depth + 1)
    is Apply -> function.dependsOnImmediateOuterBinder(depth) || argument.dependsOnImmediateOuterBinder(depth)
}
