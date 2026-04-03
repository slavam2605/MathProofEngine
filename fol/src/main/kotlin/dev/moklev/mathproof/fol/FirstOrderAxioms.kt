package dev.moklev.mathproof.fol

import dev.moklev.mathproof.core.functionSort
import dev.moklev.mathproof.core.lambda
import dev.moklev.mathproof.core.sortVariable
import dev.moklev.mathproof.core.statement
import dev.moklev.mathproof.logic.implies
import dev.moklev.mathproof.model.CoreSorts
import dev.moklev.mathproof.model.Expr
import dev.moklev.mathproof.model.Apply
import dev.moklev.mathproof.model.Bound
import dev.moklev.mathproof.model.Free
import dev.moklev.mathproof.model.Lambda

object FirstOrderAxioms {
    val forallInstantiation = statement("forall-instantiation") {
        val s = sortVariable("S")
        val predicate = parameter("predicate", functionSort(s, returns = CoreSorts.Proposition))
        val term = parameter("term", s)

        premise(FirstOrderFunctions.ForAll(predicate))
        conclusion(predicate(term))
        assumed("Trusted quantifier rule: a universal statement can be specialized to any term of the same sort.")
    }

    val existsIntroduction = statement("exists-introduction") {
        val s = sortVariable("S")
        val predicate = parameter("predicate", functionSort(s, returns = CoreSorts.Proposition))
        val witness = parameter("witness", s)

        premise(predicate(witness))
        conclusion(FirstOrderFunctions.Exists(predicate))
        assumed("Trusted quantifier rule: any explicit witness introduces an existential statement.")
    }

    val forallDistribution = statement("forall-distribution") {
        val s = sortVariable("S")
        val phi = parameter("phi", CoreSorts.Proposition)
        val psi = parameter("psi", functionSort(s, returns = CoreSorts.Proposition))

        premise(FirstOrderFunctions.ForAll(lambda("x", s) { x -> phi implies psi(x) }))
        conclusion(phi implies FirstOrderFunctions.ForAll(psi))
        instantiationCheck { arguments ->
            val actualPhi = arguments[0]
            require(!actualPhi.dependsOnImmediateOuterBinder()) {
                "Side condition for 'forall-distribution' failed: quantified variable 'x' must not be free in phi."
            }
        }
        assumed("Trusted quantifier schema: distribute implication through universal quantification when the quantified variable is not free in the antecedent.")
    }

    val existsEliminationSchema = statement("exists-elimination-schema") {
        val s = sortVariable("S")
        val phi = parameter("phi", functionSort(s, returns = CoreSorts.Proposition))
        val psi = parameter("psi", CoreSorts.Proposition)

        premise(FirstOrderFunctions.ForAll(lambda("x", s) { x -> phi(x) implies psi }))
        conclusion(FirstOrderFunctions.Exists(phi) implies psi)
        instantiationCheck { arguments ->
            val actualPsi = arguments[1]
            require(!actualPsi.dependsOnImmediateOuterBinder()) {
                "Side condition for 'exists-elimination-schema' failed: quantified variable 'x' must not be free in psi."
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
