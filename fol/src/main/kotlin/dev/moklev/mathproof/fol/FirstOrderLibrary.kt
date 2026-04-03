package dev.moklev.mathproof.fol

import dev.moklev.mathproof.core.functionSort
import dev.moklev.mathproof.core.lambda
import dev.moklev.mathproof.core.sortVariable
import dev.moklev.mathproof.core.statement
import dev.moklev.mathproof.logic.LogicAxioms
import dev.moklev.mathproof.logic.implies
import dev.moklev.mathproof.model.CoreSorts

object FirstOrderLibrary {
    val universalImpliesExistentialForWitness = statement("universal-implies-existential-for-witness") {
        val s = sortVariable("S")
        val predicate = parameter("predicate", functionSort(s, returns = CoreSorts.Proposition))
        val witness = parameter("witness", s)

        val allPredicate = premise(FirstOrderFunctions.ForAll(predicate))
        conclusion(FirstOrderFunctions.Exists(predicate))
        proof {
            val universal = given(allPredicate)
            val witnessFact = infer(FirstOrderAxioms.forallInstantiation(predicate, witness), universal)
            infer(FirstOrderAxioms.existsIntroduction(predicate, witness), witnessFact)
        }
    }

    val existentialEliminationFromPremises = statement("existential-elimination-from-premises") {
        val s = sortVariable("S")
        val predicate = parameter("predicate", functionSort(s, returns = CoreSorts.Proposition))
        val consequence = parameter("consequence", CoreSorts.Proposition)

        val implicationPremise = premise(FirstOrderFunctions.ForAll(lambda("x", s) { x ->
            predicate(x) implies consequence
        }))
        val existencePremise = premise(FirstOrderFunctions.Exists(predicate))
        conclusion(consequence)
        proof {
            val universalImplication = given(implicationPremise)
            val existential = given(existencePremise)
            val implicationToConsequence = infer(
                FirstOrderAxioms.existsEliminationSchema(predicate, consequence),
                universalImplication,
            )
            infer(LogicAxioms.modusPonens(FirstOrderFunctions.Exists(predicate), consequence), existential, implicationToConsequence)
        }
    }

    val guardedUniversalFromPremises = statement("guarded-universal-from-premises") {
        val s = sortVariable("S")
        val guard = parameter("guard", CoreSorts.Proposition)
        val predicate = parameter("predicate", functionSort(s, returns = CoreSorts.Proposition))

        val guardedPremise = premise(FirstOrderFunctions.ForAll(lambda("x", s) { x ->
            guard implies predicate(x)
        }))
        val guardPremise = premise(guard)
        conclusion(FirstOrderFunctions.ForAll(predicate))
        proof {
            val guardedUniversal = given(guardedPremise)
            val guardFact = given(guardPremise)
            val implicationToUniversal = infer(FirstOrderAxioms.forallDistribution(guard, predicate), guardedUniversal)
            infer(LogicAxioms.modusPonens(guard, FirstOrderFunctions.ForAll(predicate)), guardFact, implicationToUniversal)
        }
    }
}
