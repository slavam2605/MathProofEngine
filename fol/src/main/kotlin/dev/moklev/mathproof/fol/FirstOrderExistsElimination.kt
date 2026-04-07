package dev.moklev.mathproof.fol

import dev.moklev.mathproof.kernel.Fact
import dev.moklev.mathproof.kernel.ProofBuilder
import dev.moklev.mathproof.logic.AssumptionScope
import dev.moklev.mathproof.logic.LogicAxioms
import dev.moklev.mathproof.logic.LogicFunctions
import dev.moklev.mathproof.logic.ScopedFact
import dev.moklev.mathproof.logic.applyByMpChain
import dev.moklev.mathproof.logic.assume
import dev.moklev.mathproof.model.Apply
import dev.moklev.mathproof.model.Bound
import dev.moklev.mathproof.model.CoreSorts
import dev.moklev.mathproof.model.Expr
import dev.moklev.mathproof.model.FunctionSort
import dev.moklev.mathproof.model.Free
import dev.moklev.mathproof.model.Lambda
import dev.moklev.mathproof.model.Sort

fun ProofBuilder.eliminateExists(
    existsExpr: Expr,
    variableName: String = "x",
    proveAt: AssumptionScope.(Free, ScopedFact) -> Unit,
): Fact {
    val predicate = existsExpr.requireExistsPredicate("eliminateExists")
    val witness = arbitrary(variableName, predicate.witnessSort)
    val witnessToResult = assume(predicate.expr(witness)) { witnessFact ->
        proveAt(witness, witnessFact)
    }
    val result = requireWitnessIndependentResult(
        witness = witness,
        implicationClaim = witnessToResult.claim,
    )
    val generalizedImplication = generalizeForAll(witness, witnessToResult)
    return applyByMpChain(
        FirstOrderAxioms.existsElimination(predicate.expr, result),
        generalizedImplication,
    )
}

fun ProofBuilder.eliminateExists(
    existsFact: Fact,
    variableName: String = "x",
    proveAt: AssumptionScope.(Free, ScopedFact) -> Unit,
): Fact {
    val implication = eliminateExists(
        existsExpr = existsFact.claim,
        variableName = variableName,
        proveAt = proveAt,
    )
    return infer(
        LogicAxioms.modusPonens(existsFact.claim, implication.claim.requireImplicationConsequent("eliminateExists")),
        existsFact,
        implication,
    )
}

fun AssumptionScope.eliminateExists(
    existsExpr: Expr,
    variableName: String = "x",
    proveAt: AssumptionScope.(Free, ScopedFact) -> Unit,
): ScopedFact {
    val predicate = existsExpr.requireExistsPredicate("eliminateExists")
    val witness = arbitrary(variableName, predicate.witnessSort)
    val witnessToResult = assume(predicate.expr(witness)) { witnessFact ->
        proveAt(witness, witnessFact)
    }
    val result = requireWitnessIndependentResult(
        witness = witness,
        implicationClaim = witnessToResult.claim,
    )
    val generalizedImplication = generalizeForAll(witness, witnessToResult)
    return applyByMpChain(
        FirstOrderAxioms.existsElimination(predicate.expr, result),
        generalizedImplication,
    )
}

fun AssumptionScope.eliminateExists(
    existsFact: ScopedFact,
    variableName: String,
    proveAt: AssumptionScope.(Free, ScopedFact) -> Unit,
): ScopedFact {
    val existsInScope = given(existsFact)
    val implication = eliminateExists(
        existsExpr = existsInScope.claim,
        variableName = variableName,
        proveAt = proveAt,
    )
    return infer(
        LogicAxioms.modusPonens(existsInScope.claim, implication.claim.requireImplicationConsequent("eliminateExists")),
        existsInScope,
        implication,
    )
}

private data class ExistsPredicate(
    val expr: Expr,
    val witnessSort: Sort,
)

private fun Expr.requireExistsPredicate(apiName: String): ExistsPredicate {
    val quantified = this as? Apply
        ?: throw IllegalArgumentException("$apiName expects an existential claim like '∃x. p(x)', but got '$this'.")
    require(quantified.function == FirstOrderFunctions.Exists) {
        "$apiName expects an existential claim like '∃x. p(x)', but got '$this'."
    }
    val predicate = quantified.argument
    val predicateSort = predicate.sort as? FunctionSort
        ?: throw IllegalArgumentException(
            "$apiName expects an existential predicate of sort 'S -> Proposition', but got '$predicate' with sort '${predicate.sort}'.",
        )
    require(predicateSort.resultSort == CoreSorts.Proposition) {
        "$apiName expects an existential predicate of sort 'S -> Proposition', but got '$predicate' with sort '${predicate.sort}'."
    }
    return ExistsPredicate(
        expr = predicate,
        witnessSort = predicateSort.parameterSort,
    )
}

private fun requireWitnessIndependentResult(
    witness: Free,
    implicationClaim: Expr,
): Expr {
    val result = implicationClaim.requireImplicationConsequent("eliminateExists")
    require(!result.containsFreeSymbol(witness.symbol)) {
        "eliminateExists is invalid: witness '${witness.displayName}' is free in the derived conclusion '$result'. " +
            "Existential elimination requires the conclusion to be independent from the chosen witness."
    }
    return result
}

private fun Expr.requireImplicationConsequent(apiName: String): Expr {
    val implication = this as? Apply
        ?: throw IllegalArgumentException("$apiName expected an implication claim, but got '$this'.")
    val implicationHead = implication.function as? Apply
        ?: throw IllegalArgumentException("$apiName expected an implication claim, but got '$this'.")
    require(implicationHead.function == LogicFunctions.Implies) {
        "$apiName expected an implication claim, but got '$this'."
    }
    return implication.argument
}

private fun Expr.containsFreeSymbol(symbol: String): Boolean = when (this) {
    is Free -> this.symbol == symbol
    is Bound -> false
    is Lambda -> body.containsFreeSymbol(symbol)
    is Apply -> function.containsFreeSymbol(symbol) || argument.containsFreeSymbol(symbol)
}
