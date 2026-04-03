package dev.moklev.mathproof.fol

import dev.moklev.mathproof.core.function
import dev.moklev.mathproof.core.functionSort
import dev.moklev.mathproof.core.lambda
import dev.moklev.mathproof.core.sortVariable
import dev.moklev.mathproof.model.CoreSorts
import dev.moklev.mathproof.model.Expr
import dev.moklev.mathproof.model.Sort

object FirstOrderFunctions {
    private val operandSort = sortVariable("S")

    val ForAll = function("forall", functionSort(operandSort, returns = CoreSorts.Proposition), returns = CoreSorts.Proposition)
    val Exists = function("exists", functionSort(operandSort, returns = CoreSorts.Proposition), returns = CoreSorts.Proposition)
}

fun forall(
    name: String,
    sort: Sort,
    bodyBuilder: (Expr) -> Expr,
): Expr = FirstOrderFunctions.ForAll(quantifiedPredicate(name, sort, bodyBuilder))

fun exists(
    name: String,
    sort: Sort,
    bodyBuilder: (Expr) -> Expr,
): Expr = FirstOrderFunctions.Exists(quantifiedPredicate(name, sort, bodyBuilder))

private fun quantifiedPredicate(
    name: String,
    sort: Sort,
    bodyBuilder: (Expr) -> Expr,
): Expr {
    val predicate = lambda(name, sort, bodyBuilder)
    require(predicate.sort == functionSort(sort, returns = CoreSorts.Proposition)) {
        "Quantifier body must build a proposition-valued predicate."
    }
    return predicate
}
