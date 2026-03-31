package dev.moklev.mathproof.core

import dev.moklev.mathproof.kernel.StatementBuilder
import dev.moklev.mathproof.kernel.StatementDefinition
import dev.moklev.mathproof.model.Expr
import dev.moklev.mathproof.model.Free
import dev.moklev.mathproof.model.FunctionSort
import dev.moklev.mathproof.model.Lambda
import dev.moklev.mathproof.model.Sort
import dev.moklev.mathproof.model.SortVariable
import dev.moklev.mathproof.model.abstract
import dev.moklev.mathproof.model.freshFree

fun free(name: String, sort: Sort): Free =
    Free(symbol = name, sort = sort, displayName = name)

fun constant(name: String, sort: Sort): Free = free(name, sort)

fun function(name: String, vararg argumentSorts: Sort, returns: Sort): Free =
    constant(name, functionSort(*argumentSorts, returns = returns))

fun functionSort(vararg argumentSorts: Sort, returns: Sort): FunctionSort {
    require(argumentSorts.isNotEmpty()) { "Function sorts need at least one argument sort." }

    fun build(index: Int): FunctionSort =
        if (index == argumentSorts.lastIndex) {
            FunctionSort(argumentSorts[index], returns)
        } else {
            FunctionSort(argumentSorts[index], build(index + 1))
        }

    return build(0)
}

fun sortVariable(name: String): Sort = SortVariable(name)

fun lambda(
    name: String,
    sort: Sort,
    bodyBuilder: (Expr) -> Expr,
): Expr {
    val placeholder = freshFree(name, sort, namespace = "lambda")
    val body = bodyBuilder(placeholder).abstract(placeholder)
    return Lambda(parameterSort = sort, body = body, parameterHint = name)
}

fun statement(name: String, block: StatementBuilder.() -> Unit): StatementDefinition =
    StatementBuilder(name).apply(block).build()
