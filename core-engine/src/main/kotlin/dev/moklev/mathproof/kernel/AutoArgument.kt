package dev.moklev.mathproof.kernel

import dev.moklev.mathproof.model.Expr
import dev.moklev.mathproof.model.Free
import dev.moklev.mathproof.model.Sort
import dev.moklev.mathproof.model.SortVariable

private const val AUTO_ARGUMENT_SYMBOL_PREFIX = "__auto_argument__"

private object AutoArgumentIds {
    private var nextId = 0

    fun next(): Int {
        nextId += 1
        return nextId
    }
}

fun auto(): Expr {
    val id = AutoArgumentIds.next()
    return Free(
        symbol = "$AUTO_ARGUMENT_SYMBOL_PREFIX$id",
        sort = SortVariable("Auto$id"),
        displayName = "auto",
    )
}

internal fun Expr.isAutoArgument(): Boolean =
    this is Free && this.symbol.startsWith(AUTO_ARGUMENT_SYMBOL_PREFIX)

internal fun Expr.retargetAutoSort(sort: Sort): Expr =
    if (this is Free && this.isAutoArgument()) {
        this.copy(sort = sort)
    } else {
        this
    }
