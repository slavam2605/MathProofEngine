package dev.moklev.mathproof.model

sealed interface Sort

data class NamedSort(val name: String) : Sort {
    override fun toString(): String = name
}

data class SortVariable(val name: String) : Sort {
    override fun toString(): String = name
}

data class FunctionSort(
    val parameterSort: Sort,
    val resultSort: Sort,
) : Sort {
    override fun toString(): String =
        "${parameterSort.renderAsFunctionArgument()} -> $resultSort"
}

object CoreSorts {
    val Proposition: Sort = NamedSort("Proposition")
}

typealias SortBindings = Map<SortVariable, Sort>

fun Sort.resolve(bindings: SortBindings): Sort = when (this) {
    is SortVariable -> bindings[this]?.let { bound ->
        if (bound == this) {
            this
        } else {
            bound.resolve(bindings)
        }
    } ?: this
    is FunctionSort -> FunctionSort(
        parameterSort = parameterSort.resolve(bindings),
        resultSort = resultSort.resolve(bindings),
    )
    else -> this
}

fun Sort.isResolvedForVerification(): Boolean = when (this) {
    is FunctionSort -> parameterSort.isResolvedForVerification() && resultSort.isResolvedForVerification()
    else -> true
}

fun matchSort(
    expected: Sort,
    actual: Sort,
    bindings: MutableMap<SortVariable, Sort>,
): Boolean {
    val resolvedExpected = expected.resolve(bindings)
    val resolvedActual = actual.resolve(bindings)

    if (resolvedExpected == resolvedActual) {
        return true
    }

    return when {
        resolvedExpected is SortVariable -> bindSortVariable(resolvedExpected, resolvedActual, bindings)
        resolvedActual is SortVariable -> bindSortVariable(resolvedActual, resolvedExpected, bindings)
        resolvedExpected is FunctionSort && resolvedActual is FunctionSort ->
            matchSort(resolvedExpected.parameterSort, resolvedActual.parameterSort, bindings) &&
                matchSort(resolvedExpected.resultSort, resolvedActual.resultSort, bindings)
        else -> false
    }
}

fun unifySorts(expected: List<Sort>, actual: List<Sort>): SortBindings? {
    if (expected.size != actual.size) {
        return null
    }

    val bindings = linkedMapOf<SortVariable, Sort>()
    expected.zip(actual).forEach { (expectedSort, actualSort) ->
        if (!matchSort(expectedSort, actualSort, bindings)) {
            return null
        }
    }
    return bindings.toMap()
}

fun sortsCompatible(left: Sort, right: Sort): Boolean =
    unifySorts(listOf(left), listOf(right)) != null

private fun bindSortVariable(
    variable: SortVariable,
    sort: Sort,
    bindings: MutableMap<SortVariable, Sort>,
): Boolean {
    if (sort == variable) {
        return true
    }
    if (sort.containsSortVariable(variable, bindings)) {
        return false
    }
    bindings[variable] = sort
    return true
}

private fun Sort.containsSortVariable(
    target: SortVariable,
    bindings: SortBindings,
): Boolean = when (val resolved = resolve(bindings)) {
    target -> true
    is FunctionSort -> resolved.parameterSort.containsSortVariable(target, bindings) ||
        resolved.resultSort.containsSortVariable(target, bindings)
    else -> false
}

private fun Sort.renderAsFunctionArgument(): String =
    if (this is FunctionSort) "($this)" else toString()
