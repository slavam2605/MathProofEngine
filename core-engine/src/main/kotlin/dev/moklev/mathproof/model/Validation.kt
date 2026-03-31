package dev.moklev.mathproof.model

fun requireProposition(expr: Expr, context: String) {
    require(expr.sort == CoreSorts.Proposition) {
        "$context must have sort '${CoreSorts.Proposition}', but got '${expr.sort}'."
    }
}

fun Expr.validationIssues(path: String = "expression"): List<String> {
    val issues = mutableListOf<String>()
    collectValidationIssues(path, issues, emptyList())
    return issues
}

private fun Expr.collectValidationIssues(
    path: String,
    issues: MutableList<String>,
    boundSorts: List<Sort>,
) {
    when (this) {
        is Free -> validateSort(sort, path, issues)
        is Bound -> {
            validateSort(sort, path, issues)
            val expectedSort = boundSorts.getOrNull(boundSorts.lastIndex - index)
            if (expectedSort == null) {
                issues += "$path refers to bound variable #$index outside the current lambda scope."
            } else if (!sortsCompatible(sort, expectedSort)) {
                issues += "$path refers to bound variable #$index of sort '$expectedSort', but stores '$sort'."
            }
        }
        is Lambda -> {
            validateSort(parameterSort, "$path binder", issues)
            body.collectValidationIssues("$path body", issues, boundSorts + parameterSort)
        }
        is Apply -> {
            validateSort(sort, path, issues)
            validateApplication(path).forEach(issues::add)
            function.collectValidationIssues("$path function", issues, boundSorts)
            argument.collectValidationIssues("$path argument", issues, boundSorts)
        }
    }
}

private fun validateSort(
    sort: Sort,
    path: String,
    issues: MutableList<String>,
) {
    if (!sort.isResolvedForVerification()) {
        issues += "$path has unresolved sort '$sort'."
    }
}

private fun Apply.validateApplication(path: String): List<String> {
    val issues = mutableListOf<String>()

    val functionSort = function.sort
    if (functionSort !is FunctionSort) {
        issues += "$path applies a non-function expression of sort '$functionSort'."
        return issues
    }

    val bindings = linkedMapOf<SortVariable, Sort>()
    if (!matchSort(functionSort.parameterSort, argument.sort, bindings)) {
        issues += "$path expects an argument of sort '${functionSort.parameterSort}', but got '${argument.sort}'."
        return issues
    }

    val resolvedResultSort = functionSort.resultSort.resolve(bindings)
    if (resolvedResultSort != sort) {
        issues += "$path infers result sort '$resolvedResultSort', but expression stores '$sort'."
    }

    return issues
}
