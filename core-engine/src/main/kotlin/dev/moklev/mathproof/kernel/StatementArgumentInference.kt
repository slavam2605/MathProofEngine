package dev.moklev.mathproof.kernel

import dev.moklev.mathproof.model.Apply
import dev.moklev.mathproof.model.Bound
import dev.moklev.mathproof.model.Expr
import dev.moklev.mathproof.model.Free
import dev.moklev.mathproof.model.FunctionSort
import dev.moklev.mathproof.model.Lambda
import dev.moklev.mathproof.model.Sort
import dev.moklev.mathproof.model.SortVariable
import dev.moklev.mathproof.model.betaNormalize
import dev.moklev.mathproof.model.freshFree
import dev.moklev.mathproof.model.matchSort
import dev.moklev.mathproof.model.resolve
import dev.moklev.mathproof.model.abstract

fun StatementCall.resolveFromPremises(premiseClaims: List<Expr>): StatementCall {
    if (!hasAutoArguments()) {
        return this
    }
    require(premiseClaims.size == premises.size) {
        "Cannot infer arguments for statement '${statement.name}': expected ${premises.size} premise claim(s), but got ${premiseClaims.size}."
    }
    return resolveFromMatches(
        matches = premises.zip(premiseClaims),
        sourceDescription = "statement premises",
    )
}

fun StatementCall.resolveFromMatches(
    matches: List<Pair<Expr, Expr>>,
    sourceDescription: String,
): StatementCall {
    if (!hasAutoArguments()) {
        return this
    }

    val matcher = StatementArgumentMatcher(
        statement = statement,
        unresolvedParameterSymbols = unresolvedParameterSymbols(),
        sourceDescription = sourceDescription,
    )
    matcher.prebindExplicitArguments(statement.parameters.zip(arguments))

    matches.forEachIndexed { index, (pattern, actual) ->
        matcher.match(
            pattern = pattern.betaNormalize(),
            actual = actual.betaNormalize(),
            location = "${sourceDescription.trimEnd()} #${index + 1}",
        )
    }
    return matcher.buildCall()
}

private fun StatementCall.hasAutoArguments(): Boolean =
    arguments.any { argument -> argument.isAutoArgument() }

private fun StatementCall.unresolvedParameterSymbols(): Set<String> =
    statement.parameters.zip(arguments)
        .asSequence()
        .filter { (_, argument) -> argument.isAutoArgument() }
        .map { (parameter, _) -> parameter.symbol }
        .toSet()

private class StatementArgumentMatcher(
    private val statement: StatementDefinition,
    unresolvedParameterSymbols: Set<String>,
    private val sourceDescription: String,
) {
    private val parameterBySymbol = statement.parameters.associateBy { parameter -> parameter.symbol }
    private val unresolvedParameterBySymbol = unresolvedParameterSymbols.associateWith { symbol ->
        requireNotNull(parameterBySymbol[symbol]) {
            "Unknown parameter symbol '$symbol' in unresolved argument set."
        }
    }
    private val applicationConstraintsByParameterSymbol = linkedMapOf<String, MutableList<ApplicationConstraint>>()
    private val parameterBindings = linkedMapOf<String, Expr>()
    private val sortBindings = linkedMapOf<SortVariable, Sort>()

    fun prebindExplicitArguments(
        parameterArguments: List<Pair<StatementParameter, Expr>>,
    ) {
        parameterArguments.forEach { (parameter, argument) ->
            if (argument.isAutoArgument()) {
                return@forEach
            }
            bindParameter(
                parameter = parameter,
                actual = argument.betaNormalize(),
                location = "argument '${parameter.name}'",
            )
        }
    }

    fun match(
        pattern: Expr,
        actual: Expr,
        location: String,
    ) {
        when (pattern) {
            is Free -> matchFree(pattern, actual, location)
            is Bound -> matchBound(pattern, actual, location)
            is Lambda -> matchLambda(pattern, actual, location)
            is Apply -> matchApply(pattern, actual, location)
        }
    }

    fun buildCall(): StatementCall {
        synthesizeHigherOrderBindings()

        val unresolvedParameters = statement.parameters.filter { parameter ->
            parameter.symbol !in parameterBindings
        }
        require(unresolvedParameters.isEmpty()) {
            val rendered = unresolvedParameters.joinToString(", ") { parameter ->
                "'${parameter.name}: ${parameter.sort}'"
            }
            "Cannot infer arguments for statement '${statement.name}' from $sourceDescription: unresolved parameter(s): $rendered."
        }

        val arguments = statement.parameters.map { parameter ->
            requireNotNull(parameterBindings[parameter.symbol])
        }
        return statement.instantiate(arguments)
    }

    private fun matchFree(
        pattern: Free,
        actual: Expr,
        location: String,
    ) {
        val unresolvedParameter = unresolvedParameterBySymbol[pattern.symbol]
        if (unresolvedParameter != null) {
            bindParameter(unresolvedParameter, actual, location)
            return
        }

        val actualFree = actual as? Free ?: throw mismatch(
            location = location,
            expected = pattern,
            actual = actual,
        )
        require(pattern.symbol == actualFree.symbol) {
            mismatchMessage(
                location = location,
                expected = pattern,
                actual = actual,
            )
        }
        require(matchSort(pattern.sort, actualFree.sort, sortBindings)) {
            sortMismatchMessage(
                location = location,
                expectedSort = pattern.sort,
                actualSort = actualFree.sort,
                context = "constant '${pattern.displayName}'",
            )
        }
    }

    private fun matchBound(
        pattern: Bound,
        actual: Expr,
        location: String,
    ) {
        val actualBound = actual as? Bound ?: throw mismatch(
            location = location,
            expected = pattern,
            actual = actual,
        )
        require(pattern.index == actualBound.index) {
            mismatchMessage(
                location = location,
                expected = pattern,
                actual = actual,
            )
        }
        require(matchSort(pattern.sort, actualBound.sort, sortBindings)) {
            sortMismatchMessage(
                location = location,
                expectedSort = pattern.sort,
                actualSort = actualBound.sort,
                context = "bound variable '#${pattern.index}'",
            )
        }
    }

    private fun matchLambda(
        pattern: Lambda,
        actual: Expr,
        location: String,
    ) {
        val actualLambda = actual as? Lambda ?: throw mismatch(
            location = location,
            expected = pattern,
            actual = actual,
        )
        require(matchSort(pattern.parameterSort, actualLambda.parameterSort, sortBindings)) {
            sortMismatchMessage(
                location = location,
                expectedSort = pattern.parameterSort,
                actualSort = actualLambda.parameterSort,
                context = "lambda parameter",
            )
        }
        match(
            pattern = pattern.body,
            actual = actualLambda.body,
            location = "$location > lambda body",
        )
    }

    private fun matchApply(
        pattern: Apply,
        actual: Expr,
        location: String,
    ) {
        val unresolvedParameter = (pattern.function as? Free)
            ?.let { function -> unresolvedParameterBySymbol[function.symbol] }

        if (
            unresolvedParameter != null &&
            unresolvedParameter.sort.resolve(sortBindings) is FunctionSort &&
            !pattern.argument.containsUnresolvedParameter(unresolvedParameterBySymbol.keys)
        ) {
            registerApplicationConstraint(
                parameter = unresolvedParameter,
                argumentPattern = pattern.argument,
                actual = actual,
                location = location,
            )
            return
        }

        val actualApply = actual as? Apply ?: throw mismatch(
            location = location,
            expected = pattern,
            actual = actual,
        )
        match(
            pattern = pattern.function,
            actual = actualApply.function,
            location = "$location > function",
        )
        match(
            pattern = pattern.argument,
            actual = actualApply.argument,
            location = "$location > argument",
        )
    }

    private fun bindParameter(
        parameter: StatementParameter,
        actual: Expr,
        location: String,
    ) {
        require(matchSort(parameter.sort, actual.sort, sortBindings)) {
            sortMismatchMessage(
                location = location,
                expectedSort = parameter.sort,
                actualSort = actual.sort,
                context = "parameter '${parameter.name}'",
            )
        }

        val existing = parameterBindings[parameter.symbol]
        if (existing == null) {
            parameterBindings[parameter.symbol] = actual
            return
        }

        require(existing == actual) {
            "Cannot infer arguments for statement '${statement.name}' from $sourceDescription: " +
                "parameter '${parameter.name}' has conflicting matches ('$existing' vs '$actual') at $location."
        }
    }

    private fun registerApplicationConstraint(
        parameter: StatementParameter,
        argumentPattern: Expr,
        actual: Expr,
        location: String,
    ) {
        val functionSort = parameter.sort.resolve(sortBindings) as? FunctionSort
            ?: throw mismatch(
                location = location,
                expected = Apply(
                    function = Free(
                        symbol = parameter.symbol,
                        sort = parameter.sort.resolve(sortBindings),
                        displayName = parameter.name,
                    ),
                    argument = argumentPattern,
                ),
                actual = actual,
            )

        require(matchSort(functionSort.parameterSort, argumentPattern.sort, sortBindings)) {
            sortMismatchMessage(
                location = location,
                expectedSort = functionSort.parameterSort,
                actualSort = argumentPattern.sort,
                context = "argument for parameter '${parameter.name}'",
            )
        }
        require(matchSort(functionSort.resultSort, actual.sort, sortBindings)) {
            sortMismatchMessage(
                location = location,
                expectedSort = functionSort.resultSort,
                actualSort = actual.sort,
                context = "result of parameter '${parameter.name}' application",
            )
        }

        val constraints = applicationConstraintsByParameterSymbol.getOrPut(parameter.symbol) { mutableListOf() }
        constraints += ApplicationConstraint(
            argumentPattern = argumentPattern.betaNormalize(),
            actual = actual.betaNormalize(),
            location = location,
        )
    }

    private fun synthesizeHigherOrderBindings() {
        unresolvedParameterBySymbol.values.forEach { parameter ->
            if (parameter.symbol in parameterBindings) {
                return@forEach
            }
            val constraints = applicationConstraintsByParameterSymbol[parameter.symbol].orEmpty()
            if (constraints.isEmpty()) {
                return@forEach
            }

            val synthesized = synthesizeParameterFromConstraints(parameter, constraints)
            if (synthesized != null) {
                bindParameter(
                    parameter = parameter,
                    actual = synthesized,
                    location = "higher-order reconstruction",
                )
            }
        }
    }

    private fun synthesizeParameterFromConstraints(
        parameter: StatementParameter,
        constraints: List<ApplicationConstraint>,
    ): Expr? {
        val functionSort = parameter.sort.resolve(sortBindings) as? FunctionSort ?: return null
        constraints.forEach { seed ->
            val candidate = synthesizeFromConstraint(
                functionSort = functionSort,
                seed = seed,
            ) ?: return@forEach
            val allConstraintsSatisfied = constraints.all { constraint ->
                val reconstructed = Apply(candidate, constraint.argumentPattern).betaNormalize()
                reconstructed == constraint.actual
            }
            if (allConstraintsSatisfied) {
                return candidate
            }
        }
        return null
    }

    private fun synthesizeFromConstraint(
        functionSort: FunctionSort,
        seed: ApplicationConstraint,
    ): Expr? {
        val placeholder = freshFree(
            displayName = "auto",
            sort = functionSort.parameterSort,
            namespace = "statement-inference",
        )
        val (replaced, changed) = replaceAllOccurrences(
            expr = seed.actual,
            target = seed.argumentPattern,
            replacement = placeholder,
            depth = 0,
        )
        if (!changed) {
            return null
        }
        return Lambda(
            parameterSort = functionSort.parameterSort,
            body = replaced.abstract(placeholder),
        ).apply {
            parameterHint = "auto"
        }.betaNormalize()
    }

    private fun mismatch(
        location: String,
        expected: Expr,
        actual: Expr,
    ): IllegalArgumentException = IllegalArgumentException(
        mismatchMessage(
            location = location,
            expected = expected,
            actual = actual,
        ),
    )

    private fun mismatchMessage(
        location: String,
        expected: Expr,
        actual: Expr,
    ): String =
        "Cannot infer arguments for statement '${statement.name}' from $sourceDescription: " +
            "expression mismatch at $location: expected '$expected', got '$actual'."

    private fun sortMismatchMessage(
        location: String,
        expectedSort: Sort,
        actualSort: Sort,
        context: String,
    ): String =
        "Cannot infer arguments for statement '${statement.name}' from $sourceDescription: " +
            "sort mismatch for $context at $location: expected '$expectedSort', got '$actualSort'."

    private fun replaceAllOccurrences(
        expr: Expr,
        target: Expr,
        replacement: Free,
        depth: Int,
    ): Pair<Expr, Boolean> {
        if (matchesAtDepth(expr = expr, target = target, depth = depth)) {
            return replacement to true
        }
        return when (expr) {
            is Free, is Bound -> expr to false
            is Lambda -> {
                val (body, changed) = replaceAllOccurrences(
                    expr = expr.body,
                    target = target,
                    replacement = replacement,
                    depth = depth + 1,
                )
                if (!changed) {
                    expr to false
                } else {
                    Lambda(expr.parameterSort, body).apply {
                        parameterHint = expr.parameterHint
                    } to true
                }
            }
            is Apply -> {
                val (function, functionChanged) = replaceAllOccurrences(
                    expr = expr.function,
                    target = target,
                    replacement = replacement,
                    depth = depth,
                )
                val (argument, argumentChanged) = replaceAllOccurrences(
                    expr = expr.argument,
                    target = target,
                    replacement = replacement,
                    depth = depth,
                )
                val changed = functionChanged || argumentChanged
                if (!changed) {
                    expr to false
                } else {
                    Apply(function, argument) to true
                }
            }
        }
    }

    private fun matchesAtDepth(
        expr: Expr,
        target: Expr,
        depth: Int,
    ): Boolean = when (target) {
        is Free -> {
            val actual = expr as? Free ?: return false
            target.symbol == actual.symbol && target.sort == actual.sort
        }
        is Bound -> {
            val actual = expr as? Bound ?: return false
            actual.index == target.index + depth && actual.sort == target.sort
        }
        is Lambda -> {
            val actual = expr as? Lambda ?: return false
            actual.parameterSort == target.parameterSort &&
                matchesAtDepth(
                    expr = actual.body,
                    target = target.body,
                    depth = depth + 1,
                )
        }
        is Apply -> {
            val actual = expr as? Apply ?: return false
            matchesAtDepth(
                expr = actual.function,
                target = target.function,
                depth = depth,
            ) &&
                matchesAtDepth(
                    expr = actual.argument,
                    target = target.argument,
                    depth = depth,
                )
        }
    }

    private fun Expr.containsUnresolvedParameter(unresolvedSymbols: Set<String>): Boolean = when (this) {
        is Free -> this.symbol in unresolvedSymbols
        is Bound -> false
        is Lambda -> body.containsUnresolvedParameter(unresolvedSymbols)
        is Apply -> function.containsUnresolvedParameter(unresolvedSymbols) ||
            argument.containsUnresolvedParameter(unresolvedSymbols)
    }

    private data class ApplicationConstraint(
        val argumentPattern: Expr,
        val actual: Expr,
        val location: String,
    )
}
