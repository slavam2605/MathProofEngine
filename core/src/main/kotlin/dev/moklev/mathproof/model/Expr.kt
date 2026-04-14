package dev.moklev.mathproof.model

sealed interface Expr {
    val sort: Sort

    operator fun invoke(argument: Expr): Expr = Apply(this, argument)

    operator fun invoke(vararg arguments: Expr): Expr = arguments.fold(this) { function, argument ->
        Apply(function, argument)
    }
}

data class Free(
    val symbol: String,
    override val sort: Sort,
    val displayName: String = symbol,
) : Expr {
    override fun toString(): String = render()
}

data class Bound(
    val index: Int,
    override val sort: Sort,
) : Expr {
    init {
        require(index >= 0) { "Bound variable indices must be non-negative." }
    }

    override fun toString(): String = render()
}

data class Lambda(
    val parameterSort: Sort,
    val body: Expr
) : Expr {
    var parameterHint: String? = null
    override val sort: Sort = FunctionSort(parameterSort, body.sort)

    override fun toString(): String = render()
}

data class Apply(
    val function: Expr,
    val argument: Expr,
) : Expr {
    override val sort: Sort = inferApplicationResultSort(function.sort, argument.sort)

    override fun toString(): String = render()
}

fun Expr.substitute(bindings: Map<String, Expr>): Expr = when (this) {
    is Free -> bindings[symbol] ?: this
    is Bound -> this
    is Lambda -> copy(body = body.substitute(bindings))
    is Apply -> Apply(
        function = function.substitute(bindings),
        argument = argument.substitute(bindings),
    )
}

fun Expr.resolveSorts(bindings: SortBindings): Expr = when (this) {
    is Free -> this
    is Bound -> {
        val resolvedSort = sort.resolve(bindings)
        if (resolvedSort == sort) this else copy(sort = resolvedSort)
    }
    is Lambda -> {
        val resolvedParameterSort = parameterSort.resolve(bindings)
        val resolvedBody = body.resolveSorts(bindings)
        if (resolvedParameterSort == parameterSort && resolvedBody == body) {
            this
        } else {
            Lambda(resolvedParameterSort, resolvedBody).apply {
                parameterHint = this@resolveSorts.parameterHint
            }
        }
    }
    is Apply -> {
        val resolvedFunction = function.resolveSorts(bindings)
        val resolvedArgument = argument.resolveSorts(bindings)
        if (resolvedFunction == function && resolvedArgument == argument) {
            this
        } else {
            Apply(resolvedFunction, resolvedArgument)
        }
    }
}

fun freshFree(
    displayName: String,
    sort: Sort,
    namespace: String = "free",
): Free = Free(
    symbol = FreshFreeIds.next(namespace, displayName),
    sort = sort,
    displayName = displayName,
)

fun Expr.abstract(target: Free, depth: Int = 0): Expr = when (this) {
    is Free -> if (symbol == target.symbol) Bound(depth, sort) else this
    is Bound -> this
    is Lambda -> copy(body = body.abstract(target, depth + 1))
    is Apply -> Apply(
        function = function.abstract(target, depth),
        argument = argument.abstract(target, depth),
    )
}

private fun Expr.freeDisplayNames(): Set<String> = when (this) {
    is Free -> setOf(displayName)
    is Bound -> emptySet()
    is Lambda -> body.freeDisplayNames()
    is Apply -> function.freeDisplayNames() + argument.freeDisplayNames()
}

private fun inferApplicationResultSort(
    functionSort: Sort,
    argumentSort: Sort,
): Sort {
    val resolvedFunctionSort = functionSort.resolve(emptyMap())
    val unaryFunctionSort = resolvedFunctionSort as? FunctionSort
        ?: throw IllegalArgumentException(
            "Cannot apply an expression of non-function sort '$resolvedFunctionSort'.",
        )
    val sortBindings = linkedMapOf<SortVariable, Sort>()
    if (!matchSort(unaryFunctionSort.parameterSort, argumentSort, sortBindings)) {
        throw IllegalArgumentException(
            "Cannot apply a function expecting sort '${unaryFunctionSort.parameterSort}' to argument sort '$argumentSort'.",
        )
    }

    return unaryFunctionSort.resultSort.resolve(sortBindings)
}

private fun Expr.render(parentPrecedence: Int = 0): String =
    renderWithContext(parentPrecedence, emptyList())

private fun Expr.renderWithContext(
    parentPrecedence: Int,
    boundNames: List<String>,
): String = when (this) {
    is Free -> displayName
    is Bound -> boundNames.getOrNull(boundNames.lastIndex - index) ?: "#$index"
    is Lambda -> renderLambda(parentPrecedence, boundNames)
    is Apply -> renderApplication(parentPrecedence, boundNames)
}

private fun Lambda.renderLambda(
    parentPrecedence: Int,
    boundNames: List<String>,
): String {
    val currentPrecedence = ExprPrecedence.LAMBDA
    val parameterName = freshRenderedName(parameterHint ?: "x", boundNames + body.freeDisplayNames())
    val rendered = "\\$parameterName. ${body.renderWithContext(currentPrecedence, boundNames + parameterName)}"
    return if (currentPrecedence < parentPrecedence) "($rendered)" else rendered
}

private fun Apply.renderApplication(
    parentPrecedence: Int,
    boundNames: List<String>,
): String {
    val (head, arguments) = flattenApplication()

    ExprNotationRegistry.notationFor(head, arguments)?.let { notation ->
        return when (notation) {
            is ExprNotation.Infix -> renderWithInfixNotation(
                head = head,
                arguments = arguments,
                notation = notation,
                parentPrecedence = parentPrecedence,
                boundNames = boundNames,
            )
            is ExprNotation.Prefix -> renderWithPrefixNotation(
                arguments = arguments,
                notation = notation,
                parentPrecedence = parentPrecedence,
                boundNames = boundNames,
            )
            is ExprNotation.Binder -> renderWithBinderNotation(
                arguments = arguments,
                notation = notation,
                parentPrecedence = parentPrecedence,
                boundNames = boundNames,
            )
        }
    }

    val currentPrecedence = ExprPrecedence.APPLICATION
    val renderedHead = when (head) {
        is Free, is Bound -> head.renderWithContext(currentPrecedence, boundNames)
        else -> "(${head.renderWithContext(0, boundNames)})"
    }
    val rendered = "$renderedHead(${arguments.joinToString(", ") { it.renderWithContext(0, boundNames) }})"
    return if (currentPrecedence < parentPrecedence) "($rendered)" else rendered
}

private fun renderWithInfixNotation(
    head: Expr,
    arguments: List<Expr>,
    notation: ExprNotation.Infix,
    parentPrecedence: Int,
    boundNames: List<String>,
): String {
    if (arguments.size != 2) {
        return renderAsFunctionCall(head, arguments, parentPrecedence, boundNames)
    }

    val leftPrecedence = when (notation.associativity) {
        Associativity.RIGHT -> notation.precedence + 1
        Associativity.LEFT -> notation.precedence
    }
    val left = renderInfixOperand(
        expression = arguments[0],
        parentPrecedence = leftPrecedence,
        boundNames = boundNames,
        forceWrapBinderLike = true,
    )
    val rightPrecedence = when (notation.associativity) {
        Associativity.RIGHT -> notation.precedence - 1
        Associativity.LEFT -> notation.precedence + 1
    }
    val right = renderInfixOperand(
        expression = arguments[1],
        parentPrecedence = rightPrecedence,
        boundNames = boundNames,
        forceWrapBinderLike = notation.associativity != Associativity.RIGHT,
    )
    val rendered = if (notation.surroundWithSpaces) {
        "$left ${notation.symbol} $right"
    } else {
        "$left${notation.symbol}$right"
    }
    return if (notation.precedence < parentPrecedence) "($rendered)" else rendered
}

private fun renderWithPrefixNotation(
    arguments: List<Expr>,
    notation: ExprNotation.Prefix,
    parentPrecedence: Int,
    boundNames: List<String>,
): String {
    if (arguments.size != 1) {
        val fallback = "${notation.symbol}(${arguments.joinToString(", ") { it.renderWithContext(0, boundNames) }})"
        return if (notation.precedence < parentPrecedence) "($fallback)" else fallback
    }

    val rendered = "${notation.symbol}${arguments.single().renderWithContext(notation.precedence, boundNames)}"
    return if (notation.precedence < parentPrecedence) "($rendered)" else rendered
}

private fun renderWithBinderNotation(
    arguments: List<Expr>,
    notation: ExprNotation.Binder,
    parentPrecedence: Int,
    boundNames: List<String>,
): String {
    val lambda = arguments.singleOrNull() as? Lambda
    if (lambda == null) {
        val fallback = "${notation.symbol}(${arguments.joinToString(", ") { it.renderWithContext(0, boundNames) }})"
        return if (notation.precedence < parentPrecedence) "($fallback)" else fallback
    }

    val parameterName = freshRenderedName(
        preferred = lambda.parameterHint ?: "x",
        boundNames = boundNames + lambda.body.freeDisplayNames(),
    )
    val renderedBody = lambda.body.renderWithContext(notation.precedence, boundNames + parameterName)
    val rendered = "${notation.symbol}$parameterName. $renderedBody"
    return if (notation.precedence < parentPrecedence) "($rendered)" else rendered
}

private fun renderInfixOperand(
    expression: Expr,
    parentPrecedence: Int,
    boundNames: List<String>,
    forceWrapBinderLike: Boolean,
): String {
    val rendered = expression.renderWithContext(parentPrecedence, boundNames)
    return if (forceWrapBinderLike && expression.isBinderLikeOrPrefixedBinderExpr()) {
        rendered.ensureWrappedInParentheses()
    } else {
        rendered
    }
}

private fun renderAsFunctionCall(
    head: Expr,
    arguments: List<Expr>,
    parentPrecedence: Int,
    boundNames: List<String>,
): String {
    val currentPrecedence = ExprPrecedence.APPLICATION
    val renderedHead = when (head) {
        is Free, is Bound -> head.renderWithContext(currentPrecedence, boundNames)
        else -> "(${head.renderWithContext(0, boundNames)})"
    }
    val rendered = "$renderedHead(${arguments.joinToString(", ") { it.renderWithContext(0, boundNames) }})"
    return if (currentPrecedence < parentPrecedence) "($rendered)" else rendered
}

private fun Expr.flattenApplication(): Pair<Expr, List<Expr>> {
    val arguments = mutableListOf<Expr>()
    var current: Expr = this
    while (current is Apply) {
        arguments += current.argument
        current = current.function
    }
    arguments.reverse()
    return current to arguments
}

private fun Expr.isBinderLikeOrPrefixedBinderExpr(): Boolean = when (this) {
    is Lambda -> true
    is Apply -> {
        val (head, arguments) = flattenApplication()
        when (ExprNotationRegistry.notationFor(head, arguments)) {
            is ExprNotation.Binder -> true
            is ExprNotation.Prefix -> arguments.singleOrNull()?.isBinderLikeOrPrefixedBinderExpr() == true
            else -> false
        }
    }
    else -> false
}

private fun String.ensureWrappedInParentheses(): String {
    if (startsWith("(") && endsWith(")")) return this
    return "($this)"
}

private fun freshRenderedName(
    preferred: String,
    boundNames: List<String>,
): String {
    if (preferred !in boundNames) {
        return preferred
    }

    var suffix = 1
    while (true) {
        val candidate = "$preferred$suffix"
        if (candidate !in boundNames) {
            return candidate
        }
        suffix += 1
    }
}

private object FreshFreeIds {
    private var nextId = 0

    fun next(
        namespace: String,
        displayName: String,
    ): String {
        nextId += 1
        return "#$namespace:$nextId:$displayName"
    }
}
