package dev.moklev.mathproof.model

/**
 * Fully beta-normalizes this expression.
 *
 * The normalization uses capture-avoiding beta-contraction on de Bruijn bound variables.
 */
fun Expr.betaNormalize(): Expr = betaNormalizeRecursive(this)

private fun betaNormalizeRecursive(expr: Expr): Expr = when (expr) {
    is Free, is Bound -> expr
    is Lambda -> {
        val normalizedBody = betaNormalizeRecursive(expr.body)
        if (normalizedBody == expr.body) expr else expr.copy(body = normalizedBody)
    }
    is Apply -> {
        val normalizedFunction = betaNormalizeRecursive(expr.function)
        if (normalizedFunction is Lambda) {
            betaNormalizeRecursive(betaContract(normalizedFunction, expr.argument))
        } else {
            val normalizedArgument = betaNormalizeRecursive(expr.argument)
            if (normalizedFunction == expr.function && normalizedArgument == expr.argument) {
                expr
            } else {
                Apply(normalizedFunction, normalizedArgument)
            }
        }
    }
}

private fun betaContract(
    lambda: Lambda,
    argument: Expr,
): Expr {
    val liftedArgument = argument.shiftBoundIndices(delta = 1)
    val substitutedBody = lambda.body.substituteBound(index = 0, replacement = liftedArgument)
    return substitutedBody.shiftBoundIndices(delta = -1)
}

private fun Expr.substituteBound(
    index: Int,
    replacement: Expr,
    depth: Int = 0,
): Expr = when (this) {
    is Free -> this
    is Bound -> {
        if (this.index == index + depth) {
            replacement.shiftBoundIndices(delta = depth)
        } else {
            this
        }
    }
    is Lambda -> {
        val substitutedBody = body.substituteBound(index = index, replacement = replacement, depth = depth + 1)
        if (substitutedBody == body) this else copy(body = substitutedBody)
    }
    is Apply -> {
        val substitutedFunction = function.substituteBound(index = index, replacement = replacement, depth = depth)
        val substitutedArgument = argument.substituteBound(index = index, replacement = replacement, depth = depth)
        if (substitutedFunction == function && substitutedArgument == argument) {
            this
        } else {
            Apply(substitutedFunction, substitutedArgument)
        }
    }
}

private fun Expr.shiftBoundIndices(
    delta: Int,
    cutoff: Int = 0,
): Expr = when (this) {
    is Free -> this
    is Bound -> {
        if (index < cutoff) {
            this
        } else {
            val shiftedIndex = index + delta
            require(shiftedIndex >= 0) {
                "Invalid bound-variable shift: index=$index, delta=$delta, cutoff=$cutoff"
            }
            if (shiftedIndex == index) this else copy(index = shiftedIndex)
        }
    }
    is Lambda -> {
        val shiftedBody = body.shiftBoundIndices(delta = delta, cutoff = cutoff + 1)
        if (shiftedBody == body) this else copy(body = shiftedBody)
    }
    is Apply -> {
        val shiftedFunction = function.shiftBoundIndices(delta = delta, cutoff = cutoff)
        val shiftedArgument = argument.shiftBoundIndices(delta = delta, cutoff = cutoff)
        if (shiftedFunction == function && shiftedArgument == argument) {
            this
        } else {
            Apply(shiftedFunction, shiftedArgument)
        }
    }
}
