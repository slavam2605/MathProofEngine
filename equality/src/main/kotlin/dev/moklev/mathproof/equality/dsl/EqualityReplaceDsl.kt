package dev.moklev.mathproof.equality.dsl

import dev.moklev.mathproof.dsl.Occurences
import dev.moklev.mathproof.equality.EqualityAxioms
import dev.moklev.mathproof.equality.EqualityFunctions
import dev.moklev.mathproof.kernel.DerivationFact
import dev.moklev.mathproof.kernel.DerivationScope
import dev.moklev.mathproof.logic.applyMp
import dev.moklev.mathproof.model.Apply
import dev.moklev.mathproof.model.Bound
import dev.moklev.mathproof.model.Expr
import dev.moklev.mathproof.model.Free
import dev.moklev.mathproof.model.Lambda
import dev.moklev.mathproof.model.abstract
import dev.moklev.mathproof.model.freshFree

context(scope: DerivationScope)
fun DerivationFact.replace(
    using: DerivationFact,
    at: Occurences = Occurences.All,
): DerivationFact {
    val rewrite = buildRewritePlan(
        sourceClaim = claim,
        equalityClaim = using.claim,
        at = at,
        apiName = "replace",
    )
    return scope.applyMp(
        EqualityAxioms.substitution(rewrite.predicate, rewrite.from, rewrite.to),
        using,
        this,
    )
}

private data class RewritePlan(
    val from: Expr,
    val to: Expr,
    val predicate: Expr,
)

private data class EqualitySides(
    val left: Expr,
    val right: Expr,
)

private fun buildRewritePlan(
    sourceClaim: Expr,
    equalityClaim: Expr,
    at: Occurences,
    apiName: String,
): RewritePlan {
    val equality = equalityClaim.requireEqualitySides(apiName)
    val from = equality.left
    val to = equality.right

    val totalOccurrences = countOccurrences(sourceClaim, from)
    require(totalOccurrences > 0) {
        "$apiName cannot rewrite '$sourceClaim' using '$equalityClaim': no occurrences of '$from' found."
    }

    val selectedIndices = resolveSelectedIndices(
        at = at,
        totalOccurrences = totalOccurrences,
        apiName = apiName,
    )
    val placeholder = freshFree(
        displayName = "replace",
        sort = from.sort,
        namespace = "equality-replace",
    )
    val rewrittenClaim = replaceOccurrencesByIndex(
        expr = sourceClaim,
        target = from,
        replacement = placeholder,
        selectedIndices = selectedIndices,
    )
    val predicate = Lambda(
        parameterSort = from.sort,
        body = rewrittenClaim.abstract(placeholder),
    ).apply {
        parameterHint = placeholder.displayName
    }

    return RewritePlan(
        from = from,
        to = to,
        predicate = predicate,
    )
}

private fun resolveSelectedIndices(
    at: Occurences,
    totalOccurrences: Int,
    apiName: String,
): Set<Int> = when (at) {
    Occurences.All -> (0 until totalOccurrences).toSet()
    Occurences.First -> setOf(0)
    Occurences.Last -> setOf(totalOccurrences - 1)
    is Occurences.Only -> {
        val indices = at.zeroBasedIndices
        require(indices.isNotEmpty()) {
            "$apiName with Occurences.Only requires at least one index."
        }
        val negative = indices.firstOrNull { index -> index < 0 }
        require(negative == null) {
            "$apiName received negative occurrence index $negative."
        }
        val outOfRange = indices.firstOrNull { index -> index >= totalOccurrences }
        require(outOfRange == null) {
            "$apiName occurrence index $outOfRange is out of bounds: found $totalOccurrences occurrence(s)."
        }
        indices
    }
}

private fun countOccurrences(expr: Expr, target: Expr): Int {
    var count = 0

    fun walk(node: Expr, depth: Int) {
        if (matchesAtDepth(expr = node, target = target, depth = depth)) {
            count += 1
            return
        }
        when (node) {
            is Free, is Bound -> Unit
            is Lambda -> walk(node.body, depth + 1)
            is Apply -> {
                walk(node.function, depth)
                walk(node.argument, depth)
            }
        }
    }

    walk(expr, depth = 0)
    return count
}

private fun replaceOccurrencesByIndex(
    expr: Expr,
    target: Expr,
    replacement: Free,
    selectedIndices: Set<Int>,
): Expr {
    var currentIndex = 0

    fun walk(node: Expr, depth: Int): Expr {
        if (matchesAtDepth(expr = node, target = target, depth = depth)) {
            val matchIndex = currentIndex
            currentIndex += 1
            return if (matchIndex in selectedIndices) replacement else node
        }
        return when (node) {
            is Free, is Bound -> node
            is Lambda -> {
                val replacedBody = walk(node.body, depth + 1)
                if (replacedBody == node.body) {
                    node
                } else {
                    Lambda(node.parameterSort, replacedBody).apply {
                        parameterHint = node.parameterHint
                    }
                }
            }
            is Apply -> {
                val replacedFunction = walk(node.function, depth)
                val replacedArgument = walk(node.argument, depth)
                if (replacedFunction == node.function && replacedArgument == node.argument) {
                    node
                } else {
                    Apply(replacedFunction, replacedArgument)
                }
            }
        }
    }

    return walk(expr, depth = 0)
}

private fun Expr.requireEqualitySides(apiName: String): EqualitySides {
    val eqRight = this as? Apply
        ?: throw IllegalArgumentException(
            "$apiName expects 'using' to be an equality fact, but got '$this'.",
        )
    val eqLeft = eqRight.function as? Apply
        ?: throw IllegalArgumentException(
            "$apiName expects 'using' to be an equality fact, but got '$this'.",
        )
    require(eqLeft.function == EqualityFunctions.Eq) {
        "$apiName expects 'using' to be an equality fact, but got '$this'."
    }
    return EqualitySides(
        left = eqLeft.argument,
        right = eqRight.argument,
    )
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
