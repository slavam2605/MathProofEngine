package dev.moklev.mathproof.equality.dsl

import dev.moklev.mathproof.dsl.Occurences
import dev.moklev.mathproof.dsl.ExprPath
import dev.moklev.mathproof.dsl.ExprPathStep
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

private data class OccurrenceInfo(
    val path: ExprPath,
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

    val occurrences = collectOccurrences(sourceClaim, from)
    require(occurrences.isNotEmpty()) {
        "$apiName cannot rewrite '$sourceClaim' using '$equalityClaim': no occurrences of '$from' found."
    }

    val selectedIndices = resolveSelectedIndices(
        at = at,
        occurrences = occurrences,
        apiName = apiName,
        sourceClaim = sourceClaim,
        from = from,
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
    occurrences: List<OccurrenceInfo>,
    apiName: String,
    sourceClaim: Expr,
    from: Expr,
): Set<Int> = when (at) {
    Occurences.All -> occurrences.indices.toSet()
    Occurences.First -> setOf(0)
    Occurences.Last -> setOf(occurrences.lastIndex)
    is Occurences.Only -> {
        val indices = at.zeroBasedIndices
        require(indices.isNotEmpty()) {
            "$apiName with Occurences.Only requires at least one index."
        }
        val negative = indices.firstOrNull { index -> index < 0 }
        require(negative == null) {
            "$apiName received negative occurrence index $negative."
        }
        val outOfRange = indices.firstOrNull { index -> index >= occurrences.size }
        require(outOfRange == null) {
            "$apiName occurrence index $outOfRange is out of bounds: found ${occurrences.size} occurrence(s)."
        }
        indices
    }
    is Occurences.Path -> {
        val nodeAtPath = resolveNodeAtPath(
            root = sourceClaim,
            path = at.path,
            apiName = apiName,
        )
        require(matchesAtDepth(expr = nodeAtPath, target = from, depth = 0)) {
            "$apiName path '${at.path}' points to '$nodeAtPath', which is not an occurrence of '$from' in '$sourceClaim'."
        }
        val occurrenceIndex = occurrences.indexOfFirst { occurrence -> occurrence.path == at.path }
        check(occurrenceIndex >= 0) {
            "$apiName internal error: path '${at.path}' matched '$from' but was not indexed as an occurrence."
        }
        setOf(occurrenceIndex)
    }
}

private fun collectOccurrences(
    expr: Expr,
    target: Expr,
): List<OccurrenceInfo> {
    val occurrences = mutableListOf<OccurrenceInfo>()

    fun walk(
        node: Expr,
        depth: Int,
        path: ExprPath,
    ) {
        if (matchesAtDepth(expr = node, target = target, depth = depth)) {
            occurrences += OccurrenceInfo(path = path)
            return
        }
        when (node) {
            is Free, is Bound -> Unit
            is Lambda -> walk(
                node = node.body,
                depth = depth + 1,
                path = path / ExprPathStep.Body,
            )
            is Apply -> {
                walk(
                    node = node.function,
                    depth = depth,
                    path = path / ExprPathStep.Function,
                )
                walk(
                    node = node.argument,
                    depth = depth,
                    path = path / ExprPathStep.Argument,
                )
            }
        }
    }

    walk(expr, depth = 0, path = ExprPath.Root)
    return occurrences
}

private fun resolveNodeAtPath(
    root: Expr,
    path: ExprPath,
    apiName: String,
): Expr {
    var current: Expr = root
    path.steps.forEachIndexed { index, step ->
        current = when (step) {
            ExprPathStep.Function -> {
                val apply = current as? Apply
                    ?: throw IllegalArgumentException(
                        "$apiName cannot follow path '$path' at step ${index + 1} (Function): expected Apply, got '$current'.",
                    )
                apply.function
            }
            ExprPathStep.Argument -> {
                val apply = current as? Apply
                    ?: throw IllegalArgumentException(
                        "$apiName cannot follow path '$path' at step ${index + 1} (Argument): expected Apply, got '$current'.",
                    )
                apply.argument
            }
            ExprPathStep.Body -> {
                val lambda = current as? Lambda
                    ?: throw IllegalArgumentException(
                        "$apiName cannot follow path '$path' at step ${index + 1} (Body): expected Lambda, got '$current'.",
                    )
                lambda.body
            }
            ExprPathStep.BinLeft -> {
                val apply = current as? Apply
                    ?: throw IllegalArgumentException(
                        "$apiName cannot follow path '$path' at step ${index + 1} (BinLeft): expected Apply, got '$current'.",
                    )
                val leftBranch = apply.function as? Apply
                    ?: throw IllegalArgumentException(
                        "$apiName cannot follow path '$path' at step ${index + 1} (BinLeft): expected Apply.function to be Apply, got '${apply.function}'.",
                    )
                leftBranch.argument
            }
            ExprPathStep.BinRight -> {
                val apply = current as? Apply
                    ?: throw IllegalArgumentException(
                        "$apiName cannot follow path '$path' at step ${index + 1} (BinRight): expected Apply, got '$current'.",
                    )
                apply.argument
            }
        }
    }
    return current
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
        actual.index == target.index && actual.sort == target.sort
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
