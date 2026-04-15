package dev.moklev.mathproof.fol.dsl

import dev.moklev.mathproof.dsl.Occurences
import dev.moklev.mathproof.dsl.ExprPath
import dev.moklev.mathproof.dsl.ExprPathStep
import dev.moklev.mathproof.fol.FirstOrderAxioms
import dev.moklev.mathproof.kernel.DerivationFact
import dev.moklev.mathproof.kernel.DerivationScope
import dev.moklev.mathproof.logic.applyMp
import dev.moklev.mathproof.model.Apply
import dev.moklev.mathproof.model.Bound
import dev.moklev.mathproof.model.Expr
import dev.moklev.mathproof.model.Free
import dev.moklev.mathproof.model.Lambda
import dev.moklev.mathproof.model.Sort
import dev.moklev.mathproof.model.abstract
import dev.moklev.mathproof.model.freshFree

context(scope: DerivationScope)
fun DerivationFact.introduceExists(
    witness: Expr,
    at: Occurences = Occurences.All,
    variableName: String = "x",
): DerivationFact {
    val introduction = buildExistsIntroductionPlan(
        sourceClaim = claim,
        witness = witness,
        variableName = variableName,
        explicitSort = null,
        at = at,
        apiName = "DerivationFact.introduceExists",
    )
    return scope.applyMp(
        FirstOrderAxioms.existsIntroduction(introduction.predicate, witness),
        this,
    )
}

context(scope: DerivationScope)
fun DerivationFact.introduceExists(
    witness: Expr,
    at: Occurences = Occurences.All,
    variableName: String,
    sort: Sort,
): DerivationFact {
    val introduction = buildExistsIntroductionPlan(
        sourceClaim = claim,
        witness = witness,
        variableName = variableName,
        explicitSort = sort,
        at = at,
        apiName = "DerivationFact.introduceExists",
    )
    return scope.applyMp(
        FirstOrderAxioms.existsIntroduction(introduction.predicate, witness),
        this,
    )
}

private data class ExistsIntroductionPlan(
    val predicate: Expr,
)

private fun buildExistsIntroductionPlan(
    sourceClaim: Expr,
    witness: Expr,
    variableName: String,
    explicitSort: Sort?,
    at: Occurences,
    apiName: String,
): ExistsIntroductionPlan {
    require(variableName.isNotBlank()) {
        "$apiName requires a non-blank variableName."
    }

    val occurrences = findOccurrencesWithSorts(sourceClaim, witness)
    require(occurrences.isNotEmpty()) {
        "$apiName cannot abstract witness '$witness' in '$sourceClaim': no matching occurrences found."
    }

    val selectedIndices = resolveSelectedIndices(
        at = at,
        occurrences = occurrences,
        apiName = apiName,
        sourceClaim = sourceClaim,
        witness = witness,
    )
    val selectedSorts = selectedIndices.map { index -> occurrences[index].sort }.toSet()
    require(selectedSorts.size == 1) {
        "$apiName expected selected witness occurrences to have one sort, but got $selectedSorts."
    }
    val deducedSort = selectedSorts.single()
    val binderSort = if (explicitSort == null) {
        deducedSort
    } else {
        require(explicitSort == deducedSort) {
            "$apiName received sort '$explicitSort', but selected witness occurrences have sort '$deducedSort'."
        }
        explicitSort
    }

    val placeholder = freshFree(
        displayName = variableName,
        sort = binderSort,
        namespace = "fol-exists-introduction",
    )
    val rewrittenClaim = replaceOccurrencesByIndex(
        expr = sourceClaim,
        target = witness,
        replacement = placeholder,
        selectedIndices = selectedIndices,
    )
    val predicate = Lambda(
        parameterSort = binderSort,
        body = rewrittenClaim.abstract(placeholder),
    ).apply {
        parameterHint = variableName
    }

    return ExistsIntroductionPlan(
        predicate = predicate,
    )
}

private data class OccurrenceInfo(
    val sort: Sort,
    val path: ExprPath,
)

private fun findOccurrencesWithSorts(
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
            occurrences += OccurrenceInfo(
                sort = node.sort,
                path = path,
            )
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

private fun resolveSelectedIndices(
    at: Occurences,
    occurrences: List<OccurrenceInfo>,
    apiName: String,
    sourceClaim: Expr,
    witness: Expr,
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
        require(matchesAtDepth(expr = nodeAtPath, target = witness, depth = 0)) {
            "$apiName path '${at.path}' points to '$nodeAtPath', which is not an occurrence of '$witness' in '$sourceClaim'."
        }
        val occurrenceIndex = occurrences.indexOfFirst { occurrence -> occurrence.path == at.path }
        check(occurrenceIndex >= 0) {
            "$apiName internal error: path '${at.path}' matched '$witness' but was not indexed as an occurrence."
        }
        setOf(occurrenceIndex)
    }
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
