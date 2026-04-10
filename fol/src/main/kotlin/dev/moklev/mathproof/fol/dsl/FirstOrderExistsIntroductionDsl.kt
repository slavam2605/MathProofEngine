package dev.moklev.mathproof.fol.dsl

import dev.moklev.mathproof.dsl.Occurences
import dev.moklev.mathproof.fol.FirstOrderAxioms
import dev.moklev.mathproof.kernel.Fact
import dev.moklev.mathproof.kernel.ProofBuilder
import dev.moklev.mathproof.logic.AssumptionScope
import dev.moklev.mathproof.logic.ScopedFact
import dev.moklev.mathproof.logic.applyByMpChain
import dev.moklev.mathproof.model.Apply
import dev.moklev.mathproof.model.Bound
import dev.moklev.mathproof.model.Expr
import dev.moklev.mathproof.model.Free
import dev.moklev.mathproof.model.Lambda
import dev.moklev.mathproof.model.Sort
import dev.moklev.mathproof.model.abstract
import dev.moklev.mathproof.model.freshFree

context(proofBuilder: ProofBuilder)
fun Fact.introduceExists(
    witness: Expr,
    at: Occurences = Occurences.All,
    variableName: String = "x",
): Fact {
    val introduction = buildExistsIntroductionPlan(
        sourceClaim = claim,
        witness = witness,
        variableName = variableName,
        explicitSort = null,
        at = at,
        apiName = "Fact.introduceExists",
    )
    return proofBuilder.applyByMpChain(
        FirstOrderAxioms.existsIntroduction(introduction.predicate, witness),
        this,
    )
}

context(proofBuilder: ProofBuilder)
fun Fact.introduceExists(
    witness: Expr,
    at: Occurences = Occurences.All,
    variableName: String,
    sort: Sort,
): Fact {
    val introduction = buildExistsIntroductionPlan(
        sourceClaim = claim,
        witness = witness,
        variableName = variableName,
        explicitSort = sort,
        at = at,
        apiName = "Fact.introduceExists",
    )
    return proofBuilder.applyByMpChain(
        FirstOrderAxioms.existsIntroduction(introduction.predicate, witness),
        this,
    )
}

context(scope: AssumptionScope)
fun ScopedFact.introduceExists(
    witness: Expr,
    at: Occurences = Occurences.All,
    variableName: String = "x",
): ScopedFact {
    val introduction = buildExistsIntroductionPlan(
        sourceClaim = claim,
        witness = witness,
        variableName = variableName,
        explicitSort = null,
        at = at,
        apiName = "ScopedFact.introduceExists",
    )
    return scope.applyByMpChain(
        FirstOrderAxioms.existsIntroduction(introduction.predicate, witness),
        this,
    )
}

context(scope: AssumptionScope)
fun ScopedFact.introduceExists(
    witness: Expr,
    at: Occurences = Occurences.All,
    variableName: String,
    sort: Sort,
): ScopedFact {
    val introduction = buildExistsIntroductionPlan(
        sourceClaim = claim,
        witness = witness,
        variableName = variableName,
        explicitSort = sort,
        at = at,
        apiName = "ScopedFact.introduceExists",
    )
    return scope.applyByMpChain(
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
        totalOccurrences = occurrences.size,
        apiName = apiName,
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
)

private fun findOccurrencesWithSorts(
    expr: Expr,
    target: Expr,
): List<OccurrenceInfo> {
    val occurrences = mutableListOf<OccurrenceInfo>()

    fun walk(node: Expr, depth: Int) {
        if (matchesAtDepth(expr = node, target = target, depth = depth)) {
            occurrences += OccurrenceInfo(sort = node.sort)
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
    return occurrences
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
