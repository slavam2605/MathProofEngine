package dev.moklev.mathproof.kernel

import dev.moklev.mathproof.model.Expr
import dev.moklev.mathproof.model.Sort

data class ProofScript(
    val steps: List<ProofStep>,
    val arbitraryVariables: List<ArbitraryVariable> = emptyList(),
)

data class ArbitraryVariable(
    val symbol: String,
    val displayName: String,
    val sort: Sort,
)

data class ProofStep(
    val label: String,
    val claim: Expr,
    val justification: Justification,
)
