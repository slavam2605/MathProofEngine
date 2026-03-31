package dev.moklev.mathproof.kernel

import dev.moklev.mathproof.model.Expr

data class ProofScript(val steps: List<ProofStep>)

data class ProofStep(
    val label: String,
    val claim: Expr,
    val justification: Justification,
)
