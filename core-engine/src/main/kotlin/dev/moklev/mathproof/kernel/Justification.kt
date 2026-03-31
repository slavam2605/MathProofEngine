package dev.moklev.mathproof.kernel

import dev.moklev.mathproof.model.Expr

sealed interface Justification

data class PremiseReference(val premiseIndex: Int) : Justification

data class StatementApplication(
    val statement: StatementDefinition,
    val arguments: List<Expr>,
    val premiseLabels: List<String>,
) : Justification
