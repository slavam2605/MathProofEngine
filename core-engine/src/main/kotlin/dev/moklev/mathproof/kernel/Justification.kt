package dev.moklev.mathproof.kernel

import dev.moklev.mathproof.model.Expr
import dev.moklev.mathproof.model.Free

sealed interface Justification

data class PremiseReference(val premiseIndex: Int) : Justification

data class StatementApplication(
    val statement: StatementDefinition,
    val arguments: List<Expr>,
    val premiseLabels: List<String>,
) : Justification

data class UniversalGeneralization(
    val sourceLabel: String,
    val quantifier: Expr,
    val variable: Free,
) : Justification
