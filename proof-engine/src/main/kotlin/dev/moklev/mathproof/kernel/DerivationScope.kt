package dev.moklev.mathproof.kernel

import dev.moklev.mathproof.model.Expr
import dev.moklev.mathproof.model.Free
import dev.moklev.mathproof.model.Sort

/**
 * A lightweight fact handle produced inside a derivation scope.
 */
interface DerivationFact {
    val claim: Expr
}

/**
 * Shared proof-scripting surface for root and nested derivation contexts.
 *
 * Domain modules can layer additional scope capabilities (for example assumptions/contradiction)
 * via extension functions or module-local sub-interfaces.
 */
interface DerivationScope {
    /**
     * Imports [fact] into this derivation scope.
     *
     * Implementations may reject facts that are incompatible with the target scope
     * (for example a foreign proof context).
     */
    fun given(fact: DerivationFact): DerivationFact

    fun given(premise: StatementPremise): DerivationFact

    fun infer(statement: StatementCall, premises: List<DerivationFact>): DerivationFact

    fun infer(statement: StatementCall, vararg premises: DerivationFact): DerivationFact =
        infer(statement, premises.toList())

    fun infer(statement: StatementDefinition, premises: List<DerivationFact>): DerivationFact =
        infer(statement.autoCall(), premises)

    fun infer(statement: StatementDefinition, vararg premises: DerivationFact): DerivationFact =
        infer(statement, premises.toList())

    fun justify(claim: Expr, justification: Justification, premises: List<DerivationFact>): DerivationFact

    fun justify(claim: Expr, justification: Justification, vararg premises: DerivationFact): DerivationFact =
        justify(claim, justification, premises.toList())

    fun todoAssume(claim: Expr, note: String? = null): DerivationFact

    fun arbitrary(name: String, sort: Sort): Free

    fun withLastFactFrom(blockDescription: String, block: DerivationScope.() -> Unit): DerivationFact

    /**
     * Optional stable label for [fact]. Root scopes usually expose labels, nested scopes often do not.
     */
    fun factLabel(fact: DerivationFact): String? = null
}
