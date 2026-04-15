package dev.moklev.mathproof.core

import dev.moklev.mathproof.kernel.StatementBuilder
import dev.moklev.mathproof.kernel.StatementDefinition

fun statement(name: String, block: StatementBuilder.() -> Unit): StatementDefinition =
    registry.registerStatement(name, block)

fun axiom(
    name: String,
    note: String? = null,
    block: StatementBuilder.() -> Unit,
): StatementDefinition = registry.registerStatement(name) {
    block()
    assumed(note)
}
