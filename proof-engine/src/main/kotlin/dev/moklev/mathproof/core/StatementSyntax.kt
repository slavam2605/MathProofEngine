package dev.moklev.mathproof.core

import dev.moklev.mathproof.kernel.StatementBuilder
import dev.moklev.mathproof.kernel.StatementDefinition

fun statement(name: String, block: StatementBuilder.() -> Unit): StatementDefinition =
    StatementBuilder(name).apply(block).build()

fun axiom(
    name: String,
    note: String? = null,
    block: StatementBuilder.() -> Unit,
): StatementDefinition = StatementBuilder(name).apply {
    block()
    assumed(note)
}.build()
