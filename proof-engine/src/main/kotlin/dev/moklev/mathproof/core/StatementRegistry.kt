package dev.moklev.mathproof.core

import dev.moklev.mathproof.kernel.StatementBuilder
import dev.moklev.mathproof.kernel.StatementDefinition

class StatementRegistry {
    private val statementsByName = linkedMapOf<String, StatementDefinition>()

    @Synchronized
    fun register(statement: StatementDefinition): StatementDefinition {
        val existing = statementsByName[statement.name]
        require(existing == null) {
            "Statement '${statement.name}' is already registered. Name collisions are forbidden."
        }
        statementsByName[statement.name] = statement
        return statement
    }

    @Synchronized
    fun registerStatement(
        name: String,
        block: StatementBuilder.() -> Unit,
    ): StatementDefinition = register(
        StatementBuilder(name).apply(block).build(),
    )

    @Synchronized
    fun cachedStatement(
        name: String,
        block: StatementBuilder.() -> Unit,
    ): StatementDefinition {
        statementsByName[name]?.let { existing ->
            return existing
        }

        val created = StatementBuilder(name).apply(block).build()
        val existing = statementsByName[name]
        if (existing != null) {
            return existing
        }

        statementsByName[name] = created
        return created
    }

    @Synchronized
    fun lookup(name: String): StatementDefinition? = statementsByName[name]
}

val registry: StatementRegistry = StatementRegistry()
