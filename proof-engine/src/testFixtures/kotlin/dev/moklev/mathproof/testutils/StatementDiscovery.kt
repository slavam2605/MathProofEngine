package dev.moklev.mathproof.testutils

import dev.moklev.mathproof.kernel.StatementDefinition
import kotlin.reflect.KProperty1
import kotlin.reflect.full.memberProperties

private data class StatementFingerprint(
    val name: String,
    val parameters: List<String>,
    val premises: List<String>,
    val conclusion: String,
)

fun discoverStatements(holder: Any): List<StatementDefinition> =
    holder::class.memberProperties
        .asSequence()
        .filter { it.returnType.classifier == StatementDefinition::class }
        .sortedBy { it.name }
        .map { property ->
            @Suppress("UNCHECKED_CAST")
            (property as KProperty1<Any, StatementDefinition>).get(holder)
        }
        .toList()

fun discoverStatementsChecked(holder: Any): List<StatementDefinition> {
    val discovered = discoverStatements(holder)

    check(discovered.isNotEmpty()) {
        "No statements discovered for '${holder::class.qualifiedName}'."
    }

    val duplicateFingerprints = discovered
        .groupBy { statement ->
            StatementFingerprint(
                name = statement.name,
                parameters = statement.parameters.map { parameter -> "${parameter.name}:${parameter.sort}" },
                premises = statement.premises.map { premise -> premise.toString() },
                conclusion = statement.conclusion.toString(),
            )
        }
        .filterValues { statements -> statements.size > 1 }

    check(duplicateFingerprints.isEmpty()) {
        buildString {
            append("Duplicate discovered statements for '${holder::class.qualifiedName}': ")
            append(
                duplicateFingerprints
                    .map { (fingerprint, statements) -> "${fingerprint.name} x${statements.size}" }
                    .sorted()
                    .joinToString(", "),
            )
        }
    }

    return discovered
}
