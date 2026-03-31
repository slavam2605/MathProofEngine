package dev.moklev.mathproof

import dev.moklev.mathproof.kernel.StatementDefinition
import kotlin.reflect.KProperty1
import kotlin.reflect.full.memberProperties

fun discoverStatementsForTests(holder: Any): List<StatementDefinition> =
    holder::class.memberProperties
        .asSequence()
        .filter { it.returnType.classifier == StatementDefinition::class }
        .sortedBy { it.name }
        .map { property ->
            @Suppress("UNCHECKED_CAST")
            (property as KProperty1<Any, StatementDefinition>).get(holder)
        }
        .toList()
