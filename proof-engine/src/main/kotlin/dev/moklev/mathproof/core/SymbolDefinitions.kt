package dev.moklev.mathproof.core

import dev.moklev.mathproof.kernel.StatementBuilder
import dev.moklev.mathproof.kernel.StatementDefinition
import dev.moklev.mathproof.model.ExprNotation
import dev.moklev.mathproof.model.Free
import dev.moklev.mathproof.model.Sort

class SymbolDefinition(
    val symbol: Free,
    private val axiomsByName: Map<String, StatementDefinition>,
) {
    val axioms: Map<String, StatementDefinition> = axiomsByName.toMap()
    val allAxioms: List<StatementDefinition> = axioms.values.toList()

    fun axiom(name: String): StatementDefinition =
        requireNotNull(axioms[name]) {
            "Symbol '${symbol.displayName}' does not define axiom '$name'. Available: ${axioms.keys.sorted()}."
        }
}

class SymbolDefinitionBuilder internal constructor(
    private val symbol: Free,
) {
    private val axiomsByName = linkedMapOf<String, StatementDefinition>()

    fun axiom(
        name: String,
        note: String? = null,
        block: StatementBuilder.() -> Unit,
    ): StatementDefinition {
        require(name.isNotBlank()) { "Axiom name must be non-blank." }
        require(name !in axiomsByName) {
            "Axiom '$name' is already declared for symbol '${symbol.symbol}'."
        }
        val statementName = "def.${symbol.symbol}.$name"
        val declared = dev.moklev.mathproof.core.axiom(
            name = statementName,
            note = note,
            block = block,
        )
        axiomsByName[name] = declared
        return declared
    }

    internal fun build(): SymbolDefinition = SymbolDefinition(
        symbol = symbol,
        axiomsByName = axiomsByName.toMap(),
    )
}

fun SymbolNamespace.defineSymbol(
    name: String,
    sort: Sort,
    displayName: String = name,
    block: SymbolDefinitionBuilder.(self: Free) -> Unit,
): SymbolDefinition {
    val symbol = free(name = name, sort = sort, displayName = displayName)
    return defineWithSymbol(symbol, block)
}

private fun defineWithSymbol(
    symbol: Free,
    block: SymbolDefinitionBuilder.(self: Free) -> Unit,
): SymbolDefinition {
    val builder = SymbolDefinitionBuilder(symbol)
    builder.block(symbol)
    return builder.build()
}

fun SymbolNamespace.defineConstant(
    name: String,
    sort: Sort,
    displayName: String = name,
    block: SymbolDefinitionBuilder.(self: Free) -> Unit,
): SymbolDefinition = defineSymbol(
    name = name,
    sort = sort,
    displayName = displayName,
    block = block,
)

fun SymbolNamespace.defineFunction(
    name: String,
    vararg argumentSorts: Sort,
    returns: Sort,
    displayName: String = name,
    block: SymbolDefinitionBuilder.(self: Free) -> Unit,
): SymbolDefinition = defineSymbol(
    name = name,
    sort = functionSort(*argumentSorts, returns = returns),
    displayName = displayName,
    block = block,
)

fun SymbolNamespace.defineFunction(
    name: String,
    vararg argumentSorts: Sort,
    returns: Sort,
    notation: ExprNotation,
    block: SymbolDefinitionBuilder.(self: Free) -> Unit,
): SymbolDefinition {
    val symbol = function(
        name = name,
        *argumentSorts,
        returns = returns,
        notation = notation,
    )
    return defineWithSymbol(symbol, block)
}
