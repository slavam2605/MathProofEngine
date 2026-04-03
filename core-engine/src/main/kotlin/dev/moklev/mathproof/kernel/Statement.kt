package dev.moklev.mathproof.kernel

import dev.moklev.mathproof.model.Expr
import dev.moklev.mathproof.model.Sort
import dev.moklev.mathproof.model.SortVariable
import dev.moklev.mathproof.model.betaNormalize
import dev.moklev.mathproof.model.matchSort
import dev.moklev.mathproof.model.resolveSorts
import dev.moklev.mathproof.model.substitute

data class StatementParameter(
    val name: String,
    val sort: Sort,
    internal val symbol: String,
)

sealed interface StatementSupport

data class AssumedTrue(val note: String? = null) : StatementSupport

data class ProofProvided(val proof: ProofScript) : StatementSupport

data class StatementDefinition(
    val name: String,
    val parameters: List<StatementParameter>,
    val premises: List<Expr>,
    val conclusion: Expr,
    val support: StatementSupport,
    val instantiationCheck: ((List<Expr>) -> Unit)? = null,
) {
    operator fun invoke(vararg arguments: Expr): StatementCall = instantiate(arguments.toList())

    fun parameterNameForSymbol(symbol: String): String? =
        parameters.firstOrNull { parameter -> parameter.symbol == symbol }?.name

    fun instantiate(arguments: List<Expr>): StatementCall {
        require(arguments.size == parameters.size) {
            "Statement '$name' expects ${parameters.size} arguments, but got ${arguments.size}."
        }

        val sortBindings = linkedMapOf<SortVariable, Sort>()
        parameters.zip(arguments).forEach { (parameter, argument) ->
            require(matchSort(parameter.sort, argument.sort, sortBindings)) {
                "Statement '$name' expects argument '${parameter.name}' to have sort '${parameter.sort}', but got '${argument.sort}'."
            }
        }
        instantiationCheck?.invoke(arguments)

        val bindings = parameters.map { it.symbol }.zip(arguments).toMap()
        return StatementCall(
            statement = this,
            arguments = arguments,
            premises = premises.map { it.substitute(bindings).resolveSorts(sortBindings).betaNormalize() },
            conclusion = conclusion.substitute(bindings).resolveSorts(sortBindings).betaNormalize(),
        )
    }
}

data class StatementCall(
    val statement: StatementDefinition,
    val arguments: List<Expr>,
    val premises: List<Expr>,
    val conclusion: Expr,
)
