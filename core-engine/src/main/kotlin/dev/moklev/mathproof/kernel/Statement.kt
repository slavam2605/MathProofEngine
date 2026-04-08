package dev.moklev.mathproof.kernel

import dev.moklev.mathproof.model.Expr
import dev.moklev.mathproof.model.Free
import dev.moklev.mathproof.model.Sort
import dev.moklev.mathproof.model.SortVariable
import dev.moklev.mathproof.model.betaNormalize
import dev.moklev.mathproof.model.matchSort
import dev.moklev.mathproof.model.resolve
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
    operator fun invoke(vararg arguments: Expr): StatementCall = call(arguments.toList())

    fun parameterNameForSymbol(symbol: String): String? =
        parameters.firstOrNull { parameter -> parameter.symbol == symbol }?.name

    fun autoCall(): StatementCall = call(parameters.map { _ -> auto() })

    fun call(arguments: List<Expr>): StatementCall {
        require(arguments.size == parameters.size) {
            "Statement '$name' expects ${parameters.size} arguments, but got ${arguments.size}."
        }
        if (arguments.none { argument -> argument.isAutoArgument() }) {
            return instantiate(arguments)
        }

        val sortBindings = linkedMapOf<SortVariable, Sort>()
        parameters.zip(arguments).forEach { (parameter, rawArgument) ->
            if (rawArgument.isAutoArgument()) {
                return@forEach
            }
            require(matchSort(parameter.sort, rawArgument.sort, sortBindings)) {
                "Statement '$name' expects argument '${parameter.name}' to have sort '${parameter.sort}', but got '${rawArgument.sort}'."
            }
        }

        val resolvedArguments = parameters.zip(arguments).map { (parameter, rawArgument) ->
            rawArgument.retargetAutoSort(parameter.sort.resolve(sortBindings)).betaNormalize()
        }
        val patternArguments = parameters.zip(resolvedArguments).map { (parameter, argument) ->
            if (argument.isAutoArgument()) {
                Free(
                    symbol = parameter.symbol,
                    sort = parameter.sort.resolve(sortBindings),
                    displayName = parameter.name,
                )
            } else {
                argument
            }
        }
        val bindings = parameters.map { it.symbol }.zip(patternArguments).toMap()
        return StatementCall(
            statement = this,
            arguments = resolvedArguments,
            premises = premises.map { it.substitute(bindings).resolveSorts(sortBindings).betaNormalize() },
            conclusion = conclusion.substitute(bindings).resolveSorts(sortBindings).betaNormalize(),
        )
    }

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
