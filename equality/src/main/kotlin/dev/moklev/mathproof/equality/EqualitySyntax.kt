package dev.moklev.mathproof.equality

import dev.moklev.mathproof.core.global
import dev.moklev.mathproof.core.sortVariable
import dev.moklev.mathproof.model.Associativity
import dev.moklev.mathproof.model.CoreSorts
import dev.moklev.mathproof.model.Expr
import dev.moklev.mathproof.model.ExprNotation
import dev.moklev.mathproof.model.ExprNotationRegistry

object EqualityFunctions {
    private val operandSort = sortVariable("S")
    private val namespace = global.namespace("equality")

    val Eq = namespace.function("eq", operandSort, operandSort, returns = CoreSorts.Proposition, displayName = "=")

    init {
        ExprNotationRegistry.register { head, arguments ->
            when {
                head == Eq && arguments.size == 2 -> ExprNotation.Infix("=", precedence = 60, associativity = Associativity.LEFT)
                else -> null
            }
        }
    }
}

infix fun Expr.eq(other: Expr): Expr = EqualityFunctions.Eq(this, other)
