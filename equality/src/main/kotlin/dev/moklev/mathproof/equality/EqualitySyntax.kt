package dev.moklev.mathproof.equality

import dev.moklev.mathproof.core.function
import dev.moklev.mathproof.core.sortVariable
import dev.moklev.mathproof.model.Associativity
import dev.moklev.mathproof.model.CoreSorts
import dev.moklev.mathproof.model.Expr
import dev.moklev.mathproof.model.ExprNotation
import dev.moklev.mathproof.model.ExprNotationRegistry

object EqualityFunctions {
    private val operandSort = sortVariable("S")

    val Eq = function("=", operandSort, operandSort, returns = CoreSorts.Proposition)

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
