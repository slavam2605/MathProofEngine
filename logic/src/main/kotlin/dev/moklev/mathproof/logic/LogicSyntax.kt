package dev.moklev.mathproof.logic

import dev.moklev.mathproof.core.function
import dev.moklev.mathproof.model.Associativity
import dev.moklev.mathproof.model.CoreSorts
import dev.moklev.mathproof.model.Expr
import dev.moklev.mathproof.model.ExprNotation
import dev.moklev.mathproof.model.ExprNotationRegistry

object LogicFunctions {
    val And = function("and", CoreSorts.Proposition, CoreSorts.Proposition, returns = CoreSorts.Proposition)
    val Or = function("or", CoreSorts.Proposition, CoreSorts.Proposition, returns = CoreSorts.Proposition)
    val Implies = function("->", CoreSorts.Proposition, CoreSorts.Proposition, returns = CoreSorts.Proposition)
    val Not = function("!", CoreSorts.Proposition, returns = CoreSorts.Proposition)

    init {
        ExprNotationRegistry.register { head, arguments ->
            when {
                head == Not && arguments.size == 1 -> ExprNotation.Prefix("!", precedence = 85)
                head == And && arguments.size == 2 -> ExprNotation.Infix("and", precedence = 50)
                head == Or && arguments.size == 2 -> ExprNotation.Infix("or", precedence = 40)
                head == Implies && arguments.size == 2 -> ExprNotation.Infix("->", precedence = 30, associativity = Associativity.RIGHT)
                else -> null
            }
        }
    }
}

infix fun Expr.and(other: Expr): Expr = LogicFunctions.And(this, other)

infix fun Expr.or(other: Expr): Expr = LogicFunctions.Or(this, other)

infix fun Expr.implies(other: Expr): Expr = LogicFunctions.Implies(this, other)

operator fun Expr.not(): Expr = LogicFunctions.Not(this)
