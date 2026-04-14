package dev.moklev.mathproof.logic

import dev.moklev.mathproof.core.global
import dev.moklev.mathproof.model.Associativity
import dev.moklev.mathproof.model.CoreSorts
import dev.moklev.mathproof.model.Expr
import dev.moklev.mathproof.model.ExprNotation
import dev.moklev.mathproof.model.ExprPrecedence
import dev.moklev.mathproof.model.ExprNotationRegistry

object LogicFunctions {
    private val namespace = global.namespace("logic")

    val And = namespace.function("and", CoreSorts.Proposition, CoreSorts.Proposition, returns = CoreSorts.Proposition, displayName = "and")
    val Or = namespace.function("or", CoreSorts.Proposition, CoreSorts.Proposition, returns = CoreSorts.Proposition, displayName = "or")
    val Implies = namespace.function("implies", CoreSorts.Proposition, CoreSorts.Proposition, returns = CoreSorts.Proposition, displayName = "->")
    val Not = namespace.function("not", CoreSorts.Proposition, returns = CoreSorts.Proposition, displayName = "!")

    init {
        ExprNotationRegistry.register { head, arguments ->
            when {
                head == Not && arguments.size == 1 -> ExprNotation.Prefix("!", precedence = ExprPrecedence.PREFIX)
                head == And && arguments.size == 2 -> ExprNotation.Infix("and", precedence = ExprPrecedence.CONJUNCTION)
                head == Or && arguments.size == 2 -> ExprNotation.Infix("or", precedence = ExprPrecedence.DISJUNCTION)
                head == Implies && arguments.size == 2 -> ExprNotation.Infix(
                    "->",
                    precedence = ExprPrecedence.IMPLICATION,
                    associativity = Associativity.RIGHT,
                )
                else -> null
            }
        }
    }
}

infix fun Expr.and(other: Expr): Expr = LogicFunctions.And(this, other)

infix fun Expr.or(other: Expr): Expr = LogicFunctions.Or(this, other)

infix fun Expr.implies(other: Expr): Expr = LogicFunctions.Implies(this, other)

operator fun Expr.not(): Expr = LogicFunctions.Not(this)
