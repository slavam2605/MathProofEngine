package dev.moklev.mathproof.nat

import dev.moklev.mathproof.core.global
import dev.moklev.mathproof.model.Apply
import dev.moklev.mathproof.model.Associativity
import dev.moklev.mathproof.model.CoreSorts
import dev.moklev.mathproof.model.Expr
import dev.moklev.mathproof.model.ExprNotation
import dev.moklev.mathproof.model.ExprPrecedence
import dev.moklev.mathproof.model.ExprNotationRegistry
import dev.moklev.mathproof.model.NamedSort
import dev.moklev.mathproof.model.Sort

object NatSorts {
    val Nat: Sort = NamedSort("Nat")
}

object NatFunctions {
    private val namespace = global.namespace("nat")

    val Zero = namespace.constant("zero", NatSorts.Nat, displayName = "0")
    val Succ = namespace.function("succ", NatSorts.Nat, returns = NatSorts.Nat, displayName = "S")
    val Add = namespace.function("add", NatSorts.Nat, NatSorts.Nat, returns = NatSorts.Nat, displayName = "+")
    val Mul = namespace.function("mul", NatSorts.Nat, NatSorts.Nat, returns = NatSorts.Nat, displayName = "*")
    val Leq = namespace.function("leq", NatSorts.Nat, NatSorts.Nat, returns = CoreSorts.Proposition, displayName = "<=n")

    init {
        ExprNotationRegistry.register { head, arguments ->
            when {
                head == Succ && arguments.size == 1 -> ExprNotation.Prefix("S", precedence = ExprPrecedence.PREFIX)
                head == Add && arguments.size == 2 -> ExprNotation.Infix(
                    "+",
                    precedence = ExprPrecedence.ADDITIVE,
                    associativity = Associativity.LEFT,
                )
                head == Mul && arguments.size == 2 -> ExprNotation.Infix(
                    "*",
                    precedence = ExprPrecedence.MULTIPLICATIVE,
                    associativity = Associativity.LEFT,
                )
                head == Leq && arguments.size == 2 -> ExprNotation.Infix(
                    "<=",
                    precedence = ExprPrecedence.COMPARISON,
                    associativity = Associativity.LEFT,
                )
                else -> null
            }
        }
        ExprNotationRegistry.register { expr: Expr -> asNumeralOrNull(expr)?.toString() }
    }
}

fun succ(expr: Expr): Expr = NatFunctions.Succ(expr)

operator fun Expr.plus(other: Expr): Expr = NatFunctions.Add(this, other)

operator fun Expr.times(other: Expr): Expr = NatFunctions.Mul(this, other)

infix fun Expr.leqNat(other: Expr): Expr = NatFunctions.Leq(this, other)

val Int.n: Expr get() = numeral(this)

val Expr.natAsIntOrNull: Int? get() = asNumeralOrNull(this)

val Expr.natAsInt: Int get() = asNumeral(this)

private fun numeral(value: Int): Expr {
    require(value >= 0) { "Natural numerals must be non-negative." }
    var result: Expr = NatFunctions.Zero
    repeat(value) {
        result = succ(result)
    }
    return result
}

private fun asNumeralOrNull(expr: Expr): Int? {
    var value = 0
    var current = expr
    while (true) {
        if (current == NatFunctions.Zero) {
            return value
        }
        if (current is Apply && current.function == NatFunctions.Succ) {
            value += 1
            current = current.argument
            continue
        }
        return null
    }
}

private fun asNumeral(expr: Expr): Int {
    return asNumeralOrNull(expr) ?: error("Cannot convert $expr to natural number")
}
