package dev.moklev.mathproof.nat

import dev.moklev.mathproof.model.Apply
import dev.moklev.mathproof.model.Expr
import dev.moklev.mathproof.model.ExprNotationRegistry

internal fun registerNatSyntax() {
    ExprNotationRegistry.register { expr -> asNumeralOrNull(expr)?.toString() }
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
