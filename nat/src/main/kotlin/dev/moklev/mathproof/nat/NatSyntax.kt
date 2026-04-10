package dev.moklev.mathproof.nat

import dev.moklev.mathproof.core.constant
import dev.moklev.mathproof.core.function
import dev.moklev.mathproof.model.Associativity
import dev.moklev.mathproof.model.CoreSorts
import dev.moklev.mathproof.model.Expr
import dev.moklev.mathproof.model.ExprNotation
import dev.moklev.mathproof.model.ExprNotationRegistry
import dev.moklev.mathproof.model.NamedSort
import dev.moklev.mathproof.model.Sort

object NatSorts {
    val Nat: Sort = NamedSort("Nat")
}

object NatFunctions {
    val Zero = constant("0", NatSorts.Nat)
    val Succ = function("S", NatSorts.Nat, returns = NatSorts.Nat)
    val Add = function("+", NatSorts.Nat, NatSorts.Nat, returns = NatSorts.Nat)
    val Mul = function("*", NatSorts.Nat, NatSorts.Nat, returns = NatSorts.Nat)
    val Leq = function("<=n", NatSorts.Nat, NatSorts.Nat, returns = CoreSorts.Proposition)

    init {
        ExprNotationRegistry.register { head, arguments ->
            when {
                head == Succ && arguments.size == 1 -> ExprNotation.Prefix("S", precedence = 85)
                head == Add && arguments.size == 2 -> ExprNotation.Infix("+", precedence = 60, associativity = Associativity.LEFT)
                head == Mul && arguments.size == 2 -> ExprNotation.Infix("*", precedence = 70, associativity = Associativity.LEFT)
                head == Leq && arguments.size == 2 -> ExprNotation.Infix("<=", precedence = 45, associativity = Associativity.LEFT)
                else -> null
            }
        }
    }
}

fun succ(expr: Expr): Expr = NatFunctions.Succ(expr)

operator fun Expr.plus(other: Expr): Expr = NatFunctions.Add(this, other)

operator fun Expr.times(other: Expr): Expr = NatFunctions.Mul(this, other)

infix fun Expr.leqNat(other: Expr): Expr = NatFunctions.Leq(this, other)

val Int.n: Expr get() = numeral(this)

fun numeral(value: Int): Expr {
    require(value >= 0) { "Natural numerals must be non-negative." }
    var result: Expr = NatFunctions.Zero
    repeat(value) {
        result = succ(result)
    }
    return result
}
