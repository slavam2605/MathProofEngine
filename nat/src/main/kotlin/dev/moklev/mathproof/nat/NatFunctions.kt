package dev.moklev.mathproof.nat

import dev.moklev.mathproof.core.defineFunction
import dev.moklev.mathproof.core.global
import dev.moklev.mathproof.equality.eq
import dev.moklev.mathproof.fol.exists
import dev.moklev.mathproof.logic.implies
import dev.moklev.mathproof.model.*

object NatSorts {
    val Nat: Sort = NamedSort("Nat")
}

object NatFunctions {
    private val namespace = global.namespace("nat")

    val Zero = namespace.constant("zero", NatSorts.Nat, displayName = "0")
    val Succ = namespace.function(
        name = "succ",
        argumentSorts = arrayOf(NatSorts.Nat),
        returns = NatSorts.Nat,
        notation = ExprNotation.Prefix("S", precedence = ExprPrecedence.PREFIX)
    )

    internal val AddDef = namespace.defineFunction(
        name = "add",
        argumentSorts = arrayOf(NatSorts.Nat, NatSorts.Nat),
        returns = NatSorts.Nat,
        notation = ExprNotation.Infix("+", precedence = ExprPrecedence.ADDITIVE, associativity = Associativity.LEFT)
    ) { add ->
        axiom("nat-add-definition-zero") {
            val x = parameter("x", NatSorts.Nat)
            conclusion(add(x, Zero) eq x)
        }
        axiom("nat-add-definition-succ") {
            val x = parameter("x", NatSorts.Nat)
            val y = parameter("y", NatSorts.Nat)
            conclusion(add(x, succ(y)) eq succ(add(x, y)))
        }
    }

    val Add = AddDef.symbol

    internal val MulDef = namespace.defineFunction(
        name = "mul",
        argumentSorts = arrayOf(NatSorts.Nat, NatSorts.Nat),
        returns = NatSorts.Nat,
        notation = ExprNotation.Infix("*", precedence = ExprPrecedence.MULTIPLICATIVE, associativity = Associativity.LEFT)
    ) { mul ->
        axiom("nat-mul-definition-zero") {
            val x = parameter("x", NatSorts.Nat)
            conclusion(mul(x, Zero) eq Zero)
        }
        axiom("nat-mul-definition-succ") {
            val x = parameter("x", NatSorts.Nat)
            val y = parameter("y", NatSorts.Nat)
            conclusion(mul(x, succ(y)) eq (Add(x, mul(x, y))))
        }
    }

    val Mul = MulDef.symbol

    internal val LeqDef = namespace.defineFunction(
        name = "leq",
        argumentSorts = arrayOf(NatSorts.Nat, NatSorts.Nat),
        returns = CoreSorts.Proposition,
        notation = ExprNotation.Infix("<=", precedence = ExprPrecedence.COMPARISON, associativity = Associativity.LEFT)
    ) { leq ->
        axiom("nat-leq-introduction") {
            val x = parameter("x", NatSorts.Nat)
            val y = parameter("y", NatSorts.Nat)
            conclusion(exists("t", NatSorts.Nat) { t -> x + t eq y } implies leq(x, y))
        }
        axiom("nat-leq-elimination") {
            val x = parameter("x", NatSorts.Nat)
            val y = parameter("y", NatSorts.Nat)
            conclusion(leq(x, y) implies exists("t", NatSorts.Nat) { t -> Add(x, t) eq y })
        }
    }

    val Leq = LeqDef.symbol

    init {
        registerNatSyntax()
    }
}