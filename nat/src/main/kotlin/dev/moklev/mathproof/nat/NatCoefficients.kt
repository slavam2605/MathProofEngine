package dev.moklev.mathproof.nat

import dev.moklev.mathproof.algebra.tactics.ring.RingCoefficients
import dev.moklev.mathproof.kernel.DerivationFact
import dev.moklev.mathproof.kernel.DerivationScope
import dev.moklev.mathproof.model.Apply
import dev.moklev.mathproof.model.Expr

object NatCoefficients : RingCoefficients {
    override fun isConstant(expr: Expr): Boolean {
        var current: Expr = expr
        while (current is Apply && current.function == NatFunctions.Succ) {
            current = current.argument
        }
        return current == NatFunctions.Zero
    }

    context(scope: DerivationScope)
    override fun add(left: Expr, right: Expr): DerivationFact {
        val a = left.natAsInt
        val b = right.natAsInt
        return scope.infer(NatLibrary.addNatConstants(a, b))
    }

    context(scope: DerivationScope)
    override fun mul(left: Expr, right: Expr): DerivationFact {
        val a = left.natAsInt
        val b = right.natAsInt
        return scope.infer(NatLibrary.mulNatConstants(a, b))
    }
}
