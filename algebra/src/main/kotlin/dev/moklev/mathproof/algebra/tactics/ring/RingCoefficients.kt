package dev.moklev.mathproof.algebra.tactics.ring

import dev.moklev.mathproof.kernel.DerivationFact
import dev.moklev.mathproof.kernel.DerivationScope
import dev.moklev.mathproof.model.Expr

interface RingCoefficients {
    fun isConstant(expr: Expr): Boolean

    context(scope: DerivationScope)
    fun add(left: Expr, right: Expr): DerivationFact

    context(scope: DerivationScope)
    fun mul(left: Expr, right: Expr): DerivationFact
}