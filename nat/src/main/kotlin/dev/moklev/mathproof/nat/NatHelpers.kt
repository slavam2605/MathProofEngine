package dev.moklev.mathproof.nat

import dev.moklev.mathproof.algebra.tactics.ring.ring
import dev.moklev.mathproof.algebra.tactics.ring.ringSimplify
import dev.moklev.mathproof.kernel.DerivationScope
import dev.moklev.mathproof.model.Expr

context(scope: DerivationScope)
fun natRing(left: Expr, right: Expr) =
    NatTheory.ring(left, right, NatCoefficients)

context(scope: DerivationScope)
fun natRingSimplify(expr: Expr) =
    NatTheory.ringSimplify(expr, NatCoefficients)
