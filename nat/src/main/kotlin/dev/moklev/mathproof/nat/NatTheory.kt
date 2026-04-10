package dev.moklev.mathproof.nat

import dev.moklev.mathproof.algebra.theories.Commutative
import dev.moklev.mathproof.algebra.theories.Ordered
import dev.moklev.mathproof.algebra.theories.SemiringTheory
import dev.moklev.mathproof.nat.NatSorts.Nat

object NatTheory : SemiringTheory(
    name = "nat",
    carrier = Nat,
    zero = NatFunctions.Zero,
    one = succ(NatFunctions.Zero),
    add = NatFunctions.Add,
    mul = NatFunctions.Mul,
), Commutative<NatTheory>, Ordered<NatTheory> {
    override val semiringEvidence by lazy { NatSemiringEvidence() }

    override val leq = NatFunctions.Leq
    override val commutativeTheory = this
    override val commutativeEvidence by lazy { NatCommutativeEvidence() }

    override val orderedTheory = this
    override val orderedEvidence by lazy { NatOrderedEvidence() }

    init {
        requireOrderRelation()
    }
}
