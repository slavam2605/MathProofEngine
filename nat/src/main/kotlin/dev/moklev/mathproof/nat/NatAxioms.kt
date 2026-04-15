package dev.moklev.mathproof.nat

import dev.moklev.mathproof.core.functionSort
import dev.moklev.mathproof.core.statement
import dev.moklev.mathproof.equality.eq
import dev.moklev.mathproof.fol.forall
import dev.moklev.mathproof.logic.implies
import dev.moklev.mathproof.logic.not
import dev.moklev.mathproof.model.CoreSorts

object NatAxioms {
    /**
     * `x: Nat`
     *
     * `!(succ(x) == 0)`
     */
    val succNotZero = statement("nat-succ-zero") {
        val x = parameter("x", NatSorts.Nat)

        conclusion(!(succ(x) eq NatFunctions.Zero))
        assumed("Trusted arithmetic axiom: zero is never a successor.")
    }

    /**
     * `x, y: Nat`
     *
     * `succ(x) == succ(y) -> x == y`
     */
    val succInjective = statement("nat-succ-injective") {
        val x = parameter("x", NatSorts.Nat)
        val y = parameter("y", NatSorts.Nat)

        conclusion((succ(x) eq succ(y)) implies (x eq y))
        assumed("Trusted arithmetic axiom: successor is injective.")
    }

    /**
     * `p: Nat -> Proposition`
     *
     * `p(0) -> (∀n. p(n) -> p(S(n))) -> ∀n. p(n)`
     */
    val induction = statement("nat-induction") {
        val predicate = parameter("predicate", functionSort(NatSorts.Nat, returns = CoreSorts.Proposition))

        val pZero = predicate(NatFunctions.Zero)
        val forallStep = forall("n", NatSorts.Nat) { predicate(it) implies predicate(succ(it)) }
        val forallP = forall("n", NatSorts.Nat) { predicate(it) }

        conclusion(pZero implies (forallStep implies forallP))
        assumed("Trusted induction schema for natural numbers.")
    }

    /**
     * `x: Nat`
     *
     * `x + 0 == x`
     */
    val addDefinitionZero = NatFunctions.AddDef.axiom("nat-add-definition-zero")

    /**
     * `x, y: Nat`
     *
     * `x + S(y) == S(x + y)`
     */
    val addDefinitionSucc = NatFunctions.AddDef.axiom("nat-add-definition-succ")

    /**
     * `x: Nat`
     *
     * `x * 0 == 0`
     */
    val mulDefinitionZero = NatFunctions.MulDef.axiom("nat-mul-definition-zero")

    /**
     * `x, y: Nat`
     *
     * `x * S(y) == x + x * y`
     */
    val mulDefinitionSucc = NatFunctions.MulDef.axiom("nat-mul-definition-succ")

    /**
     * `x, y: Nat`
     *
     * `(∃t. x + t == y) -> x <= y`
     */
    val leqIntroduction = NatFunctions.LeqDef.axiom("nat-leq-introduction")

    /**
     * `x, y: Nat`
     *
     * `x <= y -> (∃t. x + t == y)`
     */
    val leqElimination = NatFunctions.LeqDef.axiom("nat-leq-elimination")
}
