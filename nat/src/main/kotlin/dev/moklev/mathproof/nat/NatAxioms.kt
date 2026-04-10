package dev.moklev.mathproof.nat

import dev.moklev.mathproof.core.functionSort
import dev.moklev.mathproof.core.statement
import dev.moklev.mathproof.equality.eq
import dev.moklev.mathproof.fol.exists
import dev.moklev.mathproof.fol.forall
import dev.moklev.mathproof.logic.implies
import dev.moklev.mathproof.logic.not
import dev.moklev.mathproof.model.CoreSorts
import dev.moklev.mathproof.nat.NatTheory.leq

object NatAxioms {
    // ========== Core Axioms ==========

    val succInjective = statement("nat-succ-injective") {
        val x = parameter("x", NatSorts.Nat)
        val y = parameter("y", NatSorts.Nat)

        conclusion((succ(x) eq succ(y)) implies (x eq y))
        assumed("Trusted arithmetic axiom: successor is injective.")
    }

    val succNotZero = statement("nat-succ-zero") {
        val x = parameter("x", NatSorts.Nat)

        conclusion(!(succ(x) eq NatFunctions.Zero))
        assumed("Trusted arithmetic axiom: zero is never a successor.")
    }

    val induction = statement("nat-induction") {
        val predicate = parameter("predicate", functionSort(NatSorts.Nat, returns = CoreSorts.Proposition))

        val pZero = predicate(NatFunctions.Zero)
        val forallStep = forall("n", NatSorts.Nat) { predicate(it) implies predicate(succ(it)) }
        val forallP = forall("n", NatSorts.Nat) { predicate(it) }

        conclusion(pZero implies (forallStep implies forallP))
        assumed("Trusted induction schema for natural numbers.")
    }

    // ========== Addition Definition ==========

    val addDefinitionZero = statement("nat-add-definition-zero") {
        val x = parameter("x", NatSorts.Nat)

        conclusion((x + NatFunctions.Zero) eq x)
        assumed("Trusted arithmetic axiom: addition with zero is the identity.")
    }

    val addDefinitionSucc = statement("nat-add-definition-succ") {
        val x = parameter("x", NatSorts.Nat)
        val y = parameter("y", NatSorts.Nat)

        conclusion((x + succ(y)) eq succ(x + y))
        assumed("Trusted arithmetic axiom: addition with a successor unfolds recursively on the right.")
    }

    // ========== Multiplication Definition ==========

    val mulDefinitionZero = statement("nat-mul-definition-zero") {
        val x = parameter("x", NatSorts.Nat)

        conclusion(x * NatFunctions.Zero eq NatFunctions.Zero)
        assumed("Definition of multiplication with zero.")
    }

    val mulDefinitionSucc = statement("nat-mul-definition-succ") {
        val x = parameter("x", NatSorts.Nat)
        val y = parameter("y", NatSorts.Nat)

        conclusion(x * succ(y) eq (x + x * y))
        assumed("Recursive definition of multiplication with a successor.")
    }

    // ========== Order Definition ==========

    val leqIntroduction = statement("nat-leq-introduction") {
        val a = parameter("a", NatSorts.Nat)
        val b = parameter("b", NatSorts.Nat)

        conclusion(exists("x", NatSorts.Nat) { x -> a + x eq b } implies leq(a, b))
        assumed("Definition of Nat.leq: introduction.")
    }

    val leqElimination = statement("nat-leq-elimination") {
        val a = parameter("a", NatSorts.Nat)
        val b = parameter("b", NatSorts.Nat)

        conclusion(leq(a, b) implies exists("x", NatSorts.Nat) { x -> a + x eq b })
        assumed("Definition of Nat.leq: elimination.")
    }
}
