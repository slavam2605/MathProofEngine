package dev.moklev.mathproof.nat

import dev.moklev.mathproof.core.statement
import dev.moklev.mathproof.dsl.Occurences
import dev.moklev.mathproof.equality.EqualityAxioms
import dev.moklev.mathproof.equality.EqualityLibrary
import dev.moklev.mathproof.equality.dsl.flipEq
import dev.moklev.mathproof.equality.dsl.replace
import dev.moklev.mathproof.equality.eq
import dev.moklev.mathproof.fol.FirstOrderAxioms
import dev.moklev.mathproof.fol.dsl.introduceExists
import dev.moklev.mathproof.fol.eliminateExists
import dev.moklev.mathproof.fol.exists
import dev.moklev.mathproof.fol.forAllByGeneralization
import dev.moklev.mathproof.kernel.auto
import dev.moklev.mathproof.logic.LogicAxioms
import dev.moklev.mathproof.logic.LogicAxioms.modusPonens
import dev.moklev.mathproof.logic.LogicLibrary
import dev.moklev.mathproof.logic.and
import dev.moklev.mathproof.logic.applyByMpChain
import dev.moklev.mathproof.logic.assume
import dev.moklev.mathproof.logic.implies
import dev.moklev.mathproof.logic.not
import dev.moklev.mathproof.model.Expr
import dev.moklev.mathproof.nat.NatSorts.Nat
import dev.moklev.mathproof.nat.NatTheory.addCommutative
import dev.moklev.mathproof.nat.leqNat as leq

object NatLibrary {
    /**
     * `x: Nat`
     *
     * `0 + x == x`
     *
     * Special proof without use of add-commutative for [NatSemiringEvidence.addCommutativeEvidence].
     */
    val addZeroLeft = statement("nat-add-zero-left-comm-free") {
        val x = parameter("x", Nat)

        conclusion((0.n + x) eq x)
        proof {
            val base = infer(NatTheory.addZeroRight(0.n)) // 0 + 0 == 0

            val step = forAllByGeneralization("y", Nat) { y ->
                assume((0.n + y) eq y) { zeroY -> // 0 + y == y
                    infer(NatAxioms.addDefinitionSucc(0.n, y)).replace(zeroY)
                } // 0 + y == y -> 0 + S(y) == S(y)
            }

            val forallY = applyByMpChain(NatAxioms.induction, base, step)
            applyByMpChain(FirstOrderAxioms.forallInstantiation(auto(), x), forallY)
        }
    }

    /**
     * `x, y: Nat`
     *
     * `S(x) + y == S(x + y)`
     *
     * Special proof without use of add-commutative for [NatSemiringEvidence.addCommutativeEvidence].
     */
    val addSuccLeft = statement("nat-add-succ-left-comm-free") {
        val x = parameter("x", Nat)
        val y = parameter("y", Nat)

        conclusion((succ(x) + y) eq succ(x + y))
        proof {
            val base = run {
                val step1 = infer(NatAxioms.addDefinitionZero(succ(x))) // S(x) + 0 == S(x)
                val step2 = infer(NatAxioms.addDefinitionZero(x)).flipEq() // x == x + 0
                step1.replace(step2, Occurences.Last) // S(x) + 0 == S(x + 0)
            }

            val step = forAllByGeneralization("t", Nat) { t ->
                assume((succ(x) + t) eq succ(x + t)) { prevStep -> // S(x) + t == S(x + t)
                    val step1 = infer(NatAxioms.addDefinitionSucc(succ(x), t)) // S(x) + S(t) == S(S(x) + t)
                    val step2 = step1.replace(prevStep) // S(x) + S(t) == S(S(x + t))
                    val step3 = infer(NatAxioms.addDefinitionSucc(x, t)).flipEq() // S(x + t) == x + S(t)
                    step2.replace(step3) // S(x) + S(t) == S(x + S(t))
                }
            }

            val forallT = applyByMpChain(NatAxioms.induction, base, step)
            applyByMpChain(FirstOrderAxioms.forallInstantiation(auto(), y), forallT)
        }
    }

    /**
     * `x: Nat`
     *
     * `x + S(0) == S(x)`
     */
    val addOneRight = statement("nat-add-one-right") {
        val x = parameter("x", Nat)

        conclusion((x + 1.n) eq succ(x))
        proof {
            val unfold = infer(NatAxioms.addDefinitionSucc(x, 0.n)) // x + S(0) == S(x + 0)
            val collapseInner = infer(NatTheory.addZeroRight(x)) // x + 0 == x
            unfold.replace(collapseInner) // x + S(0) == S(x)
        }
    }

    /**
     * `x: Nat`
     *
     * `S(0) + x == S(x)`
     */
    val addOneLeft = statement("nat-add-one-left") {
        val x = parameter("x", Nat)

        conclusion(1.n + x eq succ(x))
        proof {
            val step1 = infer(addCommutative(1.n, x)) // S(0) + x == x + S(0)
            val step2 = infer(addOneRight(x)) // x + S(0) == S(x)
            applyByMpChain(EqualityLibrary.transitivity, step1, step2) // S(0) + x == S(x)
        }
    }

    /**
     * `x: Nat`
     *
     * `0 <= x`
     */
    val zeroLeqAll = statement("nat-zero-leq-n") {
        val x = parameter("x", Nat)

        conclusion(0.n leq x)
        proof {
            val oxx = infer(addZeroLeft(x)) // 0 + x == x
            val ex = oxx.introduceExists(x, Occurences.First)
            applyByMpChain(NatAxioms.leqIntroduction, ex)
        }
    }

    /**
     * `a, b: Nat`
     *
     * `S(a) + b == a + S(b)`
     */
    val addSuccShift = statement("nat-add-succ-shift") {
        val a = parameter("a", Nat)
        val b = parameter("b", Nat)

        conclusion((succ(a) + b) eq (a + succ(b)))
        proof {
            val step1 = infer(NatAxioms.addDefinitionSucc(a, b)) // a + S(b) == S(a + b)
            val step2 = infer(NatAxioms.addDefinitionSucc(b, a)) // b + S(a) == S(b + a)
            val step3 = infer(addCommutative(a, b)) // a + b == b + a
            val step4 = step1.replace(step3).flipEq() // S(b + a) == a + S(b)
            val step5 = step2.replace(step4) // b + S(a) == a + S(b)
            val step6 = infer(addCommutative(b, succ(a))) // b + S(a) == S(a) + b
            step5.replace(step6) // S(a) + b == a + S(b)
        }
    }

    /**
     * `a, b: Nat`
     *
     * `(a + b == a) -> (b == 0)`
     */
    val sumEqualsLeftImpliesRightZero = statement("nat-sum-equals-left-implies-right-zero") {
        val a = parameter("a", Nat)
        val b = parameter("b", Nat)

        conclusion(((a + b) eq a) implies (b eq 0.n))
        proof {
            val base = assume((0.n + b) eq 0.n) { zeroBZero -> // 0 + b == 0
                val zeroBEqB = infer(addZeroLeft(b)) // 0 + b == b
                zeroBZero.replace(zeroBEqB) // b == 0
            } // (0 + b == 0) -> b == 0

            val step = forAllByGeneralization("n", Nat) { n ->
                assume(((n + b) eq n) implies (b eq 0.n)) { aBAbZero -> // (n + b == n) -> b == 0
                    assume((succ(n) + b) eq succ(n)) { saBsA -> // S(n) + b == S(n)
                        val sabAsB = infer(addSuccShift(n, b)) // S(n) + b == n + S(b)
                        val asbSAB = infer(NatAxioms.addDefinitionSucc(n, b)) // n + S(b) == S(n + b)
                        val sabSAB = applyByMpChain(EqualityLibrary.transitivity, sabAsB, asbSAB) // S(n) + b == S(n + b)
                        val sabSABRev = applyByMpChain(EqualityLibrary.symmetry, sabSAB) // S(n + b) == S(n) + b
                        val succEq = applyByMpChain(EqualityLibrary.transitivity, sabSABRev, saBsA) // S(n + b) == S(n)
                        val aba = applyByMpChain(NatAxioms.succInjective, succEq) // n + b == n
                        infer(modusPonens, aba, aBAbZero)
                    }
                } // ((n + b == n) -> b == 0) -> (S(n) + b == S(n)) -> b == 0
            } // ∀n. ((n + b == n) -> b == 0) -> (S(n) + b == S(n)) -> b == 0

            val forallN = applyByMpChain(NatAxioms.induction, base, step)

            applyByMpChain(FirstOrderAxioms.forallInstantiation(auto(), a), forallN)
        }
    }

    /**
     * `a: Nat`
     *
     * `!(a == 0) -> ∃x. S(x) == a`
     */
    val nonZeroHasPredecessor = statement("nat-non-zero-has-predecessor") {
        val a = parameter("a", Nat)
        fun targetF(param: Expr) = exists("x", Nat) { x -> succ(x) eq param }

        conclusion(!(a eq 0.n) implies targetF(a))
        proof {
            val zeroId = infer(EqualityAxioms.reflexivity(0.n)) // 0 == 0
            val base = applyByMpChain(
                LogicLibrary.exFalsoAlt(auto(), targetF(0.n)),
                zeroId,
            ) // !(0 == 0) -> target(0)

            val step = forAllByGeneralization("x", Nat) { x ->
                assume(!(x eq 0.n) implies targetF(x)) { xStep -> // !(x == 0) -> target(x)
                    val sxId = infer(EqualityAxioms.reflexivity(succ(x))) // S(x) == S(x)
                    val existsTarget = sxId.introduceExists(x, Occurences.First)
                    applyByMpChain(
                        LogicAxioms.hilbertAxiom1(auto(), !(succ(x) eq 0.n)),
                        existsTarget,
                    )
                }
            }

            val forallResult = applyByMpChain(NatAxioms.induction, base, step)
            applyByMpChain(FirstOrderAxioms.forallInstantiation(auto(), a), forallResult)
        }
    }

    /**
     * `a, b: Nat`
     *
     * `(a + b == 0) -> (a == 0)`
     */
    val sumZeroImpliesLeftZero = statement("nat-sum-zero-implies-left-zero") {
        val a = parameter("a", Nat)
        val b = parameter("b", Nat)

        conclusion(((a + b) eq 0.n) implies (a eq 0.n))
        proof {
            assume((a + b) eq 0.n) { abZero -> // a + b == 0
                contradiction(!(a eq 0.n)) { naZero ->
                    val existsX = applyByMpChain(nonZeroHasPredecessor, naZero) // ∃x. S(x) == a
                    eliminateExists(existsX, "x") { x, sxa ->
                        val asx = applyByMpChain(EqualityLibrary.symmetry, sxa) // a == S(x)
                        val sxbZero = abZero.replace(asx) // S(x) + b == 0
                        val bsxSXB = infer(addCommutative(b, succ(x))) // b + S(x) == S(x) + b
                        val bsxZero = applyByMpChain(EqualityLibrary.transitivity, bsxSXB, sxbZero) // b + S(x) == 0
                        val succEq = applyByMpChain(NatAxioms.addDefinitionSucc(b, x)) // b + S(x) == S(b + x)
                        val succEqRev = applyByMpChain(EqualityLibrary.symmetry, succEq) // S(b + x) == b + S(x)
                        val succZero = applyByMpChain(EqualityLibrary.transitivity, succEqRev, bsxZero) // S(b + x) == 0
                        val succNotZero = infer(NatAxioms.succNotZero(b + x)) // !(S(b + x) = 0)
                        applyByMpChain(LogicLibrary.exFalso(auto(), a eq 0.n), succNotZero, succZero)
                    }
                }
            }
        }
    }

    /**
     * `a, b: Nat`
     *
     * `(a + b == 0) -> (b == 0)`
     */
    val sumZeroImpliesRightZero = statement("nat-sum-zero-implies-right-zero") {
        val a = parameter("a", Nat)
        val b = parameter("b", Nat)

        conclusion(((a + b) eq 0.n) implies (b eq 0.n))
        proof {
            assume((a + b) eq 0.n) { abZero -> // a + b == 0
                val abBA = infer(addCommutative(a, b)) // a + b == b + a
                val baZero = abZero.replace(abBA) // b + a == 0
                applyByMpChain(sumZeroImpliesLeftZero, baZero)
            }
        }
    }

    /**
     * `a, b: Nat`
     *
     * `(a + b == 0) -> ((a == 0) and (b == 0))`
     */
    val sumZeroImpliesBothZero = statement("nat-sum-zero-implies-both-zero") {
        val a = parameter("a", Nat)
        val b = parameter("b", Nat)

        conclusion(((a + b) eq 0.n) implies ((a eq 0.n) and (b eq 0.n)))
        proof {
            assume((a + b) eq 0.n) { abZero ->
                val aZero = applyByMpChain(sumZeroImpliesLeftZero, abZero)
                val bZero = applyByMpChain(sumZeroImpliesRightZero, abZero)
                applyByMpChain(LogicAxioms.andIntroduction, aZero, bZero)
            }
        }
    }

    /**
     * `a: Nat`
     *
     * `0 * a == 0`
     */
    val mulZeroLeft = statement("nat-mul-zero-left") {
        val a = parameter("a", Nat)

        conclusion(0.n * a eq 0.n)
        proof {
            val base = infer(NatAxioms.mulDefinitionZero(0.n)) // 0 * 0 == 0
            val step = forAllByGeneralization("x", Nat) { x ->
                assume(0.n * x eq 0.n) { zeroXZero -> // 0 * x == 0
                    val step1 = infer(NatAxioms.mulDefinitionSucc(0.n, x)) // 0 * S(x) == 0 + 0 * x
                    val step2 = infer(addZeroLeft(0.n * x)) // 0 + 0 * x == 0 * x
                    val step3 = applyByMpChain(EqualityLibrary.transitivity, step1, step2) // 0 * S(x) == 0 * x
                    applyByMpChain(EqualityLibrary.transitivity, step3, zeroXZero)
                }
            }
            val forallY = applyByMpChain(NatAxioms.induction, base, step)
            applyByMpChain(FirstOrderAxioms.forallInstantiation(auto(), a), forallY)
        }
    }

    /**
     * `a, b: Nat`
     *
     * `S(a) * b == b + a * b`
     */
    val mulSuccLeft = statement("nat-mul-succ-left") {
        val a = parameter("a", Nat)
        val b = parameter("b", Nat)

        conclusion(succ(a) * b eq (b + a * b))
        proof {
            val base = run {
                val step1 = infer(NatAxioms.mulDefinitionZero(succ(a))) // S(a) * 0 == 0
                val step2 = infer(NatAxioms.mulDefinitionZero(a)) // a * 0 == 0
                val step3 = infer(addZeroLeft(a * 0.n)) // 0 + a * 0 == a * 0
                val step4 = applyByMpChain(EqualityLibrary.transitivity, step3, step2).flipEq() // 0 == 0 + a * 0
                applyByMpChain(EqualityLibrary.transitivity, step1, step4) // S(a) * 0 == 0 + a * 0
            }

            val step = forAllByGeneralization("y", Nat) { y ->
                assume(succ(a) * y eq (y + a * y)) { prevStep -> // S(a) * y == y + a * y
                    val step1 = infer(NatAxioms.mulDefinitionSucc(succ(a), y)) // S(a) * S(y) == S(a) + S(a) * y
                    val step2 = step1.replace(prevStep) // S(a) * S(y) == S(a) + (y + a * y)
                    val step3 = infer(NatTheory.addAssociative(succ(a), y, a * y)).flipEq() // S(a) + (y + a * y) == (S(a) + y) + a * y
                    val step4 = applyByMpChain(EqualityLibrary.transitivity, step2, step3) // S(a) * S(y) == (S(a) + y) + a * y
                    val step5 = infer(addSuccShift(a, y)) // S(a) + y == a + S(y)
                    val step6 = step4.replace(step5) // S(a) * S(y) == (a + S(y)) + a * y
                    val step7 = infer(addCommutative(a, succ(y))) // a + S(y) == S(y) + a
                    val step8 = step6.replace(step7) // S(a) * S(y) == (S(y) + a) + a * y
                    val step9 = infer(NatTheory.addAssociative(succ(y), a, a * y)) // (S(y) + a) + a * y == S(y) + (a + a * y)
                    val step10 = step8.replace(step9) // S(a) * S(y) == S(y) + (a + a * y)
                    val step11 = infer(NatAxioms.mulDefinitionSucc(a, y)).flipEq() // a + a * y == a * S(y)
                    step10.replace(step11) // S(a) * S(y) == S(y) + a * S(y)
                }
            }

            val forallX = applyByMpChain(NatAxioms.induction, base, step)
            applyByMpChain(FirstOrderAxioms.forallInstantiation(auto(), b), forallX)
        }
    }
}
