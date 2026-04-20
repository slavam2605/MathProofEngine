package dev.moklev.mathproof.nat

import dev.moklev.mathproof.algebra.theories.Ordered
import dev.moklev.mathproof.dsl.Occurences
import dev.moklev.mathproof.equality.EqualityLibrary
import dev.moklev.mathproof.equality.dsl.flipEq
import dev.moklev.mathproof.equality.dsl.replace
import dev.moklev.mathproof.fol.dsl.instantiateForall
import dev.moklev.mathproof.fol.dsl.introduceExists
import dev.moklev.mathproof.fol.eliminateExists
import dev.moklev.mathproof.fol.forAllByGeneralization
import dev.moklev.mathproof.fol.forall
import dev.moklev.mathproof.kernel.auto
import dev.moklev.mathproof.kernel.proved
import dev.moklev.mathproof.logic.*
import dev.moklev.mathproof.model.Expr
import dev.moklev.mathproof.nat.NatAxioms.leqElimination
import dev.moklev.mathproof.nat.NatAxioms.leqIntroduction
import dev.moklev.mathproof.nat.NatLibrary.addSuccLeft
import dev.moklev.mathproof.nat.NatLibrary.sumEqualsLeftImpliesRightZero
import dev.moklev.mathproof.nat.NatLibrary.sumZeroImpliesBothZero
import dev.moklev.mathproof.nat.NatSorts.Nat
import dev.moklev.mathproof.nat.NatTheory.addAssociative
import dev.moklev.mathproof.nat.NatTheory.addCommutative
import dev.moklev.mathproof.nat.NatTheory.addZeroRight
import dev.moklev.mathproof.nat.NatTheory.mul
import dev.moklev.mathproof.nat.NatTheory.zero
import dev.moklev.mathproof.nat.leqNat as leq

class NatOrderedEvidence : Ordered.Evidence {
    override fun orderReflexiveEvidence(a: Expr) = proved {
        val aZero = infer(addZeroRight(a)) // a + 0 == a
        val ex = aZero.introduceExists(zero) // ∃x. a + x == a
        applyMp(leqIntroduction, ex)
    }

    override fun orderTransitiveEvidence(a: Expr, b: Expr, c: Expr) = proved {
        assume(a leq b) { leqAB ->
            val exAB = applyMp(leqElimination(a, b), leqAB)
            assume(b leq c) { leqBC ->
                val exBC = applyMp(leqElimination(b, c), leqBC)
                eliminateExists(exAB, "x") { x, ab -> // a + x == b
                    eliminateExists(exBC, "y") { y, bc -> // b + y == c
                        val ba = ab.flipEq() // b == a + x
                        val axYEqC = bc.replace(ba) // (a + x) + y == c
                        val axyAssoc = infer(addAssociative(a, x, y)) // (a + x) + y == a + (x + y)
                        val aXyEqC = axYEqC.replace(axyAssoc) // a + (x + y) = c
                        val exAC = aXyEqC.introduceExists(x + y) // ∃z. a + z == c
                        applyMp(leqIntroduction, exAC) // a <= c
                    }
                }
            }
        }
    }

    override fun orderAntisymmetricEvidence(a: Expr, b: Expr) = proved {
        assume(a leq b) { leqAB ->
            val exAB = applyMp(leqElimination, leqAB)
            assume(b leq a) { leqBA ->
                val exBA = applyMp(leqElimination, leqBA)
                eliminateExists(exAB, "x") { x, ab -> // a + x == b
                    eliminateExists(exBA, "y") { y, ba -> // b + y == a
                        val axYeqA = ba.replace(ab.flipEq()) // (a + x) + y == a
                        val axyEqAXY = infer(addAssociative(a, x, y)) // (a + x) + y == a + (x + y)
                        val aXyEqA = axYeqA.replace(axyEqAXY) // a + (x + y) == a
                        val xyZero = applyMp(sumEqualsLeftImpliesRightZero, aXyEqA) // x + y == 0
                        val xAndYZero = applyMp(sumZeroImpliesBothZero, xyZero) // x == 0 && y == 0
                        val xZero = applyMp(LogicAxioms.andEliminationLeft, xAndYZero) // x == 0
                        val axEqAZero = ab.replace(xZero) // a + 0 == b
                        val aZeroEqA = infer(addZeroRight(a)) // a + 0 == a
                        axEqAZero.replace(aZeroEqA) // a == b
                    }
                }
            }
        }
    }

    override fun orderTotalEvidence(a: Expr, b: Expr) = proved {
        val base = forAllByGeneralization("x", Nat) { x ->
            val bZero = infer(addZeroRight(x)) // x + 0 == x
            val bZeroRevEq = infer(addCommutative(zero, x)) // 0 + x == x + 0
            val zeroX = applyMp(EqualityLibrary.transitivity, bZeroRevEq, bZero) // 0 + x == x
            val exT = zeroX.introduceExists(x, Occurences.First)
            val leqX = applyMp(leqIntroduction, exT)
            applyMp(LogicAxioms.orIntroductionLeft(auto(), x leq zero), leqX)
        }

        val step = forAllByGeneralization("k", Nat) { k ->
            assume(forall("x", Nat) { x -> (k leq x) or (x leq k) }) { forallK ->
                val subBase = run {
                    val skZero = infer(addZeroRight(succ(k))) // S(k) + 0 == S(k)
                    val skZeroRevEq = infer(addCommutative(zero, succ(k))) // 0 + S(k) == S(k) + 0
                    val zeroSK = skZeroRevEq.replace(skZero) // 0 + S(k) == S(k)
                    val exT = zeroSK.introduceExists(succ(k), Occurences.First)
                    val leqSK = applyMp(leqIntroduction, exT)
                    applyMp(LogicAxioms.orIntroductionRight(succ(k) leq zero, auto()), leqSK)
                }

                val subStep = forAllByGeneralization("m", Nat) { m ->
                    assume((succ(k) leq m) or (m leq succ(k))) { _ ->
                        val kmOr = forallK.instantiateForall(m)
                        val ifKM = assume(k leq m) { km -> // k <= m
                            val exKM = applyMp(leqElimination, km)
                            eliminateExists(exKM, "y") { y, kym -> // k + y == m
                                val skYMEq = infer(addSuccLeft(k, y)) // S(k) + y == S(k + y)
                                val skYMEqSM = skYMEq.replace(kym) // S(k) + y == S(m)
                                val exT = skYMEqSM.introduceExists(y)
                                val sksmLeq = applyMp(leqIntroduction, exT) // S(k) <= S(m)
                                applyMp(LogicAxioms.orIntroductionLeft(
                                    auto(), succ(m) leq succ(k)
                                ), sksmLeq) // S(k) <= S(m) or S(m) <= S(k)
                            }
                        }
                        val ifMK = assume(m leq k) { mk -> // m <= k
                            val exMK = applyMp(leqElimination, mk)
                            eliminateExists(exMK, "z") { z, myk -> // m + z == k
                                val skYMEq = infer(addSuccLeft(m, z)) // S(m) + z == S(m + z)
                                val skYMEqSM = skYMEq.replace(myk) // S(m) + z == S(k)
                                val exT = skYMEqSM.introduceExists(z)
                                val sksmLeq = applyMp(leqIntroduction, exT) // S(m) <= S(k)
                                applyMp(LogicAxioms.orIntroductionRight(
                                    succ(k) leq succ(m), auto()
                                ), sksmLeq) // S(k) <= S(m) or S(m) <= S(k)

                            }
                        }
                        applyMp(LogicAxioms.orElimination, ifKM, ifMK, kmOr)
                    }
                }

                applyMp(NatAxioms.induction, subBase, subStep)
            }
        }

        val forallUV = applyMp(NatAxioms.induction, base, step)
        val forallV = forallUV.instantiateForall(a)
        forallV.instantiateForall(b)
    }

    override fun addPreservesOrderRightEvidence(x: Expr, y: Expr, z: Expr) = proved {
        assume(x leq y) { leqXY ->
            val exXY = applyMp(leqElimination, leqXY) // exists k. x + k == y
            eliminateExists(exXY, "k") { k, xkyEq -> // x + k == y
                val step1 = natRing(x + z + k, (x + k) + z) // (x + z) + k = (x + k) + z
                val step2 = step1.replace(xkyEq) // (x + z) + k == y + z
                val step3 = step2.introduceExists(k)
                applyMp(leqIntroduction, step3)
            }
        }
    }

    override fun mulPreservesNonNegativeEvidence(a: Expr, b: Expr) = proved {
        val mulLeq = infer(NatLibrary.zeroLeqAll(mul(a, b))) // 0 <= a * b
        val bMulLeq = applyMp(LogicAxioms.hilbertAxiom1(auto(), zero leq b), mulLeq) // 0 <= b -> 0 <= a * b
        applyMp(LogicAxioms.hilbertAxiom1(auto(), zero leq a), bMulLeq) // 0 <= a -> 0 <= b -> 0 <= a * b
    }
}
