package dev.moklev.mathproof.kernel

import dev.moklev.mathproof.core.constant
import dev.moklev.mathproof.core.function
import dev.moklev.mathproof.core.functionSort
import dev.moklev.mathproof.core.lambda
import dev.moklev.mathproof.core.statement
import dev.moklev.mathproof.model.Expr
import dev.moklev.mathproof.model.CoreSorts
import dev.moklev.mathproof.model.NamedSort
import dev.moklev.mathproof.model.betaNormalize
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFailsWith
import kotlin.test.assertTrue

class StatementArgumentInferenceTest {
    private val elementSort = NamedSort("Elem")
    private val eq = function("eq", elementSort, elementSort, returns = CoreSorts.Proposition)
    private val p = function("P", elementSort, returns = CoreSorts.Proposition)
    private val q = function("Q", elementSort, returns = CoreSorts.Proposition)
    private val implies = function("imp", CoreSorts.Proposition, CoreSorts.Proposition, returns = CoreSorts.Proposition)
    private val zero = constant("0", elementSort)
    private val succ = function("S", elementSort, returns = elementSort)
    private val all = function("all", functionSort(elementSort, returns = CoreSorts.Proposition), returns = CoreSorts.Proposition)
    private val r = function("R", elementSort, elementSort, returns = CoreSorts.Proposition)

    @Test
    fun infersStatementArgumentsFromPremises() {
        val theorem = statement("flip-equality") {
            val x = parameter("x", elementSort)
            val y = parameter("y", elementSort)
            premise(eq(x, y))
            conclusion(eq(y, x))
            assumed()
        }

        val a = constant("a", elementSort)
        val b = constant("b", elementSort)
        val inferred = theorem.autoCall().resolveFromPremises(listOf(eq(a, b)))

        assertEquals(listOf(a, b), inferred.arguments)
        assertEquals(eq(b, a), inferred.conclusion)
    }

    @Test
    fun failsWhenInferenceIsUnderconstrained() {
        val theorem = statement("underconstrained") {
            val x = parameter("x", elementSort)
            val y = parameter("y", elementSort)
            premise(p(x))
            conclusion(q(y))
            assumed()
        }

        val a = constant("a", elementSort)
        val error = assertFailsWith<IllegalArgumentException> {
            theorem.autoCall().resolveFromPremises(listOf(p(a)))
        }

        assertTrue(error.message!!.contains("unresolved parameter"))
        assertTrue(error.message!!.contains("y"))
    }

    @Test
    fun failsWhenParameterMatchesConflict() {
        val theorem = statement("conflicting-parameter") {
            val x = parameter("x", elementSort)
            premise(p(x))
            premise(q(x))
            conclusion(p(x))
            assumed()
        }

        val a = constant("a", elementSort)
        val b = constant("b", elementSort)
        val error = assertFailsWith<IllegalArgumentException> {
            theorem.autoCall().resolveFromPremises(listOf(p(a), q(b)))
        }

        assertTrue(error.message!!.contains("conflicting matches"))
        assertTrue(error.message!!.contains("x"))
    }

    @Test
    fun infersRemainingParametersFromPremisesWithProvidedArgs() {
        val theorem = statement("need-explicit-middle-arg") {
            val f = parameter("f", functionSort(elementSort, returns = elementSort))
            val x = parameter("x", elementSort)
            val y = parameter("y", elementSort)
            premise(eq(x, y))
            conclusion(eq(f(x), f(y)))
            assumed()
        }

        val funF = function("f", elementSort, returns = elementSort)
        val a = constant("a", elementSort)
        val b = constant("b", elementSort)

        val inferred = theorem(funF, auto(), auto()).resolveFromPremises(listOf(eq(a, b)))

        assertEquals(listOf(funF, a, b), inferred.arguments)
        assertEquals(eq(funF(a), funF(b)), inferred.conclusion)
    }

    @Test
    fun rejectsPartiallySpecifiedCallWhenExplicitArgumentConflicts() {
        val theorem = statement("arg-conflict-validation") {
            val x = parameter("x", elementSort)
            val y = parameter("y", elementSort)
            premise(p(x))
            conclusion(p(y))
            assumed()
        }

        val a = constant("a", elementSort)
        val b = constant("b", elementSort)
        val error = assertFailsWith<IllegalArgumentException> {
            theorem(a, auto()).resolveFromPremises(listOf(p(b)))
        }

        assertTrue(error.message!!.contains("expression mismatch"))
    }

    @Test
    fun synthesizesHigherOrderPredicateFromApplicationConstraints() {
        val inductionLike = statement("induction-like") {
            val predicate = parameter("predicate", functionSort(elementSort, returns = CoreSorts.Proposition))
            premise(predicate(zero))
            premise(
                all(
                    lambda("n", elementSort) { n ->
                        predicate(n) implies predicate(succ(n))
                    }
                )
            )
            conclusion(all(predicate))
            assumed()
        }

        val base = all(
            lambda("v", elementSort) { v ->
                r(zero, v)
            }
        )
        val step = all(
            lambda("n", elementSort) { n ->
                all(
                    lambda("v", elementSort) { v ->
                        r(n, v)
                    }
                ) implies all(
                    lambda("v", elementSort) { v ->
                        r(succ(n), v)
                    }
                )
            }
        )

        val inferred = inductionLike.autoCall().resolveFromPremises(listOf(base, step))
        val expectedPredicate = lambda("u", elementSort) { u ->
            all(
                lambda("v", elementSort) { v ->
                    r(u, v)
                }
            )
        }

        assertEquals(expectedPredicate.betaNormalize(), inferred.arguments.single().betaNormalize())
        assertEquals(all(expectedPredicate).betaNormalize(), inferred.conclusion.betaNormalize())
    }

    @Test
    fun synthesizesHigherOrderPredicateUsingBoundSeedWhenBaseIsNotSpecificEnough() {
        val inductionLike = statement("induction-like-bound-seed") {
            val predicate = parameter("predicate", functionSort(elementSort, returns = CoreSorts.Proposition))
            premise(predicate(zero))
            premise(
                all(
                    lambda("n", elementSort) { n ->
                        predicate(n) implies predicate(succ(n))
                    }
                )
            )
            conclusion(all(predicate))
            assumed()
        }

        val mul = function("*", elementSort, elementSort, returns = elementSort)
        val base = eq(mul(zero, zero), zero)
        val step = all(
            lambda("n", elementSort) { n ->
                eq(mul(zero, n), zero) implies eq(mul(zero, succ(n)), zero)
            }
        )

        val inferred = inductionLike.autoCall().resolveFromPremises(listOf(base, step))
        val expectedPredicate = lambda("u", elementSort) { u ->
            eq(mul(zero, u), zero)
        }

        assertEquals(expectedPredicate.betaNormalize(), inferred.arguments.single().betaNormalize())
        assertEquals(all(expectedPredicate).betaNormalize(), inferred.conclusion.betaNormalize())
    }

    private infix fun Expr.implies(other: Expr): Expr = implies(this, other)
}
