package dev.moklev.mathproof

import dev.moklev.mathproof.core.functionSort
import dev.moklev.mathproof.core.lambda
import dev.moklev.mathproof.model.Expr
import dev.moklev.mathproof.model.NamedSort
import dev.moklev.mathproof.model.Sort
import dev.moklev.mathproof.model.betaNormalize
import kotlin.test.Test
import kotlin.test.assertEquals

class ChurchNumeralsTest {
    private val scalar = NamedSort("Scalar")
    private val unaryScalar = functionSort(scalar, returns = scalar)

    @Test
    fun churchAddition() {
        val churchA = churchNumber(123, scalar)
        val churchB = churchNumber(321, scalar)

        val expression = lambda("f", unaryScalar) { f ->
            lambda("x", scalar) { x ->
                churchA(f)(churchB(f)(x))
            }
        }
        val normalized = expression.betaNormalize()

        val expected = churchNumber(444, scalar)
        assertEquals(expected, normalized)
    }

    @Test
    fun churchMultiplication() {
        val churchA = churchNumber(51, scalar)
        val churchB = churchNumber(32, scalar)

        val expression = lambda("f", unaryScalar) { f ->
            lambda("x", scalar) { x ->
                churchA(churchB(f))(x)
            }
        }
        val normalized = expression.betaNormalize()

        val expected = churchNumber(1632, scalar)
        assertEquals(expected, normalized)
    }

    @Test
    fun churchExponentiation() {
        val churchA = churchNumber(5, unaryScalar)
        val churchB = churchNumber(5, scalar)

        val expression = churchA(churchB)
        val normalized = expression.betaNormalize()

        val expected = churchNumber(3125, scalar)
        assertEquals(expected, normalized)
    }

    private fun churchNumber(n: Int, baseSort: Sort): Expr {
        check(n >= 0)
        val fSort = functionSort(baseSort, returns = baseSort)

        return lambda("f", fSort) { f ->
            lambda("x", baseSort) { x ->
                (0 until n).fold(x) { acc, _ -> f(acc) }
            }
        }
    }
}