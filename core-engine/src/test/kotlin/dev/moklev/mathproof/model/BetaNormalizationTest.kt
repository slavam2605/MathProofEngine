package dev.moklev.mathproof.model

import dev.moklev.mathproof.core.constant
import dev.moklev.mathproof.core.function
import dev.moklev.mathproof.core.functionSort
import dev.moklev.mathproof.core.lambda
import kotlin.test.Test
import kotlin.test.assertEquals

class BetaNormalizationTest {
    private val scalar = NamedSort("Scalar")
    private val unaryScalar = functionSort(scalar, returns = scalar)

    @Test
    fun reducesIdentityApplication() {
        val id = lambda("x", scalar) { x -> x }
        val a = constant("a", scalar)

        assertEquals(a, id(a).betaNormalize())
    }

    @Test
    fun reducesNestedApplicationsToNormalForm() {
        val a = constant("a", scalar)
        val b = constant("b", scalar)
        val expression = lambda("x", scalar) { x ->
            lambda("y", scalar) { _ -> x }
        }(a)(b)

        assertEquals(a, expression.betaNormalize())
    }

    @Test
    fun avoidsVariableCaptureDuringBetaReduction() {
        val yFree = constant("y", scalar)
        val argument = lambda("z", scalar) { _ -> yFree }
        val expression = lambda("x", unaryScalar) { x ->
            lambda("y", scalar) { y -> x(y) }
        }(argument)
        val expected = lambda("y", scalar) { _ -> yFree }

        assertEquals(expected, expression.betaNormalize())
    }

    @Test
    fun normalizesArgumentsWhenFunctionHeadIsNotALambda() {
        val f = function("f", scalar, returns = scalar)
        val a = constant("a", scalar)
        val argumentRedex = lambda("x", scalar) { x -> x }(a)

        assertEquals(f(a), f(argumentRedex).betaNormalize())
    }

    @Test
    fun normalizationIsIdempotent() {
        val yFree = constant("y", scalar)
        val expression = lambda("x", unaryScalar) { x ->
            lambda("y", scalar) { y -> x(y) }
        }(lambda("z", scalar) { _ -> yFree })

        val normalizedOnce = expression.betaNormalize()
        assertEquals(normalizedOnce, normalizedOnce.betaNormalize())
    }
}
