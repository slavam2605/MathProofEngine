package dev.moklev.mathproof.core

import dev.moklev.mathproof.kernel.AssumedTrue
import dev.moklev.mathproof.model.Associativity
import dev.moklev.mathproof.model.CoreSorts
import dev.moklev.mathproof.model.ExprNotation
import dev.moklev.mathproof.model.ExprPrecedence
import dev.moklev.mathproof.model.NamedSort
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFailsWith
import kotlin.test.assertIs
import kotlin.test.assertTrue

class SymbolDefinitionsTest {
    @Test
    fun buildsCanonicalIdsFromNestedNamespaces() {
        val scalar = NamedSort("Scalar")
        val symbol = global
            .namespace("tests")
            .namespace("symbolDefs")
            .namespace("nested")
            .function("foo", scalar, returns = scalar)

        assertEquals("tests.symbolDefs.nested.foo", symbol.symbol)
        assertEquals("foo", symbol.displayName)
    }

    @Test
    fun rejectsDuplicateRegistrationEvenForSameSort() {
        val scalar = NamedSort("Scalar")
        val namespace = global.namespace("tests").namespace("symbolDefs").namespace("duplicates")
        namespace.constant("x", scalar)

        val error = assertFailsWith<IllegalArgumentException> {
            namespace.constant("x", scalar)
        }
        assertTrue(error.message!!.contains("already registered"))
    }

    @Test
    fun defineFunctionAutoRegistersNamedAxiomsAsAssumedStatements() {
        val namespace = global.namespace("tests").namespace("symbolDefs").namespace("functionAxioms")
        val definition = namespace.defineFunction(
            "identityish",
            CoreSorts.Proposition,
            returns = CoreSorts.Proposition,
        ) { self ->
            axiom("at-parameter") {
                val p = parameter("p", CoreSorts.Proposition)
                conclusion(self(p))
            }
        }

        val declaredAxiom = definition.axiom("at-parameter")
        assertEquals(1, definition.allAxioms.size)
        assertEquals("def.tests.symbolDefs.functionAxioms.identityish.at-parameter", declaredAxiom.name)
        assertIs<AssumedTrue>(declaredAxiom.support)
    }

    @Test
    fun functionNotationOverloadUsesNotationSymbolAndRegistersRendering() {
        val scalar = NamedSort("Scalar")
        val namespace = global.namespace("tests").namespace("symbolDefs").namespace("notationFunction")
        val exp = namespace.function(
            "exp",
            scalar, scalar,
            returns = scalar,
            notation = ExprNotation.Infix(
                "^",
                precedence = ExprPrecedence.EXPONENT,
                associativity = Associativity.RIGHT,
            ),
        )

        assertEquals("^", exp.displayName)
        val a = constant("a", scalar)
        val b = constant("b", scalar)
        assertEquals("a ^ b", exp(a, b).toString())
    }

    @Test
    fun infixNotationCanRenderWithoutSurroundingSpaces() {
        val scalar = NamedSort("Scalar")
        val namespace = global.namespace("tests").namespace("symbolDefs").namespace("tightInfix")
        val add = namespace.function(
            "add",
            scalar, scalar,
            returns = scalar,
            notation = ExprNotation.Infix("+", precedence = ExprPrecedence.ADDITIVE),
        )
        val exp = namespace.function(
            "exp",
            scalar, scalar,
            returns = scalar,
            notation = ExprNotation.Infix(
                "^",
                precedence = ExprPrecedence.EXPONENT,
                associativity = Associativity.RIGHT,
                surroundWithSpaces = false,
            ),
        )

        val a = constant("a", scalar)
        val b = constant("b", scalar)
        val c = constant("c", scalar)

        assertEquals("a^b", exp(a, b).toString())
        assertEquals("a^(b + c)", exp(a, add(b, c)).toString())
    }

    @Test
    fun defineFunctionNotationOverloadUsesNotationSymbol() {
        val namespace = global.namespace("tests").namespace("symbolDefs").namespace("notationDefinition")
        val definition = namespace.defineFunction(
            "notx",
            CoreSorts.Proposition,
            returns = CoreSorts.Proposition,
            notation = ExprNotation.Prefix("!", precedence = ExprPrecedence.PREFIX),
        ) { self ->
            axiom("at-parameter") {
                val p = parameter("p", CoreSorts.Proposition)
                conclusion(self(p))
            }
        }

        assertEquals("!", definition.symbol.displayName)
        val p = constant("p", CoreSorts.Proposition)
        assertEquals("!p", definition.symbol(p).toString())
    }
}
