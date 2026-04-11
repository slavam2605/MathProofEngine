package dev.moklev.mathproof.core

import dev.moklev.mathproof.kernel.AssumedTrue
import dev.moklev.mathproof.model.CoreSorts
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
}
