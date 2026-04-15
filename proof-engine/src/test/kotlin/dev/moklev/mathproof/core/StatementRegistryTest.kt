package dev.moklev.mathproof.core

import dev.moklev.mathproof.model.CoreSorts
import kotlin.test.Test
import kotlin.test.assertFailsWith
import kotlin.test.assertSame
import kotlin.test.assertTrue

class StatementRegistryTest {
    @Test
    fun statementRegistrationRejectsDuplicateNames() {
        val name = "registry-test-duplicate-statement-name"

        statement(name) {
            val p = parameter("p", CoreSorts.Proposition)
            conclusion(p)
            assumed("first declaration")
        }

        val error = assertFailsWith<IllegalArgumentException> {
            statement(name) {
                val p = parameter("p", CoreSorts.Proposition)
                conclusion(p)
                assumed("second declaration")
            }
        }
        assertTrue(error.message!!.contains("already registered"))
    }

    @Test
    fun cachedStatementReturnsFirstRegisteredInstance() {
        val name = "registry-test-cached-statement"

        val first = registry.cachedStatement(name) {
            val p = parameter("p", CoreSorts.Proposition)
            conclusion(p)
            assumed("cached")
        }

        val second = registry.cachedStatement(name) {
            error("cachedStatement should not execute builder when name is already cached.")
        }

        assertSame(first, second)
    }
}
