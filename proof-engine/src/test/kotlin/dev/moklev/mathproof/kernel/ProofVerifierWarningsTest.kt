package dev.moklev.mathproof.kernel

import dev.moklev.mathproof.core.constant
import dev.moklev.mathproof.core.statement
import dev.moklev.mathproof.model.CoreSorts
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertTrue

class ProofVerifierWarningsTest {
    @Test
    fun allowsTodoAssumeAndReportsWarning() {
        val p = constant("p", CoreSorts.Proposition)
        val nonStrictVerifier = ProofVerifier(failOnWarnings = false)

        val statement = statement("todo-assume-warning") {
            conclusion(p)
            proof {
                todoAssume(p, note = "temporary gap for experimentation")
            }
        }

        val result = nonStrictVerifier.verify(statement)

        assertTrue(result.isValid, result.describeIssues())
        assertEquals(1, result.warnings.size)
        assertTrue(result.warnings.single().message.contains("TODO assumption used"))
        assertTrue(result.warnings.single().message.contains("temporary gap"))
    }

    @Test
    fun propagatesTodoAssumeWarningsThroughStatementApplications() {
        val p = constant("p", CoreSorts.Proposition)
        val nonStrictVerifier = ProofVerifier(failOnWarnings = false)

        val helper = statement("todo-assume-helper") {
            conclusion(p)
            proof {
                todoAssume(p, note = "helper proof pending")
            }
        }

        val consumer = statement("todo-assume-consumer") {
            conclusion(p)
            proof {
                infer(helper())
            }
        }

        val result = nonStrictVerifier.verify(consumer)

        assertTrue(result.isValid, result.describeIssues())
        assertTrue(result.warnings.any { warning -> warning.message.contains("todo-assume-helper") })
        assertTrue(result.warnings.any { warning -> warning.message.contains("warning") })
    }

    @Test
    fun strictModeTreatsWarningsAsVerificationFailures() {
        val p = constant("p", CoreSorts.Proposition)
        val strictVerifier = ProofVerifier(failOnWarnings = true)

        val statement = statement("todo-assume-strict-failure") {
            conclusion(p)
            proof {
                todoAssume(p, note = "strict mode should reject this")
            }
        }

        val result = strictVerifier.verify(statement)

        assertFalse(result.isValid)
        assertTrue(result.warnings.isNotEmpty())
        assertTrue(result.issues.any { issue -> issue.message.contains("Strict mode rejects warning") })
    }
}
