package dev.moklev.mathproof.kernel

import dev.moklev.mathproof.core.statement
import dev.moklev.mathproof.model.CoreSorts
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertIs
import kotlin.test.assertTrue

class ProofEvidenceDslTest {
    @Test
    fun supportsTrustedEvidenceInStatementDsl() {
        val statement = statement("proof-evidence-trusted-usage") {
            val p = parameter("p", CoreSorts.Proposition)
            conclusion(p)
            byEvidence(trusted("trusted while derived proof is pending"))
        }

        val support = assertIs<AssumedTrue>(statement.support)
        assertEquals("trusted while derived proof is pending", support.note)
    }

    @Test
    fun supportsDerivedEvidenceInStatementDsl() {
        val statement = statement("proof-evidence-derived-usage") {
            val p = parameter("p", CoreSorts.Proposition)
            val pPremise = premise(p)
            conclusion(p)
            byEvidence(
                proved {
                    given(pPremise)
                },
            )
        }

        assertIs<ProofProvided>(statement.support)
        val verification = ProofVerifier().verify(statement)
        assertTrue(verification.isValid, verification.describeIssues())
    }
}
