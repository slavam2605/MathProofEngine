package dev.moklev.mathproof.kernel

sealed interface ProofEvidence {
    data class Derived(val build: ProofBuilder.() -> Unit) : ProofEvidence

    data class Trusted(val note: String? = null) : ProofEvidence
}

fun proved(block: ProofBuilder.() -> Unit): ProofEvidence = ProofEvidence.Derived(block)

fun trusted(note: String? = null): ProofEvidence = ProofEvidence.Trusted(note)

fun StatementBuilder.byEvidence(evidence: ProofEvidence) {
    when (evidence) {
        is ProofEvidence.Derived -> proof(evidence.build)
        is ProofEvidence.Trusted -> assumed(evidence.note)
    }
}
