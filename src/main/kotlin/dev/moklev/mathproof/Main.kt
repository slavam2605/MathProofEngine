package dev.moklev.mathproof

import dev.moklev.mathproof.examples.SampleProofs
import dev.moklev.mathproof.kernel.ProofVerifier
import dev.moklev.mathproof.kernel.prettyPrint

fun main() {
    val verifier = ProofVerifier()

    SampleProofs.all.forEach { statement ->
        val result = verifier.verify(statement)
        val status = if (result.isValid) "verified" else "failed"

        println("${statement.name}: $status")
        println(statement.prettyPrint())
        if (!result.isValid) {
            result.issues.forEach { println("  issue: $it") }
        }
        println()
    }
}
