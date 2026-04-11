package dev.moklev.mathproof.kernel

fun StatementDefinition.prettyPrint(): String = StatementPrinter.format(this)

object StatementPrinter {
    fun format(statement: StatementDefinition): String = buildString {
        appendLine(statement.name)

        if (statement.parameters.isNotEmpty()) {
            appendLine("parameters:")
            statement.parameters.forEach { parameter ->
                appendLine("- ${parameter.name}: ${parameter.sort}")
            }
        }

        appendLine("premises:")
        if (statement.premises.isEmpty()) {
            appendLine("- none")
        } else {
            statement.premises.forEachIndexed { index, premise ->
                appendLine("${index + 1}. $premise")
            }
        }

        appendLine("conclusion: ${statement.conclusion}")

        when (val support = statement.support) {
            is AssumedTrue -> {
                append("support: assumed")
                support.note?.let { note ->
                    append(" ($note)")
                }
            }
            is ProofProvided -> {
                appendLine("proof:")
                append(renderProof(support.proof))
            }
        }
    }.trimEnd()

    fun renderProof(proof: ProofScript): String {
        val stepNumbersByLabel = proof.steps.mapIndexed { index, step -> step.label to (index + 1) }.toMap()
        return proof.steps.joinToString(separator = "\n") { step ->
            val number = requireNotNull(stepNumbersByLabel[step.label])
            "$number. ${step.claim} (${renderJustification(step.justification, stepNumbersByLabel)})"
        }
    }

    private fun renderJustification(
        justification: Justification,
        stepNumbersByLabel: Map<String, Int>,
    ): String = when (justification) {
        is PremiseReference -> "premise ${justification.premiseIndex + 1}"
        is StatementApplication -> {
            if (justification.premiseLabels.isEmpty()) {
                justification.statement.name
            } else {
                val renderedPremises = justification.premiseLabels.joinToString(", ") { label ->
                    stepNumbersByLabel[label]?.toString() ?: "?[$label]"
                }
                "${justification.statement.name} $renderedPremises"
            }
        }
        else -> justification.displayName
    }
}
