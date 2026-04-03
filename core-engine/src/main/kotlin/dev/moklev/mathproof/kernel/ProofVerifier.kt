package dev.moklev.mathproof.kernel

import dev.moklev.mathproof.model.Expr
import dev.moklev.mathproof.model.CoreSorts
import dev.moklev.mathproof.model.betaNormalize
import dev.moklev.mathproof.model.isResolvedForVerification
import dev.moklev.mathproof.model.validationIssues

class ProofVerifier(
    private val externalJustificationValidators: List<ExternalJustificationValidator<out Justification>> = emptyList(),
) {
    private val verificationCache = mutableMapOf<StatementDefinition, VerificationResult>()
    private val verificationStack = mutableSetOf<StatementDefinition>()
    private val normalizedExprCache = mutableMapOf<Expr, Expr>()

    fun verify(statement: StatementDefinition): VerificationResult {
        verificationCache[statement]?.let { return it }

        if (!verificationStack.add(statement)) {
            return VerificationResult(
                statement = statement,
                issues = listOf(
                    VerificationIssue(
                        stepIndex = null,
                        stepLabel = null,
                        message = "Recursive statement verification detected for '${statement.name}'.",
                    ),
                ),
            )
        }

        try {
            val structureIssues = validateStatementStructure(statement)
            val proofIssues = when (val support = statement.support) {
                is AssumedTrue -> emptyList()
                is ProofProvided -> verifyProof(
                    statement = statement,
                    proof = support.proof,
                ).issues
            }
            val result = VerificationResult(statement, structureIssues + proofIssues)

            verificationCache[statement] = result
            return result
        } finally {
            verificationStack.remove(statement)
        }
    }

    private fun validateStatementStructure(statement: StatementDefinition): List<VerificationIssue> {
        val issues = mutableListOf<VerificationIssue>()

        val seenParameterNames = mutableSetOf<String>()
        statement.parameters.forEach { parameter ->
            if (!seenParameterNames.add(parameter.name)) {
                issues += VerificationIssue(
                    stepIndex = null,
                    stepLabel = null,
                    message = "Parameter '${parameter.name}' is declared more than once in '${statement.name}'.",
                )
            }
            if (!parameter.sort.isResolvedForVerification()) {
                issues += VerificationIssue(
                    stepIndex = null,
                    stepLabel = null,
                    message = "Parameter '${parameter.name}' in '${statement.name}' has unresolved sort '${parameter.sort}'.",
                )
            }
        }

        statement.premises.forEachIndexed { index, premise ->
            if (premise.sort != CoreSorts.Proposition) {
                issues += VerificationIssue(
                    stepIndex = null,
                    stepLabel = null,
                    message = "Premise ${index + 1} in '${statement.name}' must have sort '${CoreSorts.Proposition}', but got '${premise.sort}'.",
                )
            }
            premise.validationIssues("statement '${statement.name}' premise ${index + 1}")
                .forEach { message ->
                    issues += VerificationIssue(null, null, message)
                }
        }

        if (statement.conclusion.sort != CoreSorts.Proposition) {
            issues += VerificationIssue(
                stepIndex = null,
                stepLabel = null,
                message = "Conclusion of '${statement.name}' must have sort '${CoreSorts.Proposition}', but got '${statement.conclusion.sort}'.",
            )
        }
        statement.conclusion.validationIssues("statement '${statement.name}' conclusion")
            .forEach { message ->
                issues += VerificationIssue(null, null, message)
            }

        val proof = (statement.support as? ProofProvided)?.proof ?: return issues
        val seenLabels = mutableSetOf<String>()
        proof.steps.forEachIndexed { index, step ->
            if (!seenLabels.add(step.label)) {
                issues += VerificationIssue(
                    stepIndex = index + 1,
                    stepLabel = step.label,
                    message = "Duplicate proof step label '${step.label}'.",
                )
            }
            if (step.claim.sort != CoreSorts.Proposition) {
                issues += VerificationIssue(
                    stepIndex = index + 1,
                    stepLabel = step.label,
                    message = "Proof step '${step.label}' must prove a proposition, but got '${step.claim.sort}'.",
                )
            }
            step.claim.validationIssues("proof step '${step.label}'")
                .forEach { message ->
                    issues += VerificationIssue(index + 1, step.label, message)
                }
            when (val justification = step.justification) {
                is PremiseReference -> {
                    if (justification.premiseIndex !in statement.premises.indices) {
                        issues += VerificationIssue(
                            stepIndex = index + 1,
                            stepLabel = step.label,
                            message = "Premise reference ${justification.premiseIndex + 1} does not exist in '${statement.name}'.",
                        )
                    }
                }
                is StatementApplication -> {
                    justification.arguments.forEachIndexed { argumentIndex, argument ->
                        argument.validationIssues(
                            "argument ${argumentIndex + 1} to statement '${justification.statement.name}'",
                        ).forEach { message ->
                            issues += VerificationIssue(index + 1, step.label, message)
                        }
                    }
                }
                else -> {
                    val validator = externalValidatorFor(justification)
                    if (validator == null) {
                        issues += VerificationIssue(
                            stepIndex = index + 1,
                            stepLabel = step.label,
                            message = "No verifier extension registered for justification '${justification.displayName}'.",
                        )
                    } else {
                        val context = ExternalJustificationStructureContext(
                            statement = statement,
                            step = step,
                            stepIndex = index + 1,
                        )
                        validator.validateStructure(context, justification)
                            .forEach { message ->
                                issues += VerificationIssue(index + 1, step.label, message)
                            }
                    }
                }
            }
        }

        return issues
    }

    private fun verifyProof(
        statement: StatementDefinition,
        proof: ProofScript,
    ): VerificationResult {
        val provenSteps = linkedMapOf<String, Expr>()
        val failedStepMessages = linkedMapOf<String, String>()
        val issues = mutableListOf<VerificationIssue>()

        proof.steps.forEachIndexed { index, step ->
            val issue = validateStep(step, provenSteps, failedStepMessages, statement)
            if (issue == null) {
                provenSteps[step.label] = step.claim
            } else {
                failedStepMessages.putIfAbsent(step.label, issue)
                issues += VerificationIssue(
                    stepIndex = index + 1,
                    stepLabel = step.label,
                    message = issue,
                )
            }
        }

        val lastClaim = proof.steps.lastOrNull()?.claim
        if (lastClaim == null) {
            issues += VerificationIssue(
                stepIndex = null,
                stepLabel = null,
                message = "Proof is empty.",
            )
        } else if (issues.isEmpty() && !sameProposition(lastClaim, statement.conclusion)) {
            issues += VerificationIssue(
                stepIndex = proof.steps.size,
                stepLabel = proof.steps.last().label,
                message = "Last step proves '$lastClaim', but statement conclusion is '${statement.conclusion}'.",
            )
        }

        return VerificationResult(statement, issues)
    }

    private fun validateStep(
        step: ProofStep,
        provenSteps: Map<String, Expr>,
        failedStepMessages: Map<String, String>,
        statement: StatementDefinition,
    ): String? = when (val justification = step.justification) {
        is PremiseReference -> validatePremiseReference(step, statement, justification)
        is StatementApplication -> validateStatementApplication(step, provenSteps, failedStepMessages, justification)
        else -> validateExternalJustification(step, statement, provenSteps, failedStepMessages, justification)
    }

    private fun validatePremiseReference(
        step: ProofStep,
        statement: StatementDefinition,
        justification: PremiseReference,
    ): String? {
        val premise = statement.premises.getOrNull(justification.premiseIndex)
            ?: return "Premise reference ${justification.premiseIndex + 1} does not exist in '${statement.name}'."

        return if (sameProposition(premise, step.claim)) {
            null
        } else {
            "Premise reference ${justification.premiseIndex + 1} in '${statement.name}' proves '$premise', not '${step.claim}'."
        }
    }

    private fun validateStatementApplication(
        step: ProofStep,
        provenSteps: Map<String, Expr>,
        failedStepMessages: Map<String, String>,
        justification: StatementApplication,
    ): String? {
        val statement = justification.statement
        val supportResult = verify(statement)
        if (!supportResult.isValid) {
            val firstIssue = supportResult.issues.firstOrNull()
            val details = firstIssue?.let { " First issue: $it" } ?: ""
            return "Statement '${statement.name}' is not verified and cannot be used yet.$details"
        }

        val statementCall = try {
            statement.instantiate(justification.arguments)
        } catch (error: IllegalArgumentException) {
            return error.message ?: "Invalid application of statement '${statement.name}'."
        }

        if (statementCall.premises.size != justification.premiseLabels.size) {
            return "Statement '${statement.name}' expects ${statementCall.premises.size} premise steps, but got ${justification.premiseLabels.size}."
        }

        justification.premiseLabels.zip(statementCall.premises).forEachIndexed { index, (label, expectedPremise) ->
            val actualPremise = provenSteps[label]
                ?: return failedStepMessages[label]?.let { _ ->
                    "Premise step '$label' for statement '${statement.name}' failed earlier."
                } ?: "Unknown premise step '$label' for statement '${statement.name}'."
            if (!sameProposition(actualPremise, expectedPremise)) {
                return "Premise ${index + 1} for statement '${statement.name}' expected '$expectedPremise', but step '$label' proves '$actualPremise'."
            }
        }

        return if (sameProposition(statementCall.conclusion, step.claim)) {
            null
        } else {
            "Statement '${statement.name}' concludes '${statementCall.conclusion}', not '${step.claim}'."
        }
    }

    private fun validateExternalJustification(
        step: ProofStep,
        statement: StatementDefinition,
        provenSteps: Map<String, Expr>,
        failedStepMessages: Map<String, String>,
        justification: Justification,
    ): String? {
        val validator = externalValidatorFor(justification)
            ?: return "No verifier extension registered for justification '${justification.displayName}'."
        val context = ExternalJustificationStepContext(
            statement = statement,
            step = step,
            provenSteps = provenSteps,
            failedStepMessages = failedStepMessages,
            sameProposition = ::sameProposition,
        )
        return validator.validateStep(context, justification)
    }

    @Suppress("UNCHECKED_CAST")
    private fun <J : Justification> externalValidatorFor(
        justification: J,
    ): ExternalJustificationValidator<J>? =
        externalJustificationValidators.firstOrNull { validator ->
            validator.justificationClass.isInstance(justification)
        } as ExternalJustificationValidator<J>?

    private fun sameProposition(left: Expr, right: Expr): Boolean =
        normalized(left) == normalized(right)

    private fun normalized(expr: Expr): Expr =
        normalizedExprCache.getOrPut(expr) { expr.betaNormalize() }
}

data class VerificationResult(
    val statement: StatementDefinition,
    val issues: List<VerificationIssue>,
) {
    val isValid: Boolean
        get() = issues.isEmpty()

    fun describeIssues(): String = if (issues.isEmpty()) {
        "Verification of '${statement.name}' succeeded."
    } else {
        buildString {
            append("Verification of '${statement.name}' failed with ")
            append(issues.size)
            append(" issue")
            if (issues.size != 1) {
                append("s")
            }
            append(":")
            issues.forEach { issue ->
                append("\n- ")
                append(issue)
            }
        }
    }
}

data class VerificationIssue(
    val stepIndex: Int?,
    val stepLabel: String?,
    val message: String,
) {
    override fun toString(): String = buildString {
        if (stepIndex != null) {
            append("step ")
            append(stepIndex)
        } else {
            append("statement")
        }
        if (stepLabel != null) {
            append(" [")
            append(stepLabel)
            append("]")
        }
        append(": ")
        append(message)
    }
}
