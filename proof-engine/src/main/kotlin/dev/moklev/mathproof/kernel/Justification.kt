package dev.moklev.mathproof.kernel

import dev.moklev.mathproof.model.Expr
import kotlin.reflect.KClass

interface Justification {
    val displayName: String
        get() = this::class.simpleName ?: this::class.qualifiedName ?: "custom-justification"
}

data class PremiseReference(val premiseIndex: Int) : Justification

data class StatementApplication(
    val statement: StatementDefinition,
    val arguments: List<Expr>,
    val premiseLabels: List<String>,
) : Justification

data class TodoAssumption(
    val note: String? = null,
) : Justification {
    override val displayName: String = "todo-assume"
}

interface ExternalJustificationValidator<J : Justification> {
    val justificationClass: KClass<J>

    fun validateStructure(
        context: ExternalJustificationStructureContext,
        justification: J,
    ): List<String> = emptyList()

    fun validateStep(
        context: ExternalJustificationStepContext,
        justification: J,
    ): String?
}

data class ExternalJustificationStructureContext(
    val statement: StatementDefinition,
    val proof: ProofScript,
    val step: ProofStep,
    val stepIndex: Int,
)

data class ExternalJustificationStepContext(
    val statement: StatementDefinition,
    val proof: ProofScript,
    val step: ProofStep,
    val provenSteps: Map<String, Expr>,
    val failedStepMessages: Map<String, String>,
    val sameProposition: (Expr, Expr) -> Boolean,
)
