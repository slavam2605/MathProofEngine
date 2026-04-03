package dev.moklev.mathproof.fol

import dev.moklev.mathproof.kernel.ExternalJustificationStepContext
import dev.moklev.mathproof.kernel.ExternalJustificationValidator
import dev.moklev.mathproof.kernel.Fact
import dev.moklev.mathproof.kernel.Justification
import dev.moklev.mathproof.kernel.ProofBuilder
import dev.moklev.mathproof.model.Apply
import dev.moklev.mathproof.model.Bound
import dev.moklev.mathproof.model.Expr
import dev.moklev.mathproof.model.Free
import dev.moklev.mathproof.model.Lambda
import dev.moklev.mathproof.model.abstract

data class UniversalGeneralization(
    val sourceLabel: String,
    val variable: Free,
) : Justification {
    override val displayName: String = "universal-generalization"
}

object UniversalGeneralizationValidator : ExternalJustificationValidator<UniversalGeneralization> {
    override val justificationClass = UniversalGeneralization::class

    override fun validateStep(
        context: ExternalJustificationStepContext,
        justification: UniversalGeneralization,
    ): String? {
        val sourceClaim = context.provenSteps[justification.sourceLabel]
            ?: return context.failedStepMessages[justification.sourceLabel]?.let { _ ->
                "Source step '${justification.sourceLabel}' for universal generalization failed earlier."
            } ?: "Unknown source step '${justification.sourceLabel}' for universal generalization."

        if (context.statement.premises.any { premise -> premise.containsFreeSymbol(justification.variable.symbol) }) {
            return "Universal generalization over '${justification.variable.displayName}' is invalid because this variable appears in a statement premise."
        }

        val expectedClaim = try {
            val generalizedPredicate = Lambda(
                parameterSort = justification.variable.sort,
                body = sourceClaim.abstract(justification.variable),
            ).apply {
                parameterHint = justification.variable.displayName
            }
            Apply(FirstOrderFunctions.ForAll, generalizedPredicate)
        } catch (error: IllegalArgumentException) {
            return error.message ?: "Invalid quantifier application in universal generalization."
        }

        return if (context.sameProposition(expectedClaim, context.step.claim)) {
            null
        } else {
            "Universal generalization from step '${justification.sourceLabel}' expected '$expectedClaim', but got '${context.step.claim}'."
        }
    }
}

val firstOrderJustificationValidators: List<ExternalJustificationValidator<out Justification>> =
    listOf(UniversalGeneralizationValidator)

fun ProofBuilder.generalizeForAll(
    label: String,
    variable: Free,
    source: Fact,
): Fact {
    val generalizedClaim = forAllGeneralizedClaim(variable, source)
    return justify(
        label = label,
        claim = generalizedClaim,
        justification = UniversalGeneralization(
            sourceLabel = source.label,
            variable = variable,
        ),
        source,
    )
}

fun ProofBuilder.generalizeForAll(
    variable: Free,
    source: Fact,
): Fact = justify(
    claim = forAllGeneralizedClaim(variable, source),
    justification = UniversalGeneralization(
        sourceLabel = source.label,
        variable = variable,
    ),
    source,
)

private fun forAllGeneralizedClaim(variable: Free, source: Fact): Expr {
    val generalizedPredicate = Lambda(
        parameterSort = variable.sort,
        body = source.claim.abstract(variable),
    ).apply {
        parameterHint = variable.displayName
    }
    return FirstOrderFunctions.ForAll(generalizedPredicate)
}

private fun Expr.containsFreeSymbol(symbol: String): Boolean = when (this) {
    is Free -> this.symbol == symbol
    is Bound -> false
    is Lambda -> body.containsFreeSymbol(symbol)
    is Apply -> function.containsFreeSymbol(symbol) || argument.containsFreeSymbol(symbol)
}
