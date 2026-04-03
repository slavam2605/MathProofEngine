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
import dev.moklev.mathproof.model.Sort
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
        val declaredArbitrary = context.proof.arbitraryVariables.firstOrNull { variable ->
            variable.symbol == justification.variable.symbol
        } ?: return invalidGeneralizationOriginMessage(context, justification.variable)
        if (declaredArbitrary.sort != justification.variable.sort) {
            return "Universal generalization over '${justification.variable.displayName}' is invalid: proof declares symbol '${justification.variable.symbol}' as sort '${declaredArbitrary.sort}', but justification uses sort '${justification.variable.sort}'."
        }

        val sourceClaim = context.provenSteps[justification.sourceLabel]
            ?: return context.failedStepMessages[justification.sourceLabel]?.let { _ ->
                "Source step '${justification.sourceLabel}' for universal generalization failed earlier."
            } ?: "Unknown source step '${justification.sourceLabel}' for universal generalization."

        if (context.statement.premises.any { premise -> premise.containsFreeSymbol(justification.variable.symbol) }) {
            return "Universal generalization over '${justification.variable.displayName}' is invalid because this variable appears in a statement premise."
        }

        val claimedPredicate = context.step.claim.forAllPredicateOrNull()
        if (claimedPredicate != null && claimedPredicate.parameterSort != justification.variable.sort) {
            return "Universal generalization over '${justification.variable.displayName}' is invalid: quantified binder sort '${claimedPredicate.parameterSort}' does not match variable sort '${justification.variable.sort}'."
        }

        val expectedClaim = try {
            forAllGeneralizedClaim(justification.variable, sourceClaim)
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

fun ProofBuilder.forAllByGeneralization(
    variableName: String,
    sort: Sort,
    proveAt: (Free) -> Fact,
): Fact {
    val variable = arbitrary(variableName, sort)
    val source = proveAt(variable)
    return generalizeForAll(variable, source)
}

fun ProofBuilder.forAllByGeneralization(
    label: String,
    variableName: String,
    sort: Sort,
    proveAt: (Free) -> Fact,
): Fact {
    val variable = arbitrary(variableName, sort)
    val source = proveAt(variable)
    return generalizeForAll(label, variable, source)
}

private fun forAllGeneralizedClaim(variable: Free, source: Fact): Expr {
    return forAllGeneralizedClaim(variable, source.claim)
}

private fun forAllGeneralizedClaim(variable: Free, sourceClaim: Expr): Expr {
    val generalizedPredicate = Lambda(
        parameterSort = variable.sort,
        body = sourceClaim.abstract(variable),
    ).apply {
        parameterHint = variable.displayName
    }
    return FirstOrderFunctions.ForAll(generalizedPredicate)
}

private fun invalidGeneralizationOriginMessage(
    context: ExternalJustificationStepContext,
    variable: Free,
): String {
    val statementParameterName = context.statement.parameterNameForSymbol(variable.symbol)
    val origin = if (statementParameterName != null) {
        "statement parameter '$statementParameterName'"
    } else {
        "constant/untracked symbol"
    }

    return "Universal generalization over '${variable.displayName}' is invalid: symbol '${variable.symbol}' comes from $origin. Only proof-local arbitrary variables declared with arbitrary(name, sort) may be generalized."
}

private fun Expr.forAllPredicateOrNull(): Lambda? {
    val quantified = this as? Apply ?: return null
    if (quantified.function != FirstOrderFunctions.ForAll) {
        return null
    }
    return quantified.argument as? Lambda
}

private fun Expr.containsFreeSymbol(symbol: String): Boolean = when (this) {
    is Free -> this.symbol == symbol
    is Bound -> false
    is Lambda -> body.containsFreeSymbol(symbol)
    is Apply -> function.containsFreeSymbol(symbol) || argument.containsFreeSymbol(symbol)
}
