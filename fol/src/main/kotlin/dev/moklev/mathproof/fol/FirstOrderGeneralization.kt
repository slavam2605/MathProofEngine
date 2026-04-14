package dev.moklev.mathproof.fol

import dev.moklev.mathproof.kernel.ExternalJustificationStepContext
import dev.moklev.mathproof.kernel.ExternalJustificationValidator
import dev.moklev.mathproof.kernel.DerivationFact
import dev.moklev.mathproof.kernel.DerivationScope
import dev.moklev.mathproof.kernel.Justification
import dev.moklev.mathproof.logic.LogicAxioms.modusPonens
import dev.moklev.mathproof.logic.ScopedAssumptionDependentCompilationContext
import dev.moklev.mathproof.logic.ScopedJustificationSupport
import dev.moklev.mathproof.logic.implies
import dev.moklev.mathproof.logic.registerScopedJustificationSupport
import dev.moklev.mathproof.logic.validateGeneralizationVariableInLogicScope
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

private const val SCOPED_GENERALIZATION_SOURCE_PLACEHOLDER = "__scoped-generalization-source__"

private object UniversalGeneralizationScopedSupport : ScopedJustificationSupport<UniversalGeneralization> {
    override val justificationClass = UniversalGeneralization::class

    override fun bindToPremises(
        justification: UniversalGeneralization,
        premiseLabels: List<String>,
    ): UniversalGeneralization {
        require(premiseLabels.size == 1) {
            "Universal generalization expects exactly one source premise, but got ${premiseLabels.size}."
        }
        return justification.copy(sourceLabel = premiseLabels.single())
    }

    override fun compileAssumptionDependent(
        context: ScopedAssumptionDependentCompilationContext,
        justification: UniversalGeneralization,
    ): DerivationFact {
        require(context.premiseStepIds.size == 1) {
            "Scoped universal generalization expected exactly one premise step, but got ${context.premiseStepIds.size}."
        }
        val sourceStepId = context.premiseStepIds.single()
        val sourceClaim = context.premiseClaim(sourceStepId)
        val expectedConclusion = forAllGeneralizedClaim(justification.variable, sourceClaim)
        require(context.sameProposition(expectedConclusion, context.conclusion)) {
            "Scoped universal generalization expected conclusion '$expectedConclusion', but got '${context.conclusion}'."
        }
        require(!context.assumption.containsFreeSymbol(justification.variable.symbol)) {
            "Universal generalization over '${justification.variable.displayName}' is invalid because this variable appears in an open assumption."
        }

        val assumptionToSource = context.implication(sourceStepId)
        val generalizedAssumptionImplication = forAllGeneralizedClaim(
            variable = justification.variable,
            sourceClaim = context.assumption implies sourceClaim,
        )
        val quantifiedSourcePredicate = expectedConclusion.forAllPredicateOrNull()
            ?: throw IllegalArgumentException(
                "Scoped universal generalization expected a forall-claim, but got '$expectedConclusion'.",
            )

        val generalizedAssumption = context.justify(
            claim = generalizedAssumptionImplication,
            justification = justification.copy(sourceLabel = SCOPED_GENERALIZATION_SOURCE_PLACEHOLDER),
            assumptionToSource,
        )
        val distribution = context.infer(
            FirstOrderAxioms.forallDistribution(context.assumption, quantifiedSourcePredicate)
        )

        return context.infer(
            modusPonens(
                generalizedAssumptionImplication,
                context.assumption implies expectedConclusion,
            ),
            generalizedAssumption,
            distribution,
        )
    }
}

private val scopedUniversalGeneralizationSupportRegistered: Boolean = run {
    registerScopedJustificationSupport(UniversalGeneralizationScopedSupport)
    true
}

private fun ensureScopedUniversalGeneralizationSupportRegistered() {
    check(scopedUniversalGeneralizationSupportRegistered)
}

fun DerivationScope.generalizeForAll(
    variable: Free,
    source: DerivationFact,
): DerivationFact {
    ensureScopedUniversalGeneralizationSupportRegistered()
    validateGeneralizationVariableInLogicScope(variable)

    val sourceInScope = given(source)
    val sourceLabel = factLabel(sourceInScope) ?: SCOPED_GENERALIZATION_SOURCE_PLACEHOLDER
    return justify(
        claim = forAllGeneralizedClaim(variable, sourceInScope.claim),
        justification = UniversalGeneralization(
            sourceLabel = sourceLabel,
            variable = variable,
        ),
        premises = listOf(sourceInScope),
    )
}

/**
 * Declares a proof-local arbitrary variable and universally generalizes the last proof step emitted by [proveAt].
 */
fun DerivationScope.forAllByGeneralization(
    variableName: String,
    sort: Sort,
    proveAt: (Free) -> Unit,
): DerivationFact {
    ensureScopedUniversalGeneralizationSupportRegistered()
    val variable = arbitrary(variableName, sort)
    val source = withLastFactFrom("forAllByGeneralization") {
        proveAt(variable)
    }
    return generalizeForAll(variable, source)
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
