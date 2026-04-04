package dev.moklev.mathproof.logic

import dev.moklev.mathproof.kernel.Fact
import dev.moklev.mathproof.kernel.ProofBuilder
import dev.moklev.mathproof.kernel.StatementCall
import dev.moklev.mathproof.kernel.StatementPremise
import dev.moklev.mathproof.model.Apply
import dev.moklev.mathproof.model.Expr
import dev.moklev.mathproof.model.betaNormalize
import dev.moklev.mathproof.model.requireProposition

class ScopedFact internal constructor(
    internal val context: AssumptionContext,
    internal val stepId: Int,
    val claim: Expr,
)

class AssumptionScope internal constructor(
    private val context: AssumptionContext,
) {
    val assumption: ScopedFact
        get() = context.assumptionFact

    fun given(fact: ScopedFact): ScopedFact = context.useScopedFact(fact)

    fun given(fact: Fact): ScopedFact = context.useOuterFact(fact)

    fun given(premise: StatementPremise): ScopedFact = context.usePremise(premise)

    fun infer(statement: StatementCall, vararg premises: ScopedFact): ScopedFact =
        context.infer(statement, premises.toList())

    fun applyByMpChain(statement: StatementCall, vararg facts: ScopedFact): ScopedFact {
        require(statement.premises.isEmpty()) {
            "applyByMpChain expects a premise-free theorem, but statement '${statement.statement.name}' has ${statement.premises.size} declared premise(s)."
        }

        var current = infer(statement)
        facts.forEachIndexed { index, fact ->
            val resolvedFact = given(fact)
            val implication = current.claim.implicationPartsOrNull()
                ?: throw IllegalArgumentException(
                    "applyByMpChain expected an implication before applying fact ${index + 1}, but current claim is '${current.claim}'.",
                )

            require(sameProposition(resolvedFact.claim, implication.left)) {
                "applyByMpChain fact ${index + 1} mismatch: expected '${implication.left}', but got '${resolvedFact.claim}'."
            }

            current = infer(
                LogicAxioms.modusPonens(implication.left, implication.right),
                resolvedFact,
                current,
            )
        }

        return current
    }

    fun assume(assume: Expr, block: AssumptionScope.() -> ScopedFact): ScopedFact =
        context.assume(assume, block)

    fun contradiction(assume: Expr, block: AssumptionScope.() -> ScopedFact): ScopedFact =
        context.contradiction(assume, block)
}

fun ProofBuilder.assume(assume: Expr, block: AssumptionScope.() -> ScopedFact): Fact {
    requireProposition(assume, "Assumption")
    val assumptionContext = AssumptionContext(parent = null, assumptionClaim = assume)
    val result = AssumptionScope(assumptionContext).block()
    val resultInsideContext = assumptionContext.useScopedFact(result)
    return assumptionContext.compileIntoProofBuilder(this, resultInsideContext.stepId)
}

fun ProofBuilder.contradiction(assume: Expr, block: AssumptionScope.() -> ScopedFact): Fact {
    val target = requireContradictionTarget(assume)
    val implication = this.assume(assume, block)
    val expectedImplication = assume implies target
    require(sameProposition(implication.claim, expectedImplication)) {
        "contradiction(assume = $assume) expects the block to return '$target', but discharge produced '${implication.claim}'."
    }

    val clavius = infer(LogicLibrary.clavius(target))
    return infer(
        LogicAxioms.modusPonens(expectedImplication, target),
        implication,
        clavius,
    )
}

fun ProofBuilder.applyByMpChain(statement: StatementCall, vararg facts: Fact): Fact {
    require(statement.premises.isEmpty()) {
        "applyByMpChain expects a premise-free theorem, but statement '${statement.statement.name}' has ${statement.premises.size} declared premise(s)."
    }

    var current = infer(statement)
    facts.forEachIndexed { index, fact ->
        val implication = current.claim.implicationPartsOrNull()
            ?: throw IllegalArgumentException(
                "applyByMpChain expected an implication before applying fact ${index + 1}, but current claim is '${current.claim}'.",
            )

        require(sameProposition(fact.claim, implication.left)) {
            "applyByMpChain fact ${index + 1} mismatch: expected '${implication.left}', but got '${fact.claim}'."
        }

        current = infer(
            LogicAxioms.modusPonens(implication.left, implication.right),
            fact,
            current,
        )
    }

    return current
}

internal class AssumptionContext(
    private val parent: AssumptionContext?,
    private val assumptionClaim: Expr,
) {
    private val steps = mutableListOf<ScopedStep>()
    private val stepsById = linkedMapOf<Int, ScopedStep>()
    private val importedOuterFacts = linkedMapOf<Fact, ScopedFact>()
    private val importedPremises = linkedMapOf<StatementPremise, ScopedFact>()
    private val importedAncestorFacts = linkedMapOf<ScopedFact, ScopedFact>()
    private var nextStepId = 0

    val assumptionFact: ScopedFact = addStep(
        claim = assumptionClaim,
        origin = ScopedStepOrigin.Assumption,
        dependsOnAssumption = true,
    )

    fun useScopedFact(fact: ScopedFact): ScopedFact {
        if (fact.context === this) {
            return fact
        }
        if (!fact.context.isAncestorOf(this)) {
            throw IllegalArgumentException("Scoped fact '${fact.claim}' does not belong to this assumption context.")
        }
        return importedAncestorFacts.getOrPut(fact) {
            addStep(
                claim = fact.claim,
                origin = ScopedStepOrigin.ImportedAncestorFact(fact),
                dependsOnAssumption = false,
            )
        }
    }

    fun useOuterFact(fact: Fact): ScopedFact = importedOuterFacts.getOrPut(fact) {
        addStep(
            claim = fact.claim,
            origin = ScopedStepOrigin.ImportedOuterFact(fact),
            dependsOnAssumption = false,
        )
    }

    fun usePremise(premise: StatementPremise): ScopedFact = importedPremises.getOrPut(premise) {
        addStep(
            claim = premise.claim,
            origin = ScopedStepOrigin.ImportedPremise(premise),
            dependsOnAssumption = false,
        )
    }

    fun infer(statement: StatementCall, premises: List<ScopedFact>): ScopedFact {
        val resolvedPremises = premises.map(::useScopedFact)
        val premiseStepIds = resolvedPremises.map { it.stepId }
        val dependsOnAssumption = premiseStepIds.any { stepById(it).dependsOnAssumption }

        val isModusPonens = statement.statement == LogicAxioms.modusPonens
        if (isModusPonens) {
            require(resolvedPremises.size == 2) {
                "Scoped assumption compiler expected 2 premises for modus ponens, got ${resolvedPremises.size}."
            }
            val premiseClaim = resolvedPremises[0].claim
            val implicationClaim = resolvedPremises[1].claim
            val expectedImplication = premiseClaim implies statement.conclusion
            require(sameProposition(implicationClaim, expectedImplication)) {
                "Scoped assumption compiler expected MP implication '$expectedImplication', but got '$implicationClaim'."
            }
            return addStep(
                claim = statement.conclusion,
                origin = ScopedStepOrigin.DerivedModusPonens(
                    statement = statement,
                    premiseStepIds = premiseStepIds,
                ),
                dependsOnAssumption = dependsOnAssumption,
            )
        }

        require(!dependsOnAssumption) {
            "Scoped assumption compiler currently supports assumption-dependent steps only through modus ponens; statement '${statement.statement.name}' depends on the local assumption."
        }

        return addStep(
            claim = statement.conclusion,
            origin = ScopedStepOrigin.DerivedGeneral(
                statement = statement,
                premiseStepIds = premiseStepIds,
            ),
            dependsOnAssumption = false,
        )
    }

    fun assume(assume: Expr, block: AssumptionScope.() -> ScopedFact): ScopedFact {
        requireProposition(assume, "Assumption")
        val nested = AssumptionContext(parent = this, assumptionClaim = assume)
        val result = AssumptionScope(nested).block()
        val resultInsideNested = nested.useScopedFact(result)
        return nested.compileIntoContext(this, resultInsideNested.stepId)
    }

    fun contradiction(assume: Expr, block: AssumptionScope.() -> ScopedFact): ScopedFact {
        val target = requireContradictionTarget(assume)
        val implication = this.assume(assume, block)
        val expectedImplication = assume implies target
        require(sameProposition(implication.claim, expectedImplication)) {
            "contradiction(assume = $assume) expects the block to return '$target', but discharge produced '${implication.claim}'."
        }

        val clavius = infer(LogicLibrary.clavius(target), emptyList())
        return infer(
            LogicAxioms.modusPonens(expectedImplication, target),
            listOf(implication, clavius),
        )
    }

    fun compileIntoProofBuilder(builder: ProofBuilder, resultStepId: Int): Fact {
        val target = ProofBuilderCompilationTarget(builder)
        return DeductionCompiler(
            assumption = assumptionClaim,
            steps = steps.toList(),
            target = target,
        ).compile(resultStepId)
    }

    fun compileIntoContext(parentContext: AssumptionContext, resultStepId: Int): ScopedFact {
        val target = AssumptionContextCompilationTarget(parentContext)
        return DeductionCompiler(
            assumption = assumptionClaim,
            steps = steps.toList(),
            target = target,
        ).compile(resultStepId)
    }

    private fun addStep(
        claim: Expr,
        origin: ScopedStepOrigin,
        dependsOnAssumption: Boolean,
    ): ScopedFact {
        val normalizedClaim = claim.betaNormalize()
        requireProposition(normalizedClaim, "Scoped proof step")
        val step = ScopedStep(
            id = nextStepId++,
            claim = normalizedClaim,
            origin = origin,
            dependsOnAssumption = dependsOnAssumption,
        )
        steps += step
        stepsById[step.id] = step
        return ScopedFact(this, step.id, normalizedClaim)
    }

    private fun stepById(id: Int): ScopedStep =
        requireNotNull(stepsById[id]) { "Unknown scoped step id '$id'." }

    private fun isAncestorOf(descendant: AssumptionContext): Boolean {
        var cursor = descendant.parent
        while (cursor != null) {
            if (cursor === this) {
                return true
            }
            cursor = cursor.parent
        }
        return false
    }
}

private data class ScopedStep(
    val id: Int,
    val claim: Expr,
    val origin: ScopedStepOrigin,
    val dependsOnAssumption: Boolean,
)

private sealed interface ScopedStepOrigin {
    data object Assumption : ScopedStepOrigin

    data class ImportedOuterFact(
        val fact: Fact,
    ) : ScopedStepOrigin

    data class ImportedPremise(
        val premise: StatementPremise,
    ) : ScopedStepOrigin

    data class ImportedAncestorFact(
        val fact: ScopedFact,
    ) : ScopedStepOrigin

    data class DerivedGeneral(
        val statement: StatementCall,
        val premiseStepIds: List<Int>,
    ) : ScopedStepOrigin

    data class DerivedModusPonens(
        val statement: StatementCall,
        val premiseStepIds: List<Int>,
    ) : ScopedStepOrigin
}

private interface CompilationTarget<F> {
    fun givenPremise(premise: StatementPremise): F
    fun givenOuterFact(fact: Fact): F
    fun givenAncestorFact(fact: ScopedFact): F
    fun infer(statement: StatementCall, premises: List<F>): F
}

private class ProofBuilderCompilationTarget(
    private val builder: ProofBuilder,
) : CompilationTarget<Fact> {
    override fun givenPremise(premise: StatementPremise): Fact = builder.given(premise)

    override fun givenOuterFact(fact: Fact): Fact = fact

    override fun givenAncestorFact(fact: ScopedFact): Fact {
        throw IllegalStateException("Top-level scoped compilation cannot import ancestor scoped facts.")
    }

    override fun infer(statement: StatementCall, premises: List<Fact>): Fact =
        builder.infer(statement, *premises.toTypedArray())
}

private class AssumptionContextCompilationTarget(
    private val context: AssumptionContext,
) : CompilationTarget<ScopedFact> {
    override fun givenPremise(premise: StatementPremise): ScopedFact = context.usePremise(premise)

    override fun givenOuterFact(fact: Fact): ScopedFact = context.useOuterFact(fact)

    override fun givenAncestorFact(fact: ScopedFact): ScopedFact = context.useScopedFact(fact)

    override fun infer(statement: StatementCall, premises: List<ScopedFact>): ScopedFact =
        context.infer(statement, premises)
}

private class DeductionCompiler<F>(
    private val assumption: Expr,
    steps: List<ScopedStep>,
    private val target: CompilationTarget<F>,
) {
    private val stepsByIdMap = steps.associateBy { it.id }
    private val orderedSteps = steps
    private val implicationByStepId = linkedMapOf<Int, F>()
    private val rawByStepId = linkedMapOf<Int, F>()

    fun compile(resultStepId: Int): F {
        orderedSteps.forEach { step ->
            implicationByStepId[step.id] = compileImplication(step)
        }
        return requireNotNull(implicationByStepId[resultStepId]) {
            "Cannot compile scoped result step '$resultStepId': the step does not belong to this assumption block."
        }
    }

    private fun compileImplication(step: ScopedStep): F {
        if (step.origin is ScopedStepOrigin.Assumption) {
            return target.infer(LogicLibrary.implicationIdentity(assumption), emptyList())
        }

        if (!step.dependsOnAssumption) {
            val raw = replayRaw(step.id)
            val lift = target.infer(
                LogicAxioms.hilbertAxiom1(step.claim, assumption),
                emptyList(),
            )
            return target.infer(
                LogicAxioms.modusPonens(step.claim, assumption implies step.claim),
                listOf(raw, lift),
            )
        }

        val origin = step.origin as? ScopedStepOrigin.DerivedModusPonens
            ?: error("Assumption-dependent step '${step.claim}' is not derived by modus ponens.")

        val premiseStepId = origin.premiseStepIds[0]
        val implicationStepId = origin.premiseStepIds[1]
        val premiseStep = stepById(premiseStepId)

        val aToPremise = requireNotNull(implicationByStepId[premiseStepId]) {
            "Missing compiled implication for premise step $premiseStepId."
        }
        val aToImplication = requireNotNull(implicationByStepId[implicationStepId]) {
            "Missing compiled implication for implication step $implicationStepId."
        }

        val axiom2 = target.infer(
            LogicAxioms.hilbertAxiom2(assumption, premiseStep.claim, step.claim),
            emptyList(),
        )
        val bridge = target.infer(
            LogicAxioms.modusPonens(
                assumption implies (premiseStep.claim implies step.claim),
                (assumption implies premiseStep.claim) implies (assumption implies step.claim),
            ),
            listOf(aToImplication, axiom2),
        )

        return target.infer(
            LogicAxioms.modusPonens(assumption implies premiseStep.claim, assumption implies step.claim),
            listOf(aToPremise, bridge),
        )
    }

    private fun replayRaw(stepId: Int): F {
        rawByStepId[stepId]?.let { return it }
        val step = stepById(stepId)
        val rebuilt = when (val origin = step.origin) {
            is ScopedStepOrigin.Assumption ->
                error("Assumption step '${step.claim}' cannot be replayed as an independent raw step.")
            is ScopedStepOrigin.ImportedOuterFact -> target.givenOuterFact(origin.fact)
            is ScopedStepOrigin.ImportedPremise -> target.givenPremise(origin.premise)
            is ScopedStepOrigin.ImportedAncestorFact -> target.givenAncestorFact(origin.fact)
            is ScopedStepOrigin.DerivedGeneral -> target.infer(
                origin.statement,
                origin.premiseStepIds.map(::replayRaw),
            )
            is ScopedStepOrigin.DerivedModusPonens -> target.infer(
                origin.statement,
                origin.premiseStepIds.map(::replayRaw),
            )
        }
        rawByStepId[stepId] = rebuilt
        return rebuilt
    }

    private fun stepById(stepId: Int): ScopedStep =
        requireNotNull(stepsByIdMap[stepId]) { "Unknown scoped step id '$stepId'." }
}

private fun requireContradictionTarget(assume: Expr): Expr =
    assume.negatedArgumentOrNull()
        ?: throw IllegalArgumentException("contradiction requires a negated assumption like !p, but got '$assume'.")

private fun Expr.negatedArgumentOrNull(): Expr? {
    val apply = this as? Apply ?: return null
    return if (apply.function == LogicFunctions.Not) {
        apply.argument
    } else {
        null
    }
}

private data class ImplicationParts(
    val left: Expr,
    val right: Expr,
)

private fun Expr.implicationPartsOrNull(): ImplicationParts? {
    val outerApply = this as? Apply ?: return null
    val innerApply = outerApply.function as? Apply ?: return null
    if (innerApply.function != LogicFunctions.Implies) {
        return null
    }
    return ImplicationParts(
        left = innerApply.argument,
        right = outerApply.argument,
    )
}

private fun sameProposition(left: Expr, right: Expr): Boolean =
    left.betaNormalize() == right.betaNormalize()
