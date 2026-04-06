package dev.moklev.mathproof.logic

import dev.moklev.mathproof.kernel.Fact
import dev.moklev.mathproof.kernel.Justification
import dev.moklev.mathproof.kernel.ProofBuilder
import dev.moklev.mathproof.kernel.StatementCall
import dev.moklev.mathproof.kernel.StatementPremise
import dev.moklev.mathproof.model.Apply
import dev.moklev.mathproof.model.Bound
import dev.moklev.mathproof.model.Expr
import dev.moklev.mathproof.model.Free
import dev.moklev.mathproof.model.Lambda
import dev.moklev.mathproof.model.Sort
import dev.moklev.mathproof.model.betaNormalize
import dev.moklev.mathproof.model.requireProposition
import kotlin.reflect.KClass

class ScopedFact internal constructor(
    internal val context: AssumptionContext,
    internal val stepId: Int,
    val claim: Expr,
)

interface ScopedAssumptionDependentCompilationContext<F> {
    val assumption: Expr
    val conclusion: Expr
    val premiseStepIds: List<Int>

    fun premiseClaim(stepId: Int): Expr
    fun implication(stepId: Int): F
    fun infer(statement: StatementCall, vararg premises: F): F
    fun justify(claim: Expr, justification: Justification, vararg premises: F): F
    fun sameProposition(left: Expr, right: Expr): Boolean
}

interface ScopedJustificationSupport<J : Justification> {
    val justificationClass: KClass<J>

    fun bindToPremises(justification: J, premiseLabels: List<String>): J = justification

    fun <F> compileAssumptionDependent(
        context: ScopedAssumptionDependentCompilationContext<F>,
        justification: J,
    ): F? = null
}

fun registerScopedJustificationSupport(
    support: ScopedJustificationSupport<out Justification>,
) {
    ScopedJustificationSupportRegistry.register(support)
}

private object ScopedJustificationSupportRegistry {
    private val supportByClass = linkedMapOf<KClass<out Justification>, ScopedJustificationSupport<out Justification>>()

    @Synchronized
    fun register(support: ScopedJustificationSupport<out Justification>) {
        supportByClass[support.justificationClass] = support
    }

    @Suppress("UNCHECKED_CAST")
    fun <J : Justification> supportFor(justification: J): ScopedJustificationSupport<J>? =
        supportByClass[justification::class] as? ScopedJustificationSupport<J>

    fun bindToPremises(justification: Justification, premiseLabels: List<String>): Justification {
        val support = supportFor(justification) ?: return justification
        return support.bindToPremises(justification, premiseLabels)
    }
}

class AssumptionScope internal constructor(
    private val context: AssumptionContext,
) {
    fun given(fact: ScopedFact): ScopedFact = context.referenceScopedFact(fact)

    fun given(fact: Fact): ScopedFact = context.useOuterFact(fact)

    fun given(premise: StatementPremise): ScopedFact = context.usePremise(premise)

    fun infer(statement: StatementCall, vararg premises: ScopedFact): ScopedFact =
        context.infer(statement, premises.toList())

    fun justify(claim: Expr, justification: Justification, vararg premises: ScopedFact): ScopedFact =
        context.justify(claim, justification, premises.toList())

    fun arbitrary(name: String, sort: Sort): Free = context.arbitrary(name, sort)

    fun hasFreeSymbolInOpenAssumptions(symbol: String): Boolean =
        context.hasFreeSymbolInOpenAssumptions(symbol)

    fun hasFreeSymbolInStatementPremises(symbol: String): Boolean =
        context.hasFreeSymbolInStatementPremises(symbol)

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

    fun assume(assume: Expr, block: AssumptionScope.(ScopedFact) -> Unit): ScopedFact =
        context.assume(assume, block)

    fun contradiction(assume: Expr, block: AssumptionScope.(ScopedFact) -> Unit): ScopedFact =
        context.contradiction(assume, block)
}

fun ProofBuilder.assume(assume: Expr, block: AssumptionScope.(ScopedFact) -> Unit): Fact {
    requireProposition(assume, "Assumption")
    val assumptionContext = AssumptionContext(
        parent = null,
        assumptionClaim = assume,
        statementPremises = declaredPremises(),
        arbitraryAllocator = this::arbitrary,
    )
    AssumptionScope(assumptionContext).block(assumptionContext.assumptionFact)
    val resultInsideContext = assumptionContext.requireLastDerivedStep()
    return assumptionContext.compileIntoProofBuilder(this, resultInsideContext.stepId)
}

fun ProofBuilder.contradiction(assume: Expr, block: AssumptionScope.(ScopedFact) -> Unit): Fact {
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
    private val statementPremises: List<Expr>,
    private val arbitraryAllocator: (String, Sort) -> Free,
) {
    private val steps = mutableListOf<ScopedStep>()
    private val stepsById = linkedMapOf<Int, ScopedStep>()
    private val importedOuterFacts = linkedMapOf<Fact, ScopedFact>()
    private val importedPremises = linkedMapOf<StatementPremise, ScopedFact>()
    private val importedAncestorFacts = linkedMapOf<ScopedFact, ScopedFact>()
    private var nextStepId = 0
    private var lastStepId: Int? = null

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

    fun referenceScopedFact(fact: ScopedFact): ScopedFact {
        if (fact.context === this) {
            val sourceStep = stepById(fact.stepId)
            return addStep(
                claim = fact.claim,
                origin = ScopedStepOrigin.ReusedScopedFact(sourceStep.id),
                dependsOnAssumption = sourceStep.dependsOnAssumption,
            )
        }
        return useScopedFact(fact)
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

    fun justify(claim: Expr, justification: Justification, premises: List<ScopedFact>): ScopedFact {
        val resolvedPremises = premises.map(::useScopedFact)
        val premiseStepIds = resolvedPremises.map { it.stepId }
        val dependsOnAssumption = premiseStepIds.any { stepById(it).dependsOnAssumption }

        return addStep(
            claim = claim,
            origin = ScopedStepOrigin.DerivedExternal(
                justification = justification,
                premiseStepIds = premiseStepIds,
            ),
            dependsOnAssumption = dependsOnAssumption,
        )
    }

    fun arbitrary(name: String, sort: Sort): Free = arbitraryAllocator(name, sort)

    fun hasFreeSymbolInOpenAssumptions(symbol: String): Boolean {
        var cursor: AssumptionContext? = this
        while (cursor != null) {
            if (cursor.assumptionClaim.containsFreeSymbol(symbol)) {
                return true
            }
            cursor = cursor.parent
        }
        return false
    }

    fun hasFreeSymbolInStatementPremises(symbol: String): Boolean =
        statementPremises.any { premise -> premise.containsFreeSymbol(symbol) }

    fun assume(assume: Expr, block: AssumptionScope.(ScopedFact) -> Unit): ScopedFact {
        requireProposition(assume, "Assumption")
        val nested = AssumptionContext(
            parent = this,
            assumptionClaim = assume,
            statementPremises = statementPremises,
            arbitraryAllocator = arbitraryAllocator,
        )
        AssumptionScope(nested).block(nested.assumptionFact)
        val resultInsideNested = nested.requireLastDerivedStep()
        return nested.compileIntoContext(this, resultInsideNested.stepId)
    }

    fun contradiction(assume: Expr, block: AssumptionScope.(ScopedFact) -> Unit): ScopedFact {
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

    fun requireLastDerivedStep(): ScopedFact {
        val resolvedLastStepId = requireNotNull(lastStepId) {
            "Scoped assumption block did not emit any steps."
        }
        require(resolvedLastStepId != assumptionFact.stepId) {
            "assume(...) block must contain at least one proof step."
        }
        val step = stepById(resolvedLastStepId)
        return ScopedFact(this, step.id, step.claim)
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
        lastStepId = step.id
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

    data class ReusedScopedFact(
        val sourceStepId: Int,
    ) : ScopedStepOrigin

    data class DerivedGeneral(
        val statement: StatementCall,
        val premiseStepIds: List<Int>,
    ) : ScopedStepOrigin

    data class DerivedModusPonens(
        val statement: StatementCall,
        val premiseStepIds: List<Int>,
    ) : ScopedStepOrigin

    data class DerivedExternal(
        val justification: Justification,
        val premiseStepIds: List<Int>,
    ) : ScopedStepOrigin
}

private interface CompilationTarget<F> {
    fun givenPremise(premise: StatementPremise): F
    fun givenOuterFact(fact: Fact): F
    fun givenAncestorFact(fact: ScopedFact): F
    fun infer(statement: StatementCall, premises: List<F>): F
    fun justify(claim: Expr, justification: Justification, premises: List<F>): F
    fun labelOf(fact: F): String?
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

    override fun justify(claim: Expr, justification: Justification, premises: List<Fact>): Fact =
        builder.justify(claim, justification, *premises.toTypedArray())

    override fun labelOf(fact: Fact): String = fact.label
}

private class AssumptionContextCompilationTarget(
    private val context: AssumptionContext,
) : CompilationTarget<ScopedFact> {
    override fun givenPremise(premise: StatementPremise): ScopedFact = context.usePremise(premise)

    override fun givenOuterFact(fact: Fact): ScopedFact = context.useOuterFact(fact)

    override fun givenAncestorFact(fact: ScopedFact): ScopedFact = context.useScopedFact(fact)

    override fun infer(statement: StatementCall, premises: List<ScopedFact>): ScopedFact =
        context.infer(statement, premises)

    override fun justify(claim: Expr, justification: Justification, premises: List<ScopedFact>): ScopedFact =
        context.justify(claim, justification, premises)

    override fun labelOf(fact: ScopedFact): String? = null
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

        if (step.origin is ScopedStepOrigin.ReusedScopedFact) {
            return requireNotNull(implicationByStepId[step.origin.sourceStepId]) {
                "Missing compiled implication for reused step ${step.origin.sourceStepId}."
            }
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

        return when (val origin = step.origin) {
            is ScopedStepOrigin.DerivedModusPonens -> compileAssumptionDependentModusPonens(step, origin)
            is ScopedStepOrigin.DerivedExternal -> compileAssumptionDependentExternal(step, origin)
            else -> error("Assumption-dependent step '${step.claim}' has unsupported origin '${step.origin::class.simpleName}'.")
        }
    }

    private fun compileAssumptionDependentModusPonens(
        step: ScopedStep,
        origin: ScopedStepOrigin.DerivedModusPonens,
    ): F {
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

    private fun compileAssumptionDependentExternal(
        step: ScopedStep,
        origin: ScopedStepOrigin.DerivedExternal,
    ): F {
        val support = ScopedJustificationSupportRegistry.supportFor(origin.justification)
            ?: throw IllegalArgumentException(
                "Scoped assumption compiler currently supports assumption-dependent steps only through modus ponens; justification '${origin.justification.displayName}' depends on the local assumption.",
            )

        val context = object : ScopedAssumptionDependentCompilationContext<F> {
            override val assumption: Expr = this@DeductionCompiler.assumption
            override val conclusion: Expr = step.claim
            override val premiseStepIds: List<Int> = origin.premiseStepIds

            override fun premiseClaim(stepId: Int): Expr = stepById(stepId).claim

            override fun implication(stepId: Int): F =
                requireNotNull(implicationByStepId[stepId]) {
                    "Missing compiled implication for premise step $stepId."
                }

            override fun infer(statement: StatementCall, vararg premises: F): F =
                target.infer(statement, premises.toList())

            override fun justify(claim: Expr, justification: Justification, vararg premises: F): F {
                val premiseList = premises.toList()
                return target.justify(
                    claim = claim,
                    justification = bindJustificationToPremises(justification, premiseList),
                    premises = premiseList,
                )
            }

            override fun sameProposition(left: Expr, right: Expr): Boolean =
                left.betaNormalize() == right.betaNormalize()
        }

        return support.compileAssumptionDependent(context, origin.justification)
            ?: throw IllegalArgumentException(
                "Scoped assumption compiler currently supports assumption-dependent steps only through modus ponens; justification '${origin.justification.displayName}' depends on the local assumption.",
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
            is ScopedStepOrigin.ReusedScopedFact -> replayRaw(origin.sourceStepId)
            is ScopedStepOrigin.DerivedGeneral -> target.infer(
                origin.statement,
                origin.premiseStepIds.map(::replayRaw),
            )
            is ScopedStepOrigin.DerivedModusPonens -> target.infer(
                origin.statement,
                origin.premiseStepIds.map(::replayRaw),
            )
            is ScopedStepOrigin.DerivedExternal -> {
                val rawPremises = origin.premiseStepIds.map(::replayRaw)
                target.justify(
                    claim = step.claim,
                    justification = bindJustificationToPremises(origin.justification, rawPremises),
                    premises = rawPremises,
                )
            }
        }
        rawByStepId[stepId] = rebuilt
        return rebuilt
    }

    private fun bindJustificationToPremises(justification: Justification, premises: List<F>): Justification {
        val premiseLabels = premises.map { fact -> target.labelOf(fact) }
        if (premiseLabels.any { label -> label == null }) {
            return justification
        }
        return ScopedJustificationSupportRegistry.bindToPremises(
            justification = justification,
            premiseLabels = premiseLabels.filterNotNull(),
        )
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

private fun Expr.containsFreeSymbol(symbol: String): Boolean = when (this) {
    is Free -> this.symbol == symbol
    is Bound -> false
    is Lambda -> body.containsFreeSymbol(symbol)
    is Apply -> function.containsFreeSymbol(symbol) || argument.containsFreeSymbol(symbol)
}

private fun sameProposition(left: Expr, right: Expr): Boolean =
    left.betaNormalize() == right.betaNormalize()
