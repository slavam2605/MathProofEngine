package dev.moklev.mathproof.logic

import dev.moklev.mathproof.kernel.Fact
import dev.moklev.mathproof.kernel.Justification
import dev.moklev.mathproof.kernel.ProofBuilder
import dev.moklev.mathproof.kernel.DerivationFact
import dev.moklev.mathproof.kernel.DerivationScope
import dev.moklev.mathproof.kernel.StatementCall
import dev.moklev.mathproof.kernel.StatementDefinition
import dev.moklev.mathproof.kernel.StatementPremise
import dev.moklev.mathproof.kernel.TodoAssumption
import dev.moklev.mathproof.kernel.resolveFromMatches
import dev.moklev.mathproof.kernel.resolveFromPremises
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
    override val claim: Expr,
) : DerivationFact

interface ScopedAssumptionDependentCompilationContext {
    val assumption: Expr
    val conclusion: Expr
    val premiseStepIds: List<Int>

    fun premiseClaim(stepId: Int): Expr
    fun implication(stepId: Int): DerivationFact
    fun infer(statement: StatementCall, vararg premises: DerivationFact): DerivationFact
    fun justify(claim: Expr, justification: Justification, vararg premises: DerivationFact): DerivationFact
    fun sameProposition(left: Expr, right: Expr): Boolean
}

interface ScopedJustificationSupport<J : Justification> {
    val justificationClass: KClass<J>

    fun bindToPremises(justification: J, premiseLabels: List<String>): J = justification

    fun compileAssumptionDependent(
        context: ScopedAssumptionDependentCompilationContext,
        justification: J,
    ): DerivationFact? = null
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
) : DerivationScope {
    override fun given(fact: DerivationFact): ScopedFact = when (fact) {
        is ScopedFact -> context.referenceScopedFact(fact)
        is Fact -> context.useOuterFact(fact)
        else -> throw IllegalArgumentException(
            "Assumption scope can only import Fact/ScopedFact handles, but got '${fact::class.simpleName ?: "unknown"}'.",
        )
    }

    override fun given(premise: StatementPremise): ScopedFact = context.usePremise(premise)

    override fun infer(statement: StatementCall, vararg premises: DerivationFact): ScopedFact {
        val scopedPremises = premises.map(::given)
        val resolvedStatement = statement.resolveFromPremises(scopedPremises.map { premise -> premise.claim })
        return context.infer(resolvedStatement, scopedPremises)
    }

    override fun infer(statement: StatementCall, premises: List<DerivationFact>): ScopedFact {
        val scopedPremises = premises.map(::given)
        val resolvedStatement = statement.resolveFromPremises(scopedPremises.map { premise -> premise.claim })
        return context.infer(resolvedStatement, scopedPremises)
    }

    override fun infer(
        statement: StatementDefinition,
        vararg premises: DerivationFact,
    ): ScopedFact =
        infer(
            statement.autoCall(),
            *premises,
        )

    override fun infer(
        statement: StatementDefinition,
        premises: List<DerivationFact>,
    ): ScopedFact =
        infer(
            statement.autoCall(),
            *premises.toTypedArray(),
        )

    override fun justify(claim: Expr, justification: Justification, vararg premises: DerivationFact): ScopedFact =
        context.justify(claim, justification, premises.map(::given))

    override fun justify(claim: Expr, justification: Justification, premises: List<DerivationFact>): ScopedFact =
        context.justify(claim, justification, premises.map(::given))

    override fun todoAssume(
        claim: Expr,
        note: String?,
    ): ScopedFact = justify(
        claim = claim,
        justification = TodoAssumption(note),
    )

    fun todoAssume(claim: Expr): ScopedFact = todoAssume(claim, null)

    override fun arbitrary(name: String, sort: Sort): Free = context.arbitrary(name, sort)

    fun hasFreeSymbolInOpenAssumptions(symbol: String): Boolean =
        context.hasFreeSymbolInOpenAssumptions(symbol)

    fun hasFreeSymbolInStatementPremises(symbol: String): Boolean =
        context.hasFreeSymbolInStatementPremises(symbol)

    fun assume(assume: Expr, block: AssumptionScope.(ScopedFact) -> Unit): ScopedFact =
        context.assume(assume, block)

    fun contradiction(assume: Expr, block: AssumptionScope.(ScopedFact) -> Unit): ScopedFact =
        context.contradiction(assume, block)

    override fun withLastFactFrom(blockDescription: String, block: DerivationScope.() -> Unit): ScopedFact {
        val stepCountBefore = context.currentStepCount()
        this.block()
        return context.requireLastDerivedStepSince(stepCountBefore, blockDescription)
    }
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

/**
 * Generic bridge for modules above `logic` that need assume-discharge without concrete
 * dependency on AssumptionScope/ScopedFact.
 */
fun DerivationScope.assumeInLogicScope(
    assumption: Expr,
    block: DerivationScope.(DerivationFact) -> Unit,
): DerivationFact =
    when (this) {
        is ProofBuilder -> assume(assumption) { scopedFact ->
            block(this, scopedFact)
        }
        is AssumptionScope -> assume(assumption) { scopedFact ->
            block(this, scopedFact)
        }
        else -> throw IllegalArgumentException(
            "This scope does not support logic assumptions: '${this::class.simpleName ?: "unknown"}'.",
        )
    }

fun DerivationScope.validateGeneralizationVariableInLogicScope(variable: Free) {
    val appearsInPremises: Boolean
    val appearsInAssumptions: Boolean
    when (this) {
        is ProofBuilder -> {
            appearsInPremises = declaredPremises().any { premise ->
                premise.containsFreeSymbol(variable.symbol)
            }
            // Root proof scope has no open assumptions.
            appearsInAssumptions = false
        }
        is AssumptionScope -> {
            appearsInPremises = hasFreeSymbolInStatementPremises(variable.symbol)
            // Includes current and all parent assumptions.
            appearsInAssumptions = hasFreeSymbolInOpenAssumptions(variable.symbol)
        }
        else -> throw IllegalArgumentException(
            "Generalization safety checks require a logic-aware derivation scope, but got '${this::class.simpleName ?: "unknown"}'.",
        )
    }
    require(!appearsInPremises) {
        "Universal generalization over '${variable.displayName}' is invalid because this variable appears in a statement premise."
    }
    require(!appearsInAssumptions) {
        "Universal generalization over '${variable.displayName}' is invalid because this variable appears in an open assumption."
    }
}

fun DerivationScope.applyMp(statement: StatementDefinition, vararg facts: DerivationFact): DerivationFact =
    applyMpInternal(this, statement.autoCall(), facts)

fun DerivationScope.applyMp(statement: StatementCall, vararg facts: DerivationFact): DerivationFact =
    applyMpInternal(this, statement, facts)

private fun applyMpInternal(
    scope: DerivationScope,
    statement: StatementCall,
    facts: Array<out DerivationFact>,
): DerivationFact {
    val resolvedStatement = inferCallFromApplyMpFacts(
        statement = statement,
        factClaims = facts.map { fact -> fact.claim },
    )
    require(resolvedStatement.premises.isEmpty()) {
        "applyMp expects a premise-free theorem, but statement '${resolvedStatement.statement.name}' has ${resolvedStatement.premises.size} declared premise(s)."
    }

    var current = scope.infer(resolvedStatement, emptyList())
    facts.forEachIndexed { index, fact ->
        val resolvedFact = scope.given(fact)
        val implication = current.claim.implicationPartsOrNull()
            ?: throw IllegalArgumentException(
                "applyMp expected an implication before applying fact ${index + 1}, but current claim is '${current.claim}'.",
            )

        require(sameProposition(resolvedFact.claim, implication.left)) {
            "applyMp fact ${index + 1} mismatch: expected '${implication.left}', but got '${resolvedFact.claim}'."
        }

        current = scope.infer(
            LogicAxioms.modusPonens(implication.left, implication.right),
            listOf(resolvedFact, current),
        )
    }

    return current
}

private fun inferCallFromApplyMpFacts(
    statement: StatementCall,
    factClaims: List<Expr>,
): StatementCall {
    require(statement.statement.premises.isEmpty()) {
        "applyMp expects a premise-free theorem, but statement '${statement.statement.name}' has ${statement.statement.premises.size} declared premise(s)."
    }

    var currentPattern = statement.conclusion
    val matches = mutableListOf<Pair<Expr, Expr>>()
    factClaims.forEachIndexed { index, factClaim ->
        val implication = currentPattern.implicationPartsOrNull()
            ?: throw IllegalArgumentException(
                "Cannot infer arguments for statement '${statement.statement.name}' from applyMp facts: expected an implication before fact ${index + 1}, but pattern is '$currentPattern'.",
            )
        matches += implication.left to factClaim
        currentPattern = implication.right
    }

    return statement.resolveFromMatches(
        matches = matches,
        sourceDescription = "applyMp facts",
    )
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
        val compiled = DeductionCompiler(
            assumption = assumptionClaim,
            steps = steps.toList(),
            target = target,
        ).compile(resultStepId)
        return compiled as? Fact
            ?: throw IllegalStateException(
                "Top-level scoped compilation must produce Fact handles, but got '${compiled::class.simpleName ?: "unknown"}'.",
            )
    }

    fun compileIntoContext(parentContext: AssumptionContext, resultStepId: Int): ScopedFact {
        val target = AssumptionContextCompilationTarget(parentContext)
        val compiled = DeductionCompiler(
            assumption = assumptionClaim,
            steps = steps.toList(),
            target = target,
        ).compile(resultStepId)
        return compiled as? ScopedFact
            ?: throw IllegalStateException(
                "Nested scoped compilation must produce ScopedFact handles, but got '${compiled::class.simpleName ?: "unknown"}'.",
            )
    }

    fun currentStepCount(): Int = steps.size

    fun requireLastDerivedStepSince(stepCountBefore: Int, blockDescription: String): ScopedFact {
        require(steps.size > stepCountBefore) {
            "$blockDescription block must contain at least one proof step."
        }
        return requireLastDerivedStep()
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

private interface CompilationTarget {
    fun givenPremise(premise: StatementPremise): DerivationFact
    fun givenOuterFact(fact: Fact): DerivationFact
    fun givenAncestorFact(fact: ScopedFact): DerivationFact
    fun infer(statement: StatementCall, premises: List<DerivationFact>): DerivationFact
    fun justify(claim: Expr, justification: Justification, premises: List<DerivationFact>): DerivationFact
    fun labelOf(fact: DerivationFact): String?
}

private class ProofBuilderCompilationTarget(
    private val builder: ProofBuilder,
) : CompilationTarget {
    override fun givenPremise(premise: StatementPremise): Fact = builder.given(premise)

    override fun givenOuterFact(fact: Fact): Fact = fact

    override fun givenAncestorFact(fact: ScopedFact): Fact {
        throw IllegalStateException("Top-level scoped compilation cannot import ancestor scoped facts.")
    }

    override fun infer(statement: StatementCall, premises: List<DerivationFact>): DerivationFact =
        builder.infer(statement, premises)

    override fun justify(claim: Expr, justification: Justification, premises: List<DerivationFact>): DerivationFact =
        builder.justify(claim, justification, premises)

    override fun labelOf(fact: DerivationFact): String? = (fact as? Fact)?.label
}

private class AssumptionContextCompilationTarget(
    private val context: AssumptionContext,
) : CompilationTarget {
    override fun givenPremise(premise: StatementPremise): ScopedFact = context.usePremise(premise)

    override fun givenOuterFact(fact: Fact): ScopedFact = context.useOuterFact(fact)

    override fun givenAncestorFact(fact: ScopedFact): ScopedFact = context.useScopedFact(fact)

    override fun infer(statement: StatementCall, premises: List<DerivationFact>): DerivationFact =
        context.infer(statement, premises.map { premise ->
            premise as? ScopedFact
                ?: throw IllegalArgumentException(
                    "Nested scoped compilation expected ScopedFact premises, but got '${premise::class.simpleName ?: "unknown"}'.",
                )
        })

    override fun justify(claim: Expr, justification: Justification, premises: List<DerivationFact>): DerivationFact =
        context.justify(claim, justification, premises.map { premise ->
            premise as? ScopedFact
                ?: throw IllegalArgumentException(
                    "Nested scoped compilation expected ScopedFact premises, but got '${premise::class.simpleName ?: "unknown"}'.",
                )
        })

    override fun labelOf(fact: DerivationFact): String? = null
}

private class DeductionCompiler(
    private val assumption: Expr,
    steps: List<ScopedStep>,
    private val target: CompilationTarget,
) {
    private val stepsByIdMap = steps.associateBy { it.id }
    private val orderedSteps = steps
    private val implicationByStepId = linkedMapOf<Int, DerivationFact>()
    private val rawByStepId = linkedMapOf<Int, DerivationFact>()

    fun compile(resultStepId: Int): DerivationFact {
        orderedSteps.forEach { step ->
            implicationByStepId[step.id] = compileImplication(step)
        }
        return requireNotNull(implicationByStepId[resultStepId]) {
            "Cannot compile scoped result step '$resultStepId': the step does not belong to this assumption block."
        }
    }

    private fun compileImplication(step: ScopedStep): DerivationFact {
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
    ): DerivationFact {
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
    ): DerivationFact {
        val support = ScopedJustificationSupportRegistry.supportFor(origin.justification)
            ?: throw IllegalArgumentException(
                "Scoped assumption compiler currently supports assumption-dependent steps only through modus ponens; justification '${origin.justification.displayName}' depends on the local assumption.",
            )

        val context = object : ScopedAssumptionDependentCompilationContext {
            override val assumption: Expr = this@DeductionCompiler.assumption
            override val conclusion: Expr = step.claim
            override val premiseStepIds: List<Int> = origin.premiseStepIds

            override fun premiseClaim(stepId: Int): Expr = stepById(stepId).claim

            override fun implication(stepId: Int): DerivationFact =
                requireNotNull(implicationByStepId[stepId]) {
                    "Missing compiled implication for premise step $stepId."
                }

            override fun infer(statement: StatementCall, vararg premises: DerivationFact): DerivationFact =
                target.infer(statement, premises.toList())

            override fun justify(claim: Expr, justification: Justification, vararg premises: DerivationFact): DerivationFact {
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

    private fun replayRaw(stepId: Int): DerivationFact {
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

    private fun bindJustificationToPremises(justification: Justification, premises: List<DerivationFact>): Justification {
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
