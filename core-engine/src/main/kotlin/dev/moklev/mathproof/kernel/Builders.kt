package dev.moklev.mathproof.kernel

import dev.moklev.mathproof.model.Expr
import dev.moklev.mathproof.model.Free
import dev.moklev.mathproof.model.Lambda
import dev.moklev.mathproof.model.Sort
import dev.moklev.mathproof.model.abstract
import dev.moklev.mathproof.model.betaNormalize
import dev.moklev.mathproof.model.freshFree
import dev.moklev.mathproof.model.requireProposition

class Fact private constructor(
    val label: String,
    val claim: Expr,
    internal val proofContextId: Int?,
) {
    companion object {
        internal fun fromProof(
            label: String,
            claim: Expr,
            proofContextId: Int,
        ): Fact = Fact(label, claim, proofContextId)
    }
}

class StatementPremise private constructor(
    val index: Int,
    val label: String,
    val claim: Expr,
    internal val statementContextId: Int,
) {
    companion object {
        internal fun create(
            index: Int,
            label: String,
            claim: Expr,
            statementContextId: Int,
        ): StatementPremise = StatementPremise(index, label, claim, statementContextId)
    }
}

private object BuildContextIds {
    private var nextId = 0

    fun next(): Int {
        nextId += 1
        return nextId
    }
}

class ProofBuilder internal constructor(
    private val statementContextId: Int,
    private val proofContextId: Int = BuildContextIds.next(),
) {
    private val steps = mutableListOf<ProofStep>()
    private val labels = mutableSetOf<String>()
    private var autoStepCounter = 0

    fun given(label: String, premise: StatementPremise): Fact {
        require(premise.statementContextId == statementContextId) {
            "Premise '${premise.label}' does not belong to this statement."
        }
        return addStep(label, premise.claim, PremiseReference(premise.index))
    }

    fun given(premise: StatementPremise): Fact =
        given(nextAutoLabel(premise.label), premise)

    fun infer(label: String, statement: StatementCall, vararg premises: Fact): Fact {
        premises.forEach { premise ->
            require(premise.proofContextId == proofContextId) {
                "Fact '${premise.label}' does not belong to this proof."
            }
        }
        return addStep(
            label = label,
            claim = statement.conclusion,
            justification = StatementApplication(
                statement = statement.statement,
                arguments = statement.arguments,
                premiseLabels = premises.map { it.label },
            ),
        )
    }

    fun infer(statement: StatementCall, vararg premises: Fact): Fact =
        infer(nextAutoLabel("step"), statement, *premises)

    fun generalize(label: String, quantifier: Expr, variable: Free, source: Fact): Fact {
        require(source.proofContextId == proofContextId) {
            "Fact '${source.label}' does not belong to this proof."
        }
        val generalizedPredicate = Lambda(
            parameterSort = variable.sort,
            body = source.claim.abstract(variable),
        ).apply {
            parameterHint = variable.displayName
        }
        val generalizedClaim = quantifier(generalizedPredicate)
        return addStep(
            label = label,
            claim = generalizedClaim,
            justification = UniversalGeneralization(
                sourceLabel = source.label,
                quantifier = quantifier,
                variable = variable,
            ),
        )
    }

    fun generalize(quantifier: Expr, variable: Free, source: Fact): Fact =
        generalize(nextAutoLabel("step"), quantifier, variable, source)

    fun build(): ProofScript = ProofScript(steps.toList())

    private fun addStep(label: String, claim: Expr, justification: Justification): Fact {
        val normalizedClaim = claim.betaNormalize()
        require(labels.add(label)) { "Step label '$label' is already used in this proof." }
        steps += ProofStep(label, normalizedClaim, justification)
        return Fact.fromProof(label, normalizedClaim, proofContextId)
    }

    private fun nextAutoLabel(prefix: String): String {
        autoStepCounter += 1
        return "$prefix$autoStepCounter"
    }
}

class StatementBuilder(private val name: String) {
    private val parameters = linkedMapOf<String, StatementParameter>()
    private val premises = mutableListOf<Expr>()
    private var conclusion: Expr? = null
    private var support: StatementSupport? = null
    private var instantiationCheck: ((List<Expr>) -> Unit)? = null
    private var autoPremiseCounter = 0
    private val statementContextId = BuildContextIds.next()

    fun parameter(name: String, sort: Sort): Free {
        require(name !in parameters) { "Parameter '$name' is already defined in statement '${this.name}'." }
        val placeholder = freshFree(name, sort, namespace = "statement-$statementContextId")
        parameters[name] = StatementParameter(
            name = name,
            sort = sort,
            symbol = placeholder.symbol,
        )
        return placeholder
    }

    fun premise(label: String, claim: Expr): StatementPremise {
        val normalizedClaim = claim.betaNormalize()
        requireProposition(normalizedClaim, "Statement premise")
        premises += normalizedClaim
        return StatementPremise.create(
            index = premises.lastIndex,
            label = label,
            claim = normalizedClaim,
            statementContextId = statementContextId,
        )
    }

    fun premise(claim: Expr): StatementPremise {
        autoPremiseCounter += 1
        return premise("premise$autoPremiseCounter", claim)
    }

    fun conclusion(claim: Expr) {
        val normalizedClaim = claim.betaNormalize()
        requireProposition(normalizedClaim, "Statement conclusion")
        require(conclusion == null) { "Statement '$name' already has a conclusion." }
        conclusion = normalizedClaim
    }

    fun assumed(note: String? = null) {
        require(support == null) { "Statement '$name' already has support defined." }
        support = AssumedTrue(note)
    }

    fun proof(block: ProofBuilder.() -> Unit) {
        require(support == null) { "Statement '$name' already has support defined." }
        support = ProofProvided(ProofBuilder(statementContextId).apply(block).build())
    }

    fun instantiationCheck(check: (List<Expr>) -> Unit) {
        require(instantiationCheck == null) { "Statement '$name' already has an instantiation check defined." }
        instantiationCheck = check
    }

    fun build(): StatementDefinition = StatementDefinition(
        name = name,
        parameters = parameters.values.toList(),
        premises = premises.toList(),
        conclusion = requireNotNull(conclusion) { "Statement '$name' needs a conclusion." },
        support = requireNotNull(support) { "Statement '$name' needs support metadata such as assumed()." },
        instantiationCheck = instantiationCheck,
    )
}
