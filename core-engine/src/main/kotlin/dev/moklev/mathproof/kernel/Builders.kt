package dev.moklev.mathproof.kernel

import dev.moklev.mathproof.model.Expr
import dev.moklev.mathproof.model.Free
import dev.moklev.mathproof.model.Sort
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
    private val statementParameterNames: Set<String> = emptySet(),
    private val statementPremises: List<Expr> = emptyList(),
    private val proofContextId: Int = BuildContextIds.next(),
) {
    private val steps = mutableListOf<ProofStep>()
    private val labels = mutableSetOf<String>()
    private val arbitraryVariablesBySymbol = linkedMapOf<String, ArbitraryVariable>()
    private val arbitraryDisplayNames = mutableSetOf<String>()
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
        requireFactsBelongToThisProof(*premises)
        val resolvedStatement = statement.resolveFromPremises(premises.map { premise -> premise.claim })
        return addStep(
            label = label,
            claim = resolvedStatement.conclusion,
            justification = StatementApplication(
                statement = resolvedStatement.statement,
                arguments = resolvedStatement.arguments,
                premiseLabels = premises.map { it.label },
            ),
        )
    }

    fun infer(statement: StatementCall, vararg premises: Fact): Fact =
        infer(nextAutoLabel("step"), statement, *premises)

    fun infer(
        label: String,
        statement: StatementDefinition,
        vararg premises: Fact,
    ): Fact = infer(label, statement.autoCall(), *premises)

    fun infer(
        statement: StatementDefinition,
        vararg premises: Fact,
    ): Fact = infer(nextAutoLabel("step"), statement, *premises)

    fun justify(label: String, claim: Expr, justification: Justification, vararg facts: Fact): Fact {
        requireFactsBelongToThisProof(*facts)
        return addStep(label, claim, justification)
    }

    fun justify(claim: Expr, justification: Justification, vararg facts: Fact): Fact =
        justify(nextAutoLabel("step"), claim, justification, *facts)

    fun todoAssume(
        claim: Expr,
        note: String? = null,
    ): Fact = todoAssume(
        label = nextAutoLabel("todo"),
        claim = claim,
        note = note,
    )

    fun todoAssume(
        label: String,
        claim: Expr,
        note: String? = null,
    ): Fact {
        val normalizedClaim = claim.betaNormalize()
        requireProposition(normalizedClaim, "todoAssume claim")
        return addStep(
            label = label,
            claim = normalizedClaim,
            justification = TodoAssumption(note),
        )
    }

    fun arbitrary(name: String, sort: Sort): Free {
        require(name !in statementParameterNames) {
            "Arbitrary variable '$name' conflicts with statement parameter '$name'. Choose a distinct name."
        }
        require(arbitraryDisplayNames.add(name)) {
            "Arbitrary variable '$name' is already declared in this proof."
        }

        val variable = freshFree(
            displayName = name,
            sort = sort,
            namespace = "proof-$proofContextId-arbitrary",
        )
        arbitraryVariablesBySymbol[variable.symbol] = ArbitraryVariable(
            symbol = variable.symbol,
            displayName = variable.displayName,
            sort = variable.sort,
        )
        return variable
    }

    fun build(): ProofScript = ProofScript(
        steps = steps.toList(),
        arbitraryVariables = arbitraryVariablesBySymbol.values.toList(),
    )

    fun declaredPremises(): List<Expr> = statementPremises.toList()

    private fun addStep(label: String, claim: Expr, justification: Justification): Fact {
        val normalizedClaim = claim.betaNormalize()
        require(labels.add(label)) { "Step label '$label' is already used in this proof." }
        steps += ProofStep(label, normalizedClaim, justification)
        return Fact.fromProof(label, normalizedClaim, proofContextId)
    }

    private fun requireFactsBelongToThisProof(vararg facts: Fact) {
        facts.forEach { fact ->
            require(fact.proofContextId == proofContextId) {
                "Fact '${fact.label}' does not belong to this proof."
            }
        }
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
        support = ProofProvided(
            ProofBuilder(
                statementContextId = statementContextId,
                statementParameterNames = parameters.keys.toSet(),
                statementPremises = premises.toList(),
            ).apply(block).build(),
        )
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
