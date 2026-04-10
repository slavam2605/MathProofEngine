package dev.moklev.mathproof.fol.dsl

import dev.moklev.mathproof.fol.FirstOrderAxioms
import dev.moklev.mathproof.kernel.Fact
import dev.moklev.mathproof.kernel.ProofBuilder
import dev.moklev.mathproof.kernel.auto
import dev.moklev.mathproof.logic.AssumptionScope
import dev.moklev.mathproof.logic.ScopedFact
import dev.moklev.mathproof.logic.applyByMpChain
import dev.moklev.mathproof.model.Expr

context(proofBuilder: ProofBuilder)
fun Fact.instantiateForall(term: Expr): Fact =
    proofBuilder.applyByMpChain(
        FirstOrderAxioms.forallInstantiation(auto(), term),
        this,
    )

context(scope: AssumptionScope)
fun ScopedFact.instantiateForall(term: Expr): ScopedFact =
    scope.applyByMpChain(
        FirstOrderAxioms.forallInstantiation(auto(), term),
        this,
    )

context(scope: AssumptionScope)
fun Fact.instantiateForall(term: Expr): ScopedFact =
    scope.given(this).instantiateForall(term)
