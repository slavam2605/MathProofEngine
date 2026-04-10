package dev.moklev.mathproof.equality.dsl

import dev.moklev.mathproof.equality.EqualityLibrary
import dev.moklev.mathproof.kernel.Fact
import dev.moklev.mathproof.kernel.ProofBuilder
import dev.moklev.mathproof.logic.AssumptionScope
import dev.moklev.mathproof.logic.ScopedFact
import dev.moklev.mathproof.logic.applyByMpChain

context(proofBuilder: ProofBuilder)
fun Fact.flipEq(): Fact =
    proofBuilder.applyByMpChain(EqualityLibrary.symmetry, this)

context(scope: AssumptionScope)
fun ScopedFact.flipEq(): ScopedFact =
    scope.applyByMpChain(EqualityLibrary.symmetry, this)
