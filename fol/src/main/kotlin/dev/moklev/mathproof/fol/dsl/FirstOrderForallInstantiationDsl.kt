package dev.moklev.mathproof.fol.dsl

import dev.moklev.mathproof.fol.FirstOrderAxioms
import dev.moklev.mathproof.kernel.DerivationFact
import dev.moklev.mathproof.kernel.DerivationScope
import dev.moklev.mathproof.kernel.auto
import dev.moklev.mathproof.logic.applyMp
import dev.moklev.mathproof.model.Expr

context(scope: DerivationScope)
fun DerivationFact.instantiateForall(term: Expr): DerivationFact =
    scope.applyMp(
        FirstOrderAxioms.forallInstantiation(auto(), term),
        this,
    )
