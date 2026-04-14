package dev.moklev.mathproof.equality.dsl

import dev.moklev.mathproof.equality.EqualityLibrary
import dev.moklev.mathproof.kernel.DerivationFact
import dev.moklev.mathproof.kernel.DerivationScope
import dev.moklev.mathproof.logic.applyMp

context(scope: DerivationScope)
fun DerivationFact.flipEq(): DerivationFact =
    scope.applyMp(EqualityLibrary.symmetry, this)
