package dev.moklev.mathproof.dsl

sealed interface Occurences {
    data object All : Occurences
    data object First : Occurences
    data object Last : Occurences
    data class Only(val zeroBasedIndices: Set<Int>) : Occurences

    companion object {
        fun Only(vararg indices: Int): Occurences = Only(indices.toSet())
    }
}
