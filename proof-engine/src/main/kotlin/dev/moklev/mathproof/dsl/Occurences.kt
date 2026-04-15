package dev.moklev.mathproof.dsl

sealed interface ExprPathStep {
    data object Function : ExprPathStep
    data object Argument : ExprPathStep
    data object Body : ExprPathStep
    data object BinLeft : ExprPathStep
    data object BinRight : ExprPathStep
}

@JvmInline
value class ExprPath private constructor(val steps: List<ExprPathStep>) {
    companion object {
        val Root: ExprPath = ExprPath(emptyList())
        fun of(vararg steps: ExprPathStep): ExprPath = ExprPath(canonicalize(steps.toList()))

        private fun canonicalize(steps: List<ExprPathStep>): List<ExprPathStep> =
            steps.flatMap { step -> step.expand() }
    }

    operator fun div(step: ExprPathStep): ExprPath = ExprPath(steps + step.expand())
}

private fun ExprPathStep.expand(): List<ExprPathStep> = when (this) {
    ExprPathStep.Function -> listOf(ExprPathStep.Function)
    ExprPathStep.Argument -> listOf(ExprPathStep.Argument)
    ExprPathStep.Body -> listOf(ExprPathStep.Body)
    ExprPathStep.BinLeft -> listOf(ExprPathStep.Function, ExprPathStep.Argument)
    ExprPathStep.BinRight -> listOf(ExprPathStep.Argument)
}

sealed interface Occurences {
    data object All : Occurences
    data object First : Occurences
    data object Last : Occurences
    data class Only(val zeroBasedIndices: Set<Int>) : Occurences
    data class Path(val path: ExprPath) : Occurences

    companion object {
        fun Only(vararg indices: Int): Occurences = Only(indices.toSet())
    }
}
