package dev.moklev.mathproof.model

enum class Associativity {
    LEFT,
    RIGHT,
}

sealed interface ExprNotation {
    data class Infix(
        val symbol: String,
        val precedence: Int,
        val associativity: Associativity = Associativity.LEFT,
    ) : ExprNotation

    data class Prefix(
        val symbol: String,
        val precedence: Int,
    ) : ExprNotation
}

fun interface ExprNotationProvider {
    fun notationFor(head: Expr, arguments: List<Expr>): ExprNotation?
}

object ExprNotationRegistry {
    private val providers = mutableListOf<ExprNotationProvider>()

    @Synchronized
    fun register(provider: ExprNotationProvider) {
        providers += provider
    }

    @Synchronized
    internal fun notationFor(head: Expr, arguments: List<Expr>): ExprNotation? =
        providers.firstNotNullOfOrNull { it.notationFor(head, arguments) }
}
