package dev.moklev.mathproof.model

enum class Associativity {
    LEFT,
    RIGHT,
}

object ExprPrecedence {
    const val LAMBDA = 10

    const val IMPLICATION = 30
    const val DISJUNCTION = 40
    const val CONJUNCTION = 50

    const val EQUALITY = 55
    const val COMPARISON = 56
    const val ADDITIVE = 60
    const val MULTIPLICATIVE = 70
    const val EXPONENT = 80

    const val PREFIX = 85
    const val BINDER = 85

    const val APPLICATION = 90
}

sealed interface ExprNotation {
    val symbol: String
    val precedence: Int

    data class Infix(
        override val symbol: String,
        override val precedence: Int,
        val associativity: Associativity = Associativity.LEFT,
        val surroundWithSpaces: Boolean = true,
    ) : ExprNotation

    data class Prefix(
        override val symbol: String,
        override val precedence: Int,
    ) : ExprNotation

    data class Binder(
        override val symbol: String,
        override val precedence: Int,
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
