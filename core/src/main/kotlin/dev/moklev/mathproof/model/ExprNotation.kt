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

fun interface ExprAtomProvider {
    fun atomFor(expr: Expr): String?
}

object ExprNotationRegistry {
    private val notationProviders = mutableListOf<ExprNotationProvider>()
    private val atomProviders = mutableListOf<ExprAtomProvider>()

    @Synchronized
    fun register(provider: ExprNotationProvider) {
        notationProviders += provider
    }

    @Synchronized
    fun register(provider: ExprAtomProvider) {
        atomProviders += provider
    }

    @Synchronized
    internal fun notationFor(head: Expr, arguments: List<Expr>): ExprNotation? =
        notationProviders.firstNotNullOfOrNull { it.notationFor(head, arguments) }

    @Synchronized
    internal fun atomFor(expr: Expr): String? =
        atomProviders.firstNotNullOfOrNull { it.atomFor(expr) }
}
