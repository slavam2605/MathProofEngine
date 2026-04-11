package dev.moklev.mathproof.core

import dev.moklev.mathproof.model.Free
import dev.moklev.mathproof.model.Sort

class SymbolRegistry private constructor() {
    private val registeredByCanonicalId = linkedMapOf<String, Free>()

    val root: SymbolNamespace = SymbolNamespace(this, emptyList())

    fun lookup(canonicalId: String): Free? = registeredByCanonicalId[canonicalId]

    internal fun registerNamed(
        namespaceSegments: List<String>,
        name: String,
        sort: Sort,
        displayName: String,
    ): Free {
        val canonicalId = canonicalId(namespaceSegments, name)
        return registerCanonical(canonicalId, sort, displayName)
    }

    private fun registerCanonical(
        canonicalId: String,
        sort: Sort,
        displayName: String,
    ): Free {
        require(canonicalId !in registeredByCanonicalId) {
            "Symbol '$canonicalId' is already registered. Re-declaration is forbidden."
        }
        val symbol = Free(
            symbol = canonicalId,
            sort = sort,
            displayName = displayName,
        )
        registeredByCanonicalId[canonicalId] = symbol
        return symbol
    }

    internal fun ensureValidSegment(segment: String) {
        require(segment.isNotBlank()) { "Namespace segments must be non-blank." }
        require('.' !in segment) { "Namespace segment '$segment' must not contain '.'." }
        require(segment.none(Char::isWhitespace)) {
            "Namespace segment '$segment' must not contain whitespace."
        }
    }

    private fun canonicalId(namespaceSegments: List<String>, name: String): String {
        ensureValidSegment(name)
        namespaceSegments.forEach(::ensureValidSegment)
        return (namespaceSegments + name).joinToString(".")
    }

    companion object {
        val global: SymbolRegistry = SymbolRegistry()
    }
}

class SymbolNamespace internal constructor(
    private val registry: SymbolRegistry,
    private val segments: List<String>,
) {
    fun namespace(name: String): SymbolNamespace {
        registry.ensureValidSegment(name)
        return SymbolNamespace(
            registry = registry,
            segments = segments + name,
        )
    }

    fun free(
        name: String,
        sort: Sort,
        displayName: String = name,
    ): Free = registry.registerNamed(segments, name, sort, displayName)

    fun constant(
        name: String,
        sort: Sort,
        displayName: String = name,
    ): Free = free(name, sort, displayName)

    fun function(
        name: String,
        vararg argumentSorts: Sort,
        returns: Sort,
        displayName: String = name,
    ): Free = constant(
        name = name,
        sort = functionSort(*argumentSorts, returns = returns),
        displayName = displayName,
    )
}
