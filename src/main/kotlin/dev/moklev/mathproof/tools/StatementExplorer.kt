package dev.moklev.mathproof.tools

import dev.moklev.mathproof.kernel.AssumedTrue
import dev.moklev.mathproof.kernel.ProofProvided
import dev.moklev.mathproof.kernel.StatementDefinition
import dev.moklev.mathproof.kernel.StatementApplication
import dev.moklev.mathproof.kernel.TodoAssumption
import java.io.File
import java.lang.reflect.Field
import java.lang.reflect.Method
import java.lang.reflect.Modifier
import java.util.IdentityHashMap
import java.util.jar.JarFile
import org.jline.reader.EndOfFileException
import org.jline.reader.LineReader
import org.jline.reader.LineReaderBuilder
import org.jline.reader.UserInterruptException
import org.jline.reader.impl.DefaultParser
import org.jline.reader.impl.completer.AggregateCompleter
import org.jline.reader.impl.completer.ArgumentCompleter
import org.jline.reader.impl.completer.NullCompleter
import org.jline.reader.impl.completer.StringsCompleter
import org.jline.terminal.TerminalBuilder

fun main(args: Array<String>) {
    val colorMode = parseColorMode(args) ?: return
    val explorer = StatementExplorer(
        packagePrefix = "dev.moklev.mathproof",
        classLoader = Thread.currentThread().contextClassLoader ?: StatementExplorer::class.java.classLoader,
        colorMode = colorMode,
    )
    explorer.run()
}

private class StatementExplorer(
    private val packagePrefix: String,
    private val classLoader: ClassLoader,
    private val colorMode: ColorMode,
) {
    private var entries: List<StatementEntry> = discoverStatements()
    private val filters = ExplorerFilters()
    private var renderStyle: RenderStyle = RenderStyle(ansiEnabled = false)

    fun run() {
        val lineReader = buildLineReader()
        renderStyle = RenderStyle.detect(lineReader, colorMode)
        println(renderStyle.summary("Discovered ${entries.size} statement entries."))
        println("Type 'help' to see commands.")

        while (true) {
            val line = try {
                lineReader.readLine("statement-explorer> ").trim()
            } catch (_: UserInterruptException) {
                continue
            } catch (_: EndOfFileException) {
                break
            }
            if (line.isEmpty()) {
                continue
            }

            val command = line.substringBefore(' ').lowercase()
            val args = line.substringAfter(' ', missingDelimiterValue = "").trim()

            when (command) {
                "help" -> printHelp()
                "list" -> listStatements()
                "find" -> findStatements(args)
                "depends" -> printDependencies(args)
                "axioms" -> printAxioms(args)
                "filters" -> printFilters()
                "clear" -> if (args.isEmpty()) {
                    filters.clearAll()
                    println("Cleared all filters.")
                } else {
                    clearFilter(args)
                }
                "refresh" -> {
                    entries = discoverStatements()
                    println("Refreshed. Discovered ${entries.size} statement entries.")
                }
                "exit", "quit" -> return
                "show" -> showStatement(args)
                "set" -> setFilter(args)
                else -> println("Unknown command '$line'. Type 'help'.")
            }
        }
    }

    private fun buildLineReader(): LineReader {
        val commands = StringsCompleter("help", "list", "find", "depends", "axioms", "filters", "set", "clear", "refresh", "show", "quit", "exit")
        val filterNames = StringsCompleter("class-glob", "class-regex", "text-regex", "conclusion-regex")

        val completer = AggregateCompleter(
            ArgumentCompleter(commands, NullCompleter.INSTANCE),
            ArgumentCompleter(StringsCompleter("set"), filterNames, NullCompleter.INSTANCE),
            ArgumentCompleter(StringsCompleter("clear"), filterNames, NullCompleter.INSTANCE),
            ArgumentCompleter(StringsCompleter("find"), NullCompleter.INSTANCE),
            ArgumentCompleter(
                StringsCompleter("depends"),
                NullCompleter.INSTANCE,
                StringsCompleter("--max-depth", "-d", "--flat", "--transitive"),
                NullCompleter.INSTANCE,
            ),
            ArgumentCompleter(StringsCompleter("show"), NullCompleter.INSTANCE),
        )

        val terminal = TerminalBuilder.builder()
            .system(true)
            .build()

        return LineReaderBuilder.builder()
            .terminal(terminal)
            .parser(DefaultParser())
            .completer(completer)
            .build()
    }

    private fun printHelp() {
        println(
            """
            Commands:
              list
                List statements grouped by holder class and matching active filters.
              find <regex>
                Temporarily add a text-regex for this command only and list matching statements.
              depends <regex> [--max-depth <n>]
                Print recursive statement dependencies for matching Kotlin names (for example: NatAxioms.induction).
                Use --max-depth (or -d) to limit recursion depth; omitted means unlimited.
                Use --flat (or --transitive) to flatten output to one transitive dependency layer.
              axioms
                List trusted statements (assumed/trusted support) and separately list todoAssume() proof facts.
              show <index|holder.property>
                Show the full rendered view for one statement.
              filters
                Show active filters and current match count.
              set class-glob <glob[,glob...]>
                Set class-name glob filter. Example: Nat*,Logic*
              set class-regex <regex>
                Set class-name regex filter. Example: Nat.*|Logic.*
              set text-regex <regex>
                Set rendered-view regex filter. Example: .*succ\(.* 
              set conclusion-regex <regex>
                Set regex filter over sequent text only: premises ⊢ conclusion.
              clear
                Clear all filters.
              clear class-glob | class-regex | text-regex | conclusion-regex
                Clear one filter.
              refresh
                Re-discover statements from the runtime classpath.
              --color=auto|always|never
                Launch option to control ANSI styling (default: auto).
              quit | exit

            Notes:
              - Field entries come from properties with backing fields (for example: val x = statement(...)).
              - Function entries come from object methods returning StatementDefinition by substituting
                available singleton objects compatible with parameter types.
              - Statement-returning property getters (including inherited ones) are included.
              - Class filters match both simple and fully qualified class name.
            """.trimIndent()
        )
    }

    private fun listStatements() {
        val filtered = filteredEntries()
        printStatementsResult(filtered)
    }

    private fun printAxioms(args: String) {
        if (args.isNotBlank()) {
            println("Usage: axioms")
            return
        }
        val filtered = filteredEntries()
        printActiveFilters()

        val trustedEntries = filtered
            .filter { entry -> entry.statement.support !is ProofProvided }
            .sortedWith(compareBy(StatementEntry::holderSimpleName, StatementEntry::memberName))

        if (trustedEntries.isEmpty()) {
            println("No trusted statements found.")
        } else {
            println(renderStyle.classHeader("Trusted statements:"))
            val grouped = trustedEntries.groupBy { entry -> entry.holderSimpleName }
            grouped.toSortedMap().forEach { (holder, entriesByHolder) ->
                println("$holder:")
                entriesByHolder.forEach { entry ->
                    val support = entry.statement.support
                    val detailsSuffix = when (support) {
                        is AssumedTrue -> support.note?.let { note -> " ${renderStyle.muted("// $note")}" }.orEmpty()
                        else -> " ${renderStyle.muted("// support=${support::class.simpleName ?: "unknown"}")}"
                    }
                    println("  - ${renderStyle.signature(renderedSignature(entry))} [${entry.statement.name}]$detailsSuffix")
                }
                println()
            }
            println(renderStyle.summary("Matched ${trustedEntries.size} trusted statement(s) in ${grouped.size} class(es)."))
        }

        val todoFacts = filtered
            .sortedWith(compareBy(StatementEntry::holderSimpleName, StatementEntry::memberName))
            .flatMap { entry ->
                val proof = (entry.statement.support as? ProofProvided)?.proof ?: return@flatMap emptyList()
                proof.steps.mapNotNull { step ->
                    val todo = step.justification as? TodoAssumption ?: return@mapNotNull null
                    TodoFact(
                        entry = entry,
                        stepLabel = step.label,
                        claimText = step.claim.toString(),
                        note = todo.note,
                    )
                }
            }

        if (todoFacts.isNotEmpty()) {
            println()
            println(renderStyle.classHeader("todoAssume() facts:"))
            val groupedByStatement = todoFacts.groupBy { todo ->
                "${todo.entry.holderSimpleName}.${todo.entry.memberName}"
            }.toSortedMap()

            groupedByStatement.forEach { (_, facts) ->
                val statementEntry = facts.first().entry
                println("${statementEntry.holderSimpleName}.${statementEntry.memberName} [${statementEntry.statement.name}]")
                facts.forEach { fact ->
                    val noteSuffix = fact.note?.let { note -> " ${renderStyle.muted("// $note")}" }.orEmpty()
                    println("  - ${fact.stepLabel}: ${fact.claimText}$noteSuffix")
                }
                println()
            }
            println(renderStyle.summary("Found ${todoFacts.size} todoAssume fact(s) in ${groupedByStatement.size} statement(s)."))
        }
    }

    private fun findStatements(args: String) {
        val raw = args.trim()
        if (raw.isEmpty()) {
            println("Usage: find <regex>")
            return
        }
        val temporaryTextRegex = runCatching { Regex(raw) }
        if (temporaryTextRegex.isFailure) {
            println("Invalid find regex: ${temporaryTextRegex.exceptionOrNull()?.message}")
            return
        }
        val filtered = filteredEntries(additionalTextRegex = temporaryTextRegex.getOrThrow())
        printStatementsResult(filtered, temporaryTextRegexRaw = raw)
    }

    private fun printDependencies(args: String) {
        val options = parseDependsArgs(args) ?: return

        val roots = filteredEntries().filter { entry ->
            val simpleRef = "${entry.holderSimpleName}.${entry.memberName}"
            val fqRef = "${entry.holderClassName}.${entry.memberName}"
            options.nameRegex.containsMatchIn(simpleRef) || options.nameRegex.containsMatchIn(fqRef)
        }

        printActiveFilters()
        if (roots.isEmpty()) {
            println("No statements matched depends regex '${options.regexRaw}'.")
            return
        }

        val lookup = StatementLookup.build(entries)
        roots.forEachIndexed { index, root ->
            val rootRef = "${root.holderSimpleName}.${root.memberName}"
            println(renderStyle.classHeader(rootRef))
            println("  id: ${root.statement.name}")
            val depthSuffix = options.maxDepth?.let { value -> ", max-depth=$value" }.orEmpty()
            val modeLabel = if (options.flattenTransitive) "flat, transitive" else "tree"
            println("  dependencies ($modeLabel$depthSuffix):")
            if (options.flattenTransitive) {
                val dependencies = collectTransitiveDependencies(
                    root = root.statement,
                    lookup = lookup,
                    maxDepth = options.maxDepth,
                )
                if (dependencies.isEmpty()) {
                    println("    - none")
                } else {
                    dependencies.forEachIndexed { dependencyIndex, dependency ->
                        val branch = if (dependencyIndex == dependencies.lastIndex) "└─ " else "├─ "
                        println("    $branch${dependencyLabel(dependency, lookup)}")
                    }
                }
            } else {
                val dependencies = directDependencies(root.statement, lookup)
                if (dependencies.isEmpty()) {
                    println("    - none")
                } else if (options.maxDepth == 0) {
                    println("    - omitted (max-depth=0)")
                } else {
                    dependencies.forEachIndexed { dependencyIndex, dependency ->
                        val isLast = dependencyIndex == dependencies.lastIndex
                        printDependencyNode(
                            statement = dependency,
                            lookup = lookup,
                            ancestorFingerprints = listOf(statementFingerprint(root.statement)),
                            prefix = "    ",
                            isLast = isLast,
                            currentDepth = 1,
                            maxDepth = options.maxDepth,
                        )
                    }
                }
            }
            if (index != roots.lastIndex) {
                println()
            }
        }
    }

    private fun parseDependsArgs(args: String): DependsOptions? {
        val tokens = args.trim().split(Regex("\\s+")).filter { token -> token.isNotEmpty() }
        if (tokens.isEmpty()) {
            println("Usage: depends <regex> [--max-depth <n>] [--flat]")
            return null
        }

        val regexRaw = tokens.first()
        val nameRegex = runCatching { Regex(regexRaw) }
        if (nameRegex.isFailure) {
            println("Invalid depends regex: ${nameRegex.exceptionOrNull()?.message}")
            return null
        }

        var maxDepth: Int? = null
        var flattenTransitive = false
        var index = 1
        while (index < tokens.size) {
            val option = tokens[index]
            when (option) {
                "--max-depth", "-d" -> {
                    if (index + 1 >= tokens.size) {
                        println("Missing value for '$option'. Usage: depends <regex> [--max-depth <n>] [--flat]")
                        return null
                    }
                    val depthRaw = tokens[index + 1]
                    val depth = depthRaw.toIntOrNull()
                    if (depth == null || depth < 0) {
                        println("Invalid max depth '$depthRaw'. Expected non-negative integer.")
                        return null
                    }
                    maxDepth = depth
                    index += 2
                }
                "--flat", "--transitive" -> {
                    flattenTransitive = true
                    index += 1
                }
                else -> {
                    println("Unknown depends option '$option'. Usage: depends <regex> [--max-depth <n>] [--flat]")
                    return null
                }
            }
        }

        return DependsOptions(
            regexRaw = regexRaw,
            nameRegex = nameRegex.getOrThrow(),
            maxDepth = maxDepth,
            flattenTransitive = flattenTransitive,
        )
    }

    private fun printStatementsResult(
        filtered: List<StatementEntry>,
        temporaryTextRegexRaw: String? = null,
    ) {
        printActiveFilters(temporaryTextRegexRaw)
        if (filtered.isEmpty()) {
            println("No statements matched.")
            return
        }

        val groups = filtered.groupBy { entry -> entry.holderSimpleName }
        val sortedGroups = groups.toSortedMap().entries.toList()
        sortedGroups.forEachIndexed { groupIndex, (holder, entriesByHolder) ->
            println(renderStyle.classHeader("$holder:"))
            entriesByHolder.forEach { entry ->
                val renderedParameters = entry.statement.parameters.joinToString(", ") { parameter ->
                    "${parameter.name}: ${parameter.sort}"
                }
                val signature = "${entry.memberName}($renderedParameters)"
                val prefix = renderStyle.muted("  -")
                if (entry.statement.premises.isNotEmpty()) {
                    val renderedPremises = entry.statement.premises.joinToString(", ") { premise -> premise.toString() }
                    println(
                        "$prefix ${renderStyle.signature(signature)} ${renderStyle.muted("=")} ${renderStyle.premises(renderedPremises)} ${renderStyle.turnstile()} ${renderStyle.conclusion(entry.statement.conclusion.toString())}.",
                    )
                } else {
                    println("$prefix ${renderStyle.signature(signature)} ${renderStyle.muted("=")} ${renderStyle.conclusion(entry.statement.conclusion.toString())}.")
                }
            }
            if (groupIndex != sortedGroups.lastIndex) {
                println()
            }
        }
        println()
        println(renderStyle.summary("Matched ${filtered.size} statement(s) in ${groups.size} class(es)."))
    }

    private fun renderedSignature(entry: StatementEntry): String {
        val renderedParameters = entry.statement.parameters.joinToString(", ") { parameter ->
            "${parameter.name}: ${parameter.sort}"
        }
        return "${entry.memberName}($renderedParameters)"
    }

    private fun printActiveFilters(temporaryTextRegexRaw: String? = null) {
        val activeFilters = buildList {
            filters.classGlobRaw?.let { raw -> add("class-glob=$raw") }
            filters.classRegexRaw?.let { raw -> add("class-regex=$raw") }
            filters.textRegexRaw?.let { raw -> add("text-regex=$raw") }
            filters.conclusionRegexRaw?.let { raw -> add("conclusion-regex=$raw") }
            temporaryTextRegexRaw?.let { raw -> add("find-text-regex=$raw") }
        }
        if (activeFilters.isEmpty()) {
            return
        }
        println(renderStyle.summary("Active filters: ${activeFilters.joinToString("; ")}"))
        println()
    }

    private fun showStatement(indexOrRefRaw: String) {
        val filtered = filteredEntries()
        val input = indexOrRefRaw.trim()
        if (input.isEmpty()) {
            println("Usage: show <index|holder.property>")
            return
        }

        val selected = input.toIntOrNull()?.let { index ->
            if (index <= 0 || index > filtered.size) {
                null
            } else {
                filtered[index - 1]
            }
        } ?: run {
            val matches = filtered.filter { entry ->
                "${entry.holderSimpleName}.${entry.memberName}" == input ||
                    "${entry.holderClassName}.${entry.memberName}" == input
            }
            when {
                matches.isEmpty() -> null
                matches.size == 1 -> matches.single()
                else -> {
                    println("Ambiguous reference '$input'. Use fully qualified class name.")
                    return
                }
            }
        }

        if (selected == null) {
            println("Statement '$input' not found in current filtered set.")
            return
        }
        println(selected.renderedView)
    }

    private fun printFilters() {
        println("class-glob: ${filters.classGlobRaw ?: "<none>"}")
        println("class-regex: ${filters.classRegexRaw ?: "<none>"}")
        println("text-regex: ${filters.textRegexRaw ?: "<none>"}")
        println("conclusion-regex: ${filters.conclusionRegexRaw ?: "<none>"}")
        println("matches: ${filteredEntries().size}/${entries.size}")
    }

    private fun setFilter(args: String) {
        when {
            args.startsWith("class-glob ") -> {
                val raw = args.removePrefix("class-glob").trim()
                if (raw.isEmpty()) {
                    println("Usage: set class-glob <glob[,glob...]>")
                    return
                }
                val compiled = runCatching { compileGlobPatterns(raw) }
                if (compiled.isFailure) {
                    println("Invalid glob filter: ${compiled.exceptionOrNull()?.message}")
                    return
                }
                filters.classGlobRaw = raw
                filters.classGlob = compiled.getOrThrow()
                println("Set class-glob filter.")
            }
            args.startsWith("class-regex ") -> {
                val raw = args.removePrefix("class-regex").trim()
                if (raw.isEmpty()) {
                    println("Usage: set class-regex <regex>")
                    return
                }
                val compiled = runCatching { Regex(raw) }
                if (compiled.isFailure) {
                    println("Invalid class regex: ${compiled.exceptionOrNull()?.message}")
                    return
                }
                filters.classRegexRaw = raw
                filters.classRegex = compiled.getOrThrow()
                println("Set class-regex filter.")
            }
            args.startsWith("text-regex ") -> {
                val raw = args.removePrefix("text-regex").trim()
                if (raw.isEmpty()) {
                    println("Usage: set text-regex <regex>")
                    return
                }
                val compiled = runCatching { Regex(raw) }
                if (compiled.isFailure) {
                    println("Invalid text regex: ${compiled.exceptionOrNull()?.message}")
                    return
                }
                filters.textRegexRaw = raw
                filters.textRegex = compiled.getOrThrow()
                println("Set text-regex filter.")
            }
            args.startsWith("conclusion-regex ") -> {
                val raw = args.removePrefix("conclusion-regex").trim()
                if (raw.isEmpty()) {
                    println("Usage: set conclusion-regex <regex>")
                    return
                }
                val compiled = runCatching { Regex(raw) }
                if (compiled.isFailure) {
                    println("Invalid conclusion regex: ${compiled.exceptionOrNull()?.message}")
                    return
                }
                filters.conclusionRegexRaw = raw
                filters.conclusionRegex = compiled.getOrThrow()
                println("Set conclusion-regex filter.")
            }
            else -> println("Unknown filter setting. Type 'help'.")
        }
    }

    private fun clearFilter(args: String) {
        when (args.lowercase()) {
            "class-glob" -> {
                filters.classGlobRaw = null
                filters.classGlob = null
                println("Cleared class-glob.")
            }
            "class-regex" -> {
                filters.classRegexRaw = null
                filters.classRegex = null
                println("Cleared class-regex.")
            }
            "text-regex" -> {
                filters.textRegexRaw = null
                filters.textRegex = null
                println("Cleared text-regex.")
            }
            "conclusion-regex" -> {
                filters.conclusionRegexRaw = null
                filters.conclusionRegex = null
                println("Cleared conclusion-regex.")
            }
            else -> println("Unknown filter '$args'. Type 'help'.")
        }
    }

    private fun filteredEntries(additionalTextRegex: Regex? = null): List<StatementEntry> =
        entries.filter { entry ->
            filters.matchesClass(entry.holderSimpleName, entry.holderClassName) &&
                filters.matchesText(entry.renderedView) &&
                (additionalTextRegex?.containsMatchIn(entry.renderedView) ?: true) &&
                filters.matchesConclusion(entry.sequentText)
        }

    private fun printDependencyNode(
        statement: StatementDefinition,
        lookup: StatementLookup,
        ancestorFingerprints: List<String>,
        prefix: String,
        isLast: Boolean,
        currentDepth: Int,
        maxDepth: Int?,
    ) {
        val branch = if (isLast) "└─ " else "├─ "
        val fingerprint = statementFingerprint(statement)
        val cycle = ancestorFingerprints.any { ancestorFingerprint -> ancestorFingerprint == fingerprint }
        if (cycle) {
            println("$prefix$branch${dependencyLabel(statement, lookup)} ${renderStyle.summary("[cycle]")}")
            return
        }

        println("$prefix$branch${dependencyLabel(statement, lookup)}")
        val children = directDependencies(statement, lookup)
        if (children.isEmpty()) {
            return
        }
        if (maxDepth != null && currentDepth >= maxDepth) {
            return
        }

        val childPrefix = prefix + if (isLast) "   " else "│  "
        children.forEachIndexed { childIndex, child ->
            val childIsLast = childIndex == children.lastIndex
            printDependencyNode(
                statement = child,
                lookup = lookup,
                ancestorFingerprints = ancestorFingerprints + fingerprint,
                prefix = childPrefix,
                isLast = childIsLast,
                currentDepth = currentDepth + 1,
                maxDepth = maxDepth,
            )
        }
    }

    private fun dependencyLabel(
        statement: StatementDefinition,
        lookup: StatementLookup,
    ): String {
        val knownEntry = lookup.resolve(statement)
        return if (knownEntry != null) {
            "${knownEntry.holderSimpleName}.${knownEntry.memberName} [${statement.name}]"
        } else {
            "[${statement.name}]"
        }
    }

    private fun directDependencies(
        statement: StatementDefinition,
        lookup: StatementLookup,
    ): List<StatementDefinition> {
        val proof = (statement.support as? ProofProvided)?.proof ?: return emptyList()
        val dependenciesByFingerprint = linkedMapOf<String, StatementDefinition>()
        proof.steps.forEach { step ->
            val dependency = (step.justification as? StatementApplication)?.statement ?: return@forEach
            val fingerprint = statementFingerprint(dependency)
            dependenciesByFingerprint.putIfAbsent(fingerprint, dependency)
        }
        return dependenciesByFingerprint.values.sortedWith(dependencyComparator(lookup))
    }

    private fun dependencySortKey(
        statement: StatementDefinition,
        lookup: StatementLookup,
    ): String {
        val knownEntry = lookup.resolve(statement)
        return if (knownEntry != null) {
            "${knownEntry.holderSimpleName}.${knownEntry.memberName}"
        } else {
            statement.name
        }
    }

    private fun dependencyComparator(lookup: StatementLookup): Comparator<StatementDefinition> =
        compareBy<StatementDefinition>(
            { dependencySortKey(it, lookup).lowercase() },
            { it.name.lowercase() },
        )

    private fun collectTransitiveDependencies(
        root: StatementDefinition,
        lookup: StatementLookup,
        maxDepth: Int?,
    ): List<StatementDefinition> {
        if (maxDepth == 0) {
            return emptyList()
        }

        val rootFingerprint = statementFingerprint(root)
        val discoveredByFingerprint = linkedMapOf<String, StatementDefinition>()
        val queue = ArrayDeque<Pair<StatementDefinition, Int>>()

        directDependencies(root, lookup).forEach { dependency ->
            val fingerprint = statementFingerprint(dependency)
            if (fingerprint == rootFingerprint) {
                return@forEach
            }
            if (discoveredByFingerprint.putIfAbsent(fingerprint, dependency) == null) {
                queue.addLast(dependency to 1)
            }
        }

        while (queue.isNotEmpty()) {
            val (current, depth) = queue.removeFirst()
            if (maxDepth != null && depth >= maxDepth) {
                continue
            }

            directDependencies(current, lookup).forEach { dependency ->
                val fingerprint = statementFingerprint(dependency)
                if (fingerprint == rootFingerprint) {
                    return@forEach
                }
                if (discoveredByFingerprint.putIfAbsent(fingerprint, dependency) == null) {
                    queue.addLast(dependency to (depth + 1))
                }
            }
        }

        return discoveredByFingerprint.values.sortedWith(dependencyComparator(lookup))
    }

    private fun discoverStatements(): List<StatementEntry> {
        val classNames = discoverClassNames(packagePrefix)
        val objectHolders = classNames
            .mapNotNull { className -> discoverObjectHolder(className, classLoader) }
            .sortedBy(ObjectHolder::className)

        val discovered = mutableListOf<StatementEntry>()

        objectHolders.forEach { holder ->
            discovered += discoverFieldEntries(holder)
        }
        objectHolders.forEach { holder ->
            discovered += discoverFunctionEntries(holder, objectHolders)
        }

        return discovered
            .distinctBy(StatementEntry::uniqueId)
            .sortedWith(compareBy(StatementEntry::holderClassName, StatementEntry::memberName, { it.statement.name }))
    }
}

private data class ExplorerFilters(
    var classGlobRaw: String? = null,
    var classRegexRaw: String? = null,
    var textRegexRaw: String? = null,
    var conclusionRegexRaw: String? = null,
    var classGlob: List<Regex>? = null,
    var classRegex: Regex? = null,
    var textRegex: Regex? = null,
    var conclusionRegex: Regex? = null,
) {
    fun clearAll() {
        classGlobRaw = null
        classRegexRaw = null
        textRegexRaw = null
        conclusionRegexRaw = null
        classGlob = null
        classRegex = null
        textRegex = null
        conclusionRegex = null
    }

    fun matchesClass(simpleName: String, fqName: String): Boolean {
        val targets = listOf(simpleName, fqName)

        val globMatch = classGlob?.let { globs ->
            targets.any { target -> globs.any { glob -> glob.matches(target) } }
        } ?: true

        val regexMatch = classRegex?.let { regex ->
            targets.any { target -> regex.containsMatchIn(target) }
        } ?: true

        return globMatch && regexMatch
    }

    fun matchesText(renderedView: String): Boolean = textRegex?.containsMatchIn(renderedView) ?: true

    fun matchesConclusion(sequentText: String): Boolean =
        conclusionRegex?.containsMatchIn(sequentText) ?: true
}

private data class StatementEntry(
    val holderClassName: String,
    val holderSimpleName: String,
    val memberName: String,
    val statement: StatementDefinition,
) {
    val uniqueId: String = "$holderClassName.$memberName"

    val supportLabel: String = when (statement.support) {
        is AssumedTrue -> "assumed"
        is ProofProvided -> "proof"
    }

    val renderedView: String = buildString {
        appendLine("holder: $holderClassName.$memberName")
        appendLine("name: ${statement.name}")
        appendLine("support: $supportLabel")

        appendLine("parameters:")
        if (statement.parameters.isEmpty()) {
            appendLine("- none")
        } else {
            statement.parameters.forEach { parameter ->
                appendLine("- ${parameter.name}: ${parameter.sort}")
            }
        }

        appendLine("premises:")
        if (statement.premises.isEmpty()) {
            appendLine("- none")
        } else {
            statement.premises.forEachIndexed { index, premise ->
                appendLine("${index + 1}. $premise : ${premise.sort}")
            }
        }

        appendLine("conclusion:")
        appendLine("- ${statement.conclusion} : ${statement.conclusion.sort}")
    }.trimEnd()

    val sequentText: String = if (statement.premises.isNotEmpty()) {
        "${statement.premises.joinToString(", ")} ⊢ ${statement.conclusion}"
    } else {
        statement.conclusion.toString()
    }
}

private data class TodoFact(
    val entry: StatementEntry,
    val stepLabel: String,
    val claimText: String,
    val note: String?,
)

private data class StatementLookup(
    private val byIdentity: IdentityHashMap<StatementDefinition, StatementEntry>,
    private val byFingerprint: Map<String, StatementEntry>,
) {
    companion object {
        fun build(entries: List<StatementEntry>): StatementLookup {
            val identity = IdentityHashMap<StatementDefinition, StatementEntry>()
            val fingerprint = linkedMapOf<String, StatementEntry>()
            entries.forEach { entry ->
                identity.putIfAbsent(entry.statement, entry)
                fingerprint.putIfAbsent(statementFingerprint(entry.statement), entry)
            }
            return StatementLookup(
                byIdentity = identity,
                byFingerprint = fingerprint,
            )
        }
    }

    fun resolve(statement: StatementDefinition): StatementEntry? =
        byIdentity[statement] ?: byFingerprint[statementFingerprint(statement)]
}

private data class DependsOptions(
    val regexRaw: String,
    val nameRegex: Regex,
    val maxDepth: Int?,
    val flattenTransitive: Boolean,
)

private fun statementFingerprint(statement: StatementDefinition): String = buildString {
    append(statement.name)
    append("|")
    append(
        statement.parameters.joinToString(",") { parameter ->
            "${parameter.name}:${parameter.sort}"
        },
    )
    append("|")
    append(statement.premises.joinToString(";;") { premise -> premise.toString() })
    append("|")
    append(statement.conclusion)
}

private data class RenderStyle(
    private val ansiEnabled: Boolean,
) {
    companion object {
        fun detect(lineReader: LineReader, colorMode: ColorMode): RenderStyle {
            if (colorMode == ColorMode.Always) {
                return RenderStyle(ansiEnabled = true)
            }
            if (colorMode == ColorMode.Never) {
                return RenderStyle(ansiEnabled = false)
            }

            val forceColor = System.getenv("CLICOLOR_FORCE")?.let { value -> value != "0" } ?: false
            if (forceColor) {
                return RenderStyle(ansiEnabled = true)
            }
            val noColor = System.getenv("NO_COLOR") != null
            if (noColor) {
                return RenderStyle(ansiEnabled = false)
            }
            val terminalType = runCatching { lineReader.terminal.type }.getOrNull().orEmpty()
            val termEnv = System.getenv("TERM").orEmpty()
            val dumb = terminalType.contains("dumb", ignoreCase = true) || termEnv.equals("dumb", ignoreCase = true)
            return RenderStyle(ansiEnabled = !dumb)
        }
    }

    fun classHeader(text: String): String = wrap("1;36", text)

    fun signature(text: String): String = wrap("1;32", text)

    fun premises(text: String): String = wrap("33", text)

    fun turnstile(): String = wrap("1;35", "⊢")

    fun conclusion(text: String): String = wrap("1", text)

    fun summary(text: String): String = wrap("1;34", text)

    fun muted(text: String): String = wrap("2", text)

    private fun wrap(code: String, text: String): String =
        if (!ansiEnabled) text else "\u001B[${code}m$text\u001B[0m"
}

private enum class ColorMode {
    Auto,
    Always,
    Never,
}

private fun parseColorMode(args: Array<String>): ColorMode? {
    var colorMode = ColorMode.Auto
    args.forEach { arg ->
        when {
            arg.startsWith("--color=") -> {
                colorMode = when (arg.substringAfter('=').lowercase()) {
                    "auto" -> ColorMode.Auto
                    "always" -> ColorMode.Always
                    "never" -> ColorMode.Never
                    else -> {
                        println("Invalid color mode '${arg.substringAfter('=')}'. Use auto|always|never.")
                        return null
                    }
                }
            }
            else -> {
                println("Unknown argument '$arg'. Supported argument: --color=auto|always|never")
                return null
            }
        }
    }
    return colorMode
}

private data class ObjectHolder(
    val className: String,
    val simpleName: String,
    val clazz: Class<*>,
    val instance: Any,
)

private fun discoverObjectHolder(
    className: String,
    classLoader: ClassLoader,
): ObjectHolder? {
    val clazz = runCatching { Class.forName(className, false, classLoader) }.getOrNull() ?: return null
    val instance = extractObjectInstance(clazz) ?: return null
    val simpleName = clazz.simpleName.takeUnless { it.isEmpty() } ?: className.substringAfterLast('.')
    return ObjectHolder(
        className = className,
        simpleName = simpleName,
        clazz = clazz,
        instance = instance,
    )
}

private fun discoverFieldEntries(holder: ObjectHolder): List<StatementEntry> {
    val entries = mutableListOf<StatementEntry>()
    val fields = statementFieldsAcrossHierarchy(holder.clazz)
    fields.forEach { field ->
        val statement = runCatching {
            field.isAccessible = true
            field.get(holder.instance) as? StatementDefinition
        }.getOrNull() ?: return@forEach
        entries += StatementEntry(
            holderClassName = holder.className,
            holderSimpleName = holder.simpleName,
            memberName = field.name,
            statement = statement,
        )
    }
    return entries
}

private fun discoverFunctionEntries(
    holder: ObjectHolder,
    allObjectHolders: List<ObjectHolder>,
): List<StatementEntry> {
    val entries = mutableListOf<StatementEntry>()
    val methods = discoverStatementFactoryMethods(holder.clazz)
    methods.forEach { method ->
        val argumentBindings = discoverArgumentBindings(method, allObjectHolders)
        argumentBindings.forEach { binding ->
            val arguments = binding.map { objectHolder -> objectHolder.instance }.toTypedArray()
            val statement = runCatching {
                method.isAccessible = true
                method.invoke(holder.instance, *arguments) as? StatementDefinition
            }.getOrNull() ?: return@forEach

                entries += StatementEntry(
                    holderClassName = holder.className,
                    holderSimpleName = holder.simpleName,
                    memberName = renderFunctionVariantName(method = method, binding = binding),
                    statement = statement,
                )
            }
        }
    return entries
}

private fun discoverStatementFactoryMethods(clazz: Class<*>): List<Method> =
    (clazz.declaredMethods.asSequence() + clazz.methods.asSequence())
        .asSequence()
        .filter { method -> !method.isSynthetic }
        .filter { method -> !Modifier.isStatic(method.modifiers) }
        .filter { method -> StatementDefinition::class.java.isAssignableFrom(method.returnType) }
        .filter { method -> '$' !in method.name }
        .distinctBy(::methodSignatureKey)
        .sortedBy(Method::getName)
        .toList()

private fun isLikelyPropertyGetter(methodName: String): Boolean =
    methodName.startsWith("get") &&
        methodName.length > 3 &&
        methodName[3].isUpperCase()

private fun discoverArgumentBindings(
    method: Method,
    allObjectHolders: List<ObjectHolder>,
): List<List<ObjectHolder>> {
    val parameterTypes = method.parameterTypes.toList()
    if (parameterTypes.isEmpty()) {
        return listOf(emptyList())
    }

    val candidatesPerParameter = parameterTypes.map { parameterType ->
        allObjectHolders.filter { objectHolder ->
            parameterType.isAssignableFrom(objectHolder.clazz)
        }
    }
    if (candidatesPerParameter.any { candidates -> candidates.isEmpty() }) {
        return emptyList()
    }

    return cartesianProduct(candidatesPerParameter)
}

private fun renderFunctionVariantName(
    method: Method,
    binding: List<ObjectHolder>,
): String = if (binding.isEmpty()) {
    memberNameForMethod(method)
} else {
    "${memberNameForMethod(method)}[${binding.joinToString(",") { objectHolder -> objectHolder.simpleName }}]"
}

private fun memberNameForMethod(method: Method): String {
    if (method.parameterCount == 0 && isLikelyPropertyGetter(method.name)) {
        return getterNameToPropertyName(method.name)
    }
    return method.name
}

private fun getterNameToPropertyName(methodName: String): String {
    val suffix = methodName.removePrefix("get")
    if (suffix.isEmpty()) {
        return methodName
    }
    return suffix.replaceFirstChar { character -> character.lowercase() }
}

private fun methodSignatureKey(method: Method): String =
    buildString {
        append(method.name)
        append('#')
        append(method.parameterTypes.joinToString(",") { parameterType -> parameterType.name })
        append("->")
        append(method.returnType.name)
    }

private fun <T> cartesianProduct(candidates: List<List<T>>): List<List<T>> {
    if (candidates.isEmpty()) {
        return listOf(emptyList())
    }

    var product: List<List<T>> = listOf(emptyList())
    candidates.forEach { options ->
        product = product.flatMap { prefix ->
            options.map { option -> prefix + option }
        }
    }
    return product
}

private fun discoverClassNames(packagePrefix: String): Set<String> {
    val packagePath = packagePrefix.replace('.', '/')
    val classPath = System.getProperty("java.class.path").orEmpty()
    val separator = System.getProperty("path.separator")
    val result = linkedSetOf<String>()

    classPath
        .split(separator)
        .asSequence()
        .map { it.trim() }
        .filter { it.isNotEmpty() }
        .forEach { entry ->
            val file = File(entry)
            when {
                file.isDirectory -> collectFromDirectory(file, packagePath, result)
                file.isFile && file.extension == "jar" -> collectFromJar(file, packagePath, result)
            }
        }

    return result
}

private fun collectFromDirectory(
    root: File,
    packagePath: String,
    destination: MutableSet<String>,
) {
    val base = File(root, packagePath)
    if (!base.exists()) {
        return
    }

    base.walkTopDown()
        .filter { it.isFile && it.extension == "class" }
        .forEach { classFile ->
            val className = classFile
                .relativeTo(root)
                .path
                .removeSuffix(".class")
                .replace(File.separatorChar, '.')
            if (isClassNameCandidate(className)) {
                destination += className
            }
        }
}

private fun collectFromJar(
    jarFile: File,
    packagePath: String,
    destination: MutableSet<String>,
) {
    runCatching {
        JarFile(jarFile).use { jar ->
            val entries = jar.entries()
            while (entries.hasMoreElements()) {
                val entry = entries.nextElement()
                if (entry.isDirectory) {
                    continue
                }
                if (!entry.name.startsWith("$packagePath/")) {
                    continue
                }
                if (!entry.name.endsWith(".class")) {
                    continue
                }

                val className = entry.name.removeSuffix(".class").replace('/', '.')
                if (isClassNameCandidate(className)) {
                    destination += className
                }
            }
        }
    }
}

private fun isClassNameCandidate(className: String): Boolean {
    if (className.contains('$')) {
        return false
    }
    if (className.endsWith("Kt")) {
        return false
    }
    return true
}

private fun extractObjectInstance(clazz: Class<*>): Any? {
    val instanceField = clazz.declaredFields.firstOrNull { field ->
        field.name == "INSTANCE" &&
            Modifier.isStatic(field.modifiers) &&
            field.type == clazz
    } ?: return null

    return runCatching {
        instanceField.isAccessible = true
        instanceField.get(null)
    }.getOrNull()
}

private fun statementFieldsAcrossHierarchy(clazz: Class<*>): List<Field> {
    val result = mutableListOf<Field>()
    val names = linkedSetOf<String>()
    var current: Class<*>? = clazz
    while (current != null && current != Any::class.java) {
        current.declaredFields
            .asSequence()
            .filter { !it.isSynthetic }
            .filter { it.name != "INSTANCE" }
            .filter { StatementDefinition::class.java.isAssignableFrom(it.type) }
            .forEach { field ->
                if (names.add(field.name)) {
                    result += field
                }
            }
        current = current.superclass
    }
    return result
}

private fun compileGlobPatterns(raw: String): List<Regex> {
    val patterns = raw.split(',').map { it.trim() }.filter { it.isNotEmpty() }
    require(patterns.isNotEmpty()) { "At least one glob pattern is required." }
    return patterns.map { glob -> Regex(globToRegex(glob)) }
}

private fun globToRegex(glob: String): String {
    val builder = StringBuilder("^")
    glob.forEach { ch ->
        when (ch) {
            '*' -> builder.append(".*")
            '?' -> builder.append('.')
            '.', '(', ')', '[', ']', '{', '}', '+', '^', '$', '|', '\\' -> {
                builder.append('\\').append(ch)
            }
            else -> builder.append(ch)
        }
    }
    builder.append('$')
    return builder.toString()
}
