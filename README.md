# MathProofEngine

`MathProofEngine` is a Kotlin-first playground for writing mathematical statements and proofs in code and then checking those proofs with a small verification kernel.

The current baseline is intentionally modest:

- a minimal sorted expression core built from `Free`, `Bound`, `Lambda`, and unary `Apply`
- curried function sorts, higher-order application, and sort variables
- foundational syntax in `core-engine` and proposition logic in `logic`
- a starter logical basis split into trusted `LogicAxioms` and proof-backed `LogicLibrary`
- runnable examples and tests that show the verifier working end to end

## Project Shape

```text
core-engine/
  model/      Minimal expression kernel, core sorts, and validation
  kernel/     Statements, proof steps, justifications, and verifier
  core/       Foundational constructors and non-logical syntax (`CoreSorts`, constructors, lambda helpers)
logic/
  logic/      Proposition-level syntax, trusted axioms, and proof-backed logical lemmas
equality/
  equality/   Generic equality syntax, trusted axioms, and proof-backed equality lemmas
fol/
  fol/        Explicit `forall` / `exists` syntax and starter first-order rules
src/main/kotlin/dev/moklev/mathproof/
  examples/   Small sample proofs that double as executable documentation
  Main.kt     Runnable entry point
```

`core-engine` intentionally knows only foundational concepts. Proposition logic now lives in `logic`. Domain-specific mathematics will be added back later as separate modules once that boundary is redesigned. Quantifiers and other first-order logic features are intentionally not part of the current `logic` module yet; they are planned as a separate layer above propositional logic.

## Current Usage

Run the examples:

```bash
./gradlew run
```

Run the tests:

```bash
./gradlew test
```

Example style:

```kotlin
val statement = statement("chained-modus-ponens") {
    val p = parameter("p", CoreSorts.Proposition)
    val q = parameter("q", CoreSorts.Proposition)
    val r = parameter("r", CoreSorts.Proposition)

    val pqPremise = premise(p implies q)
    val qrPremise = premise(q implies r)
    val pPremise = premise(p)
    conclusion(r)
    proof {
        val pq = given(pqPremise)
        val qr = given(qrPremise)
        val givenP = given(pPremise)
        val givenQ = infer(LogicAxioms.modusPonens(p, q), givenP, pq)
        infer(LogicAxioms.modusPonens(q, r), givenQ, qr)
    }
}
```

Universal generalization in `fol` now requires a proof-local arbitrary variable (not a statement parameter or constant):

```kotlin
val theorem = statement("forall-id") {
    val s = sortVariable("S")
    val p = function("P", s, returns = CoreSorts.Proposition)
    conclusion(forall("u", s) { p(it) implies p(it) })
    proof {
        forAllByGeneralization("x", s) { x ->
            infer(LogicLibrary.implicationIdentity(p(x)))
        }
    }
}
```

Trusted logical primitives live in `LogicAxioms`, while proof-backed derived lemmas live in `LogicLibrary`.

For example, the Hilbert `A1` schema is stored as an axiom:

```kotlin
val hilbertAxiom1 = statement("hilbert-a1") {
    val p = parameter("p", CoreSorts.Proposition)
    val q = parameter("q", CoreSorts.Proposition)

    conclusion(p implies (q implies p))
    assumed("Hilbert axiom schema A1 for classical propositional logic. Trusted as an axiom.")
}
```

And a proof-backed derived lemma can be stored separately:

```kotlin
val hypotheticalSyllogism = statement("hypothetical-syllogism") {
    val p = parameter("p", CoreSorts.Proposition)
    val q = parameter("q", CoreSorts.Proposition)
    val r = parameter("r", CoreSorts.Proposition)

    val pqPremise = premise("pq", p implies q)
    val qrPremise = premise("qr", q implies r)
    conclusion(p implies r)
    proof {
        ...
    }
}
```

## Intended Growth Path

The current design is biased toward a future proof assistant rather than a closed demo. The next natural layers are:

1. parser support for a text proof language that compiles into the same lambda-based kernel objects
2. derived logical/mathematical syntax over the minimal core, while keeping verification on the core terms
3. a separate first-order logic layer with quantifiers, quantifier axioms/rules, and eventually equality-aware reasoning
4. derived rules and small automation tactics
5. richer domain libraries for algebra, number theory, analysis, geometry, and set theory
6. proof search experiments driven by deterministic tactics first, then LLM-guided exploration

## Notes

- `AGENTS.md` is the canonical map for future Codex sessions and other AI agents.
- `docs/project-roadmap.md` proposes a commit cadence where each commit teaches the engine one new capability and records one mathematical idea.
- `docs/reading/mathematics-roadmap.md` is the structured literature and note-taking backbone for future study.
