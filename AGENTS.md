# Agent Guide

## Mission

Build a math-proof engine that grows from a small trustworthy kernel into a reusable statement-rich environment for exploring formalized mathematics in Kotlin.

## Non-Negotiables

- Keep the verifier small and inspectable.
- Prefer explicit domain models over stringly typed shortcuts.
- Add new mathematical power through reusable statements, rules, tests, and examples.
- Preserve a path from Kotlin surface syntax to future text parsing instead of coupling the kernel to any one notation layer.
- Each meaningful commit should add both engine value and mathematical knowledge.

## Current Architecture

- `core-engine/`: the minimal expression kernel (`Free`, `Bound`, `Lambda`, `Apply`), foundational sorts, constructors, statements, and verifier
- `logic/`: proposition-level syntax, trusted axioms in `LogicAxioms`, and proof-backed lemmas in `LogicLibrary`
- root `src/`: executable examples, the app entry point, and integration-style tests

## Extension Rules

- Only kernel-level proof mechanics belong in `core-engine`; proposition logic belongs in `logic/`, and mathematical rules and domain sorts should stay out of the core by default.
- Quantifiers and other first-order constructs should come back in a separate module above `logic/`, not by silently expanding the propositional layer.
- New mathematical domains should be added as separate modules once their boundaries are clear, rather than recreated ad hoc inside the core or logic modules.
- New syntax experiments should either live in `core-engine` when they are foundational, or in future domain modules when they are domain-specific, and in both cases compile into core objects.
- Every new rule should land with at least one passing example and one failing test when the rule is misused.
- Trusted logical primitives belong in `LogicAxioms`; reusable proof-backed lemmas belong in `LogicLibrary`.

## Commit Rhythm

Prefer commits that pair the engine with the mathematics it unlocked:

1. add a rule or representation
2. add or refine a mathematical library using that new capability
3. add one example proof and one test that exercise the new idea
4. update the docs or reading notes with what was learned

## Near-Term Roadmap

- Add richer syntax and sugar on top of the minimal lambda-based core.
- Add a separate first-order logic layer with quantifiers and quantifier reasoning above the current propositional `logic` module.
- Add a context-aware proof layer with sequents like `Gamma |- phi`, local assumptions, and explicit implication discharge; prefer treating it as a derived proof DSL first, then decide later whether it belongs in the kernel.
- Add rewriting over equalities and named identities.
- Introduce a parser layer for text-based proof scripts.
- Reintroduce mathematical domain modules with sharper boundaries than the old `topics/` bucket.
- Add geometry-oriented structures instead of forcing everything through function syntax.

## Known Current Limitation

- `BuildContextIds` and `FreshFreeIds` are still simple process-global counters. That is acceptable for current single-threaded work, but it should be revisited before parallel proof construction or heavier agent concurrency is introduced.

## AI Workflow

- Read `README.md` and this file before making structural changes.
- Update `docs/project-roadmap.md` when the project direction changes.
- Keep `docs/reading/mathematics-roadmap.md` useful as both a study plan and a knowledge capture document.
- Avoid replacing the kernel with opaque external tooling; integrations are welcome, but the core should stay understandable from the repository alone.
