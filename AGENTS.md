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

- `core/`: the minimal expression kernel (`Free`, `Bound`, `Lambda`, `Apply`), foundational sorts, constructors, and symbol registry/namespaces
- `proof-engine/`: statements, proof scripts, justifications, verifier, and proof-focused DSL primitives
- `logic/`: proposition-level syntax, trusted axioms in `LogicAxioms`, proof-backed lemmas in `LogicLibrary`, and scoped proof DSL helpers
- `equality/`: generic equality syntax, trusted equality axioms, and proof-backed equality lemmas/helpers
- `fol/`: first-order (`forall`/`exists`) syntax plus first-order axioms and helper DSL
- `algebra/`: reusable algebra theory surfaces (`SemiringTheory`, `RingTheory`, `FieldTheory`) and orthogonal traits (`Commutative`, `Ordered`, `OrderedField`)
- `nat/`: natural-number syntax, axioms, and proof-backed Nat evidence/lemmas
- root `src/`: executable examples, statement explorer tool, and integration-style tests

## Extension Rules

- Only expression/sort/symbol foundations belong in `core/`; proof mechanics belong in `proof-engine`. Proposition logic belongs in `logic/`, and mathematical rules/domain sorts should stay out of lower layers by default.
- Quantifiers and first-order constructs belong in `fol/` above `logic/`; avoid silently expanding propositional `logic/` with first-order semantics.
- New mathematical domains should be added as separate modules once their boundaries are clear, rather than recreated ad hoc inside the core or logic modules.
- New syntax experiments should live in `core/` when foundational to expressions/symbols, in `proof-engine/` when proof-layer specific, or in future domain modules when domain-specific.
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
- Expand first-order reasoning ergonomics (`fol`) and keep quantifier-aware helpers reusable across math domains.
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
