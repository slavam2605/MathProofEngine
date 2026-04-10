# Project Roadmap

This roadmap is organized as commit-sized slices so the repository grows in a way that is both technically useful and mathematically educational.

## Current State (2026-04-10)

- Multi-module layout is active: `core-engine`, `logic`, `equality`, `fol`, `algebra`, `nat`, plus root `src/` examples and integration tests.
- Proof surface supports direct scripts plus scoped assumptions (`assume`, `contradiction`) with explicit context tracking.
- Algebra statements are now evidence-driven across `SemiringTheory`, `Commutative`, `Ordered`, `RingTheory`, and `FieldTheory`.
- `NatTheory` currently provides proof-backed evidence for semiring, multiplicative commutativity, and ordered properties.
- The largest remaining trust debt in this area is ordered-field `zeroLeOne` (`0 <= 1`).

## Active Gaps

- Replace trusted `OrderedField.zeroLeOne` with proof-backed derivation.
- Improve proof ergonomics for long rewrite/transitivity chains used in arithmetic/order proofs.
- Continue reducing overload friction between root and scoped proof DSL APIs.
- Add parser/text-script layer while keeping Kotlin DSL as canonical lossless representation.

## Suggested Next Commits

1. Close ordered-field trust debt (`0 <= 1`) by replacing the current trusted path with proof-backed evidence.

2. Add reusable rewrite-chain helpers.
   Focus on additive term reordering and transitivity chain builders used repeatedly in `nat` and future `real` proofs.

3. Expand algebra-module verification tests.
   Add discovery-based statement verification (with shared discovery robustness checks) for algebra holders.

4. Continue proof-scope unification.
   Follow [unified-proof-scope-plan.md](unified-proof-scope-plan.md) incrementally: keep semantics stable, reduce overload ambiguity.

5. Add parser groundwork for statement/proof scripts.
   Preserve Kotlin DSL as source of truth while introducing text-level round-tripping.

6. Introduce targeted deterministic tactics.
   Start with equality-chain completion and MP-chain closure helpers before any search-heavy automation.

7. Grow domain libraries beyond number foundations.
   Prioritize commit slices that pair new engine capability with one proved theorem and one negative test.

## Commit Heuristic

If a commit changes the engine, try to include one of these alongside it:

- a new theorem in a domain library module
- a new worked example in `src/main/.../examples`
- a new note in `docs/reading/`
- a new failing-then-passing test
