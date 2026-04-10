# Unified Proof Scope Plan

Date: 2026-04-10 (reviewed)
Status: Proposed (active)
Owner: MathProofEngine

## Why This Plan Exists

Current proof scripting has two closely related but different DSL surfaces:

- top-level `ProofBuilder` with `Fact`
- nested `AssumptionScope` with `ScopedFact`

This split can cause overload-resolution traps in nested blocks. A typical failure mode is passing a `Fact` where a scoped import is intended, which can create sibling contexts and then fail when reusing `ScopedFact` values across them.

The goal is to make proof authoring feel uniform at top-level and under assumptions, while preserving soundness and keeping the verifier kernel small.

## Current Reality Check (2026-04-10)

- The split still exists (`Fact` at root, `ScopedFact` in nested scopes).
- Scoped proof support is functional and used across modules.
- Unification work has not yet replaced the dual-surface API model.

## Rating Of The Direction

- Design value: 8/10
- Refactor risk if done all at once: 5/10
- Recommendation: do this incrementally in DSL layers first, not as a kernel rewrite.

## Scope

In scope:

- unify user-facing proof operations behind one scope-shaped API
- reduce or eliminate ambiguous overload sets across `ProofBuilder` and `AssumptionScope`
- keep existing proof semantics and verifier guarantees

Out of scope:

- replacing the proof verifier kernel
- introducing first-order automation/tactics in this effort

## Target Architecture

Introduce a single DSL facade (working name: `DerivationScope`) that exposes:

- `given`, `infer`, `justify`
- `assume`, `contradiction`
- helper combinators like `applyByMpChain`, `forAllByGeneralization`, `eliminateExists`

Backends:

- Root backend over top-level proof context
- Nested backend over assumption context

Long-term option:

- one internal context model where root is just an assumption context with no assumption claim
- one fact-handle type for both root and nested flows

## Phased Implementation Plan

### Phase 0: Regression Safety Net

Deliverables:

- tests that reproduce known ambiguity/cross-context failure modes
- tests that lock in semantic differences between:
  - `eliminateExists(Expr)` (implication result)
  - `eliminateExists(Fact)` / `eliminateExists(ScopedFact)` (consumes premise)

Exit criteria:

- failures are deterministic and covered by tests before refactor starts

### Phase 1: Unified Facade Introduction

Deliverables:

- new facade API in `logic` layer (or equivalent DSL module boundary)
- root adapter (delegating to current top-level behavior)
- nested adapter (delegating to current `AssumptionContext`)

Exit criteria:

- core operations can be authored using the facade in both root and nested contexts
- no behavior change in existing statement verification

### Phase 2: Helper Migration

Deliverables:

- migrate helper combinators to facade implementations:
  - MP chaining
  - quantifier helpers (`forAllByGeneralization`, `eliminateExists`)
  - assumption-aware helpers relying on scoped compilation support

Exit criteria:

- helper code no longer duplicates separate `ProofBuilder` and `AssumptionScope` logic
- helper tests pass in both root and nested contexts

### Phase 3: Compatibility Layer + Deprecation

Deliverables:

- keep old extension entry points as thin delegates
- mark ambiguous overloads as deprecated with migration guidance
- add docs with before/after usage examples

Exit criteria:

- old code compiles with warnings
- new code path defaults to facade usage

### Phase 4: Optional Deep Unification

Deliverables:

- evaluate replacing separate `Fact`/`ScopedFact` surfaces with one fact-handle model
- evaluate using one context graph model for root + nested compilation

Exit criteria:

- decision record: proceed or stop at Phase 3
- if proceeding, no verifier soundness regression in test suite

## Risk Register

Risk 1: soundness regression around assumption dependency tracking.
Mitigation: property tests and targeted negative tests on context ancestry checks.

Risk 2: migration churn across modules (`fol`, `nat`, `algebra`, `real`).
Mitigation: staged migration with compatibility delegates and deprecation period.

Risk 3: API confusion during transition.
Mitigation: one canonical usage section in docs, with examples for root and nested proof blocks.

## Acceptance Criteria

Functional criteria:

- no cross-context misuse exceptions from overload confusion in canonical usage
- same or stronger verifier guarantees
- proof scripts for existing modules continue to verify

DX criteria:

- one obvious way to write top-level and nested proof steps
- helper signatures are context-uniform and unsurprising

## Rollout Notes

Suggested rollout order:

1. add tests and facade skeleton
2. migrate `eliminateExists` and `forAllByGeneralization`
3. migrate remaining helpers
4. deprecate legacy overloads
5. revisit deep unification decision

## Open Questions

- Should root proof blocks be represented explicitly as a root scope object in public API?
- Should legacy overloads be removed in one major step or kept permanently as forwarding shims?
- How much compile-time type guidance can we add without increasing DSL verbosity?
