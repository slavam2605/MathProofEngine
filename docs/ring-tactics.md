# Ring/Order Tactics Notes

Date: 2026-04-10  
Status: Draft

## Why This Exists

Several Nat and ordered proofs are currently long because we repeatedly hand-build:

- additive term reordering steps (association/commutation reshaping)
- long equality transitivity chains

This note tracks small, deterministic helper tactics that reduce boilerplate without hiding proof structure.

## Current Pain Points

- `NatOrderedEvidence.addPreservesOrderRightEvidence` includes TODOs for additive reordering and transitivity-chain ergonomics.
- Similar rewrite-chain noise appears in distributivity and order-compatibility proofs.

## Candidate Helpers

1. Additive normalization helper
   - Rewrites nested sums into a canonical association order.
   - Applies commutativity/associativity in deterministic order only.

2. Equality chain builder
   - Utility to compose `a == b`, `b == c`, `c == d` into `a == d`.
   - Emits explicit transitivity steps for verifier transparency.

3. Targeted rewrite helper
   - Replaces a selected subexpression occurrence using a provided equality fact.
   - Keeps occurrence selection explicit to avoid hidden rewrite surprises.

## Guardrails

- Helpers should compile into ordinary explicit proof steps.
- No heuristic search in these helpers.
- Keep them reusable across `nat`, `algebra`, and future `real` proofs.

## Adoption Plan

1. Introduce one helper at a time with tests.
2. Refactor one existing long Nat proof per helper.
3. Keep old proof style examples nearby until readability is clearly improved.
