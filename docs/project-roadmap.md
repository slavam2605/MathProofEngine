# Project Roadmap

This roadmap is organized as commit-sized slices so the repository can grow in a way that is both technically useful and mathematically educational.

## Baseline

- Establish the kernel, DSL, starter theories, docs, and tests.

## Suggested Next Commits

1. Add term and formula substitution.
   Capture the idea of variable binding, free variables, and safe replacement.

2. Add schema instantiation for axioms and theorems.
   Use it to move from one-off identities to reusable theorem schemas.

3. Add equality rewriting.
   Prove simple algebraic and trigonometric transformations by chaining named identities.

4. Add arithmetic and induction primitives.
   Record Peano-style examples and a first induction proof over naturals.

5. Add a text parser for statements and proof scripts.
   Keep Kotlin DSL as the lossless reference representation.

6. Add a separate first-order logic module.
   Reintroduce `forall`, `exists`, and later biconditional support together with real quantifier axioms/rules instead of keeping unsupported syntax in the propositional `logic` module.

7. Add context-aware proof judgments.
   Introduce a proof layer around sequents such as `Gamma |- phi`, local assumptions, weakening, and implication discharge so proofs can use temporary contexts and later compile back into implication-based statements.

8. Add geometry-specific structures.
   Introduce points, lines, incidence, and betweenness instead of encoding geometry only as generic function terms.

9. Add search helpers.
   Start with deterministic tactics such as repeated rewriting, modus ponens closure, or equality-chain completion.

10. Add theory packs.
   Separate foundations, algebra, analysis, number theory, set theory, and geometry into clearer modules if the single Gradle module becomes crowded.

## Commit Heuristic

If a commit changes the engine, try to include one of these alongside it:

- a new theorem in `library/`
- a new worked example in `examples/`
- a new note in `docs/reading/`
- a new failing-then-passing test
