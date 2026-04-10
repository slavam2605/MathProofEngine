# Mathematics Reading Roadmap

This file is a living study map for both mathematical growth and future engine design.

## How To Use This File

For each item, keep notes in place under the prompts:

- Status:
- Why now:
- Core objects and definitions:
- Common proof patterns:
- Ideas worth encoding in the engine:
- Candidate example theorems:
- Open questions:

## Current Focus (2026-04-10)

- Immediate project focus is number foundations: Nat/Algebra consolidation and replacing trusted ordered-field `0 <= 1`.
- When capturing reading notes, prioritize material that shortens this path:
  - ring/field identity proofs
  - ordered-ring/ordered-field lemmas
  - contradiction-oriented proof patterns

## 1. Proof Writing And Introductory Logic

### Daniel J. Velleman, *How to Prove It: A Structured Approach* (3rd ed., Cambridge, 2019)
Link: https://www.cambridge.org/core/books/how-to-prove-it/97F48414AF68062CCE4BBACBA3DDE1E9

- Why start here: it directly covers sentential logic, quantificational logic, proofs, relations, functions, induction, and infinite sets.
- Engine relevance: this is a strong guide for the first proof rules, proof styles, and examples.
- Notes:
  - Status:
  - Core objects and definitions:
  - Common proof patterns:
  - Ideas worth encoding in the engine:
  - Candidate example theorems:
  - Open questions:

### Richard Hammack, *Book of Proof* (free online text)
Link: https://richardhammack.github.io/BookOfProof/

- Why add it: it is a free companion for proof habits, sets, functions, relations, induction, countability, and cardinality.
- Engine relevance: useful for early examples and for writing notes in a style that stays accessible.
- Notes:
  - Status:
  - Core objects and definitions:
  - Common proof patterns:
  - Ideas worth encoding in the engine:
  - Candidate example theorems:
  - Open questions:

### The Open Logic Project (open modular text)
Link: https://openlogicproject.org/

- Why add it: it is free, modular, and covers proof systems, model theory, set theory, computability, and incompleteness.
- Engine relevance: especially valuable once you want multiple proof systems or a parser that supports more than one notation style.
- Notes:
  - Status:
  - Core objects and definitions:
  - Common proof patterns:
  - Ideas worth encoding in the engine:
  - Candidate example theorems:
  - Open questions:

## 2. Foundations: Set Theory, Logic, And Arithmetic

### Paul R. Halmos, *Naive Set Theory* (Springer)
Link: https://link.springer.com/book/10.1007/978-1-4757-1645-0

- Why now: a compact bridge from everyday mathematical set usage into explicit axioms and constructions.
- Engine relevance: good source for extensionality, specification-style reasoning, products, relations, ordinals, and well-ordering seeds.
- Notes:
  - Status:
  - Core objects and definitions:
  - Common proof patterns:
  - Ideas worth encoding in the engine:
  - Candidate example theorems:
  - Open questions:

### David Marker, *An Invitation to Mathematical Logic* (Springer, 2024)
Link: https://link.springer.com/book/10.1007/978-3-031-55368-4

- Why now: it gives a modern entry point to truth, proof, model theory, computability, incompleteness, and Peano arithmetic.
- Engine relevance: useful when the project graduates from proof checking into semantics, models, and metatheory.
- Notes:
  - Status:
  - Core objects and definitions:
  - Common proof patterns:
  - Ideas worth encoding in the engine:
  - Candidate example theorems:
  - Open questions:

### Peter Smith, *An Introduction to Gödel's Theorems* (Cambridge)
Link: https://www.cambridge.org/core/books/an-introduction-to-godels-theorems/BC74EDED93973CB8F3B656A251C58B09

- Why add it: it gives a focused route into formal arithmetic, incompleteness, and the exact role of Peano arithmetic.
- Engine relevance: especially good when you want to model syntax about syntax, encoding, and proof statements about proof systems.
- Notes:
  - Status:
  - Core objects and definitions:
  - Common proof patterns:
  - Ideas worth encoding in the engine:
  - Candidate example theorems:
  - Open questions:

### Thomas Jech, *Set Theory* (for deeper ZFC and beyond)
Link: https://link.springer.com/book/10.1007/3-540-44761-X

- Why later: this is the step from basic axiomatic set theory into forcing, descriptive set theory, and large cardinals.
- Engine relevance: useful once the project can already express and verify substantial first-order reasoning.
- Notes:
  - Status:
  - Core objects and definitions:
  - Common proof patterns:
  - Ideas worth encoding in the engine:
  - Candidate example theorems:
  - Open questions:

## 3. Analysis And Functions

### Stephen Abbott, *Understanding Analysis* (2nd ed., Springer)
Link: https://link.springer.com/book/10.1007/978-1-4939-2712-8

- Why now: it is a clean route into rigorous real analysis and proofs about sequences, limits, continuity, and compactness.
- Engine relevance: ideal for building theories around real-valued functions, epsilon-delta proofs, and structured derivations.
- Notes:
  - Status:
  - Core objects and definitions:
  - Common proof patterns:
  - Ideas worth encoding in the engine:
  - Candidate example theorems:
  - Open questions:

### Tristan Needham, *Visual Complex Analysis: 25th Anniversary Edition* (Oxford, 2023)
Link: https://academic.oup.com/book/45765

- Why add it: it gives a geometric feel for complex analysis instead of reducing everything to symbol pushing.
- Engine relevance: a good reminder that the project may eventually need geometric structures, not just scalar expressions.
- Notes:
  - Status:
  - Core objects and definitions:
  - Common proof patterns:
  - Ideas worth encoding in the engine:
  - Candidate example theorems:
  - Open questions:

## 4. Algebra, Number Theory, And Structural Mathematics

### Sheldon Axler, *Linear Algebra Done Right* (4th ed., open access)
Link: https://link.springer.com/book/10.1007/978-3-031-41026-0

- Why add it: it is open access and strong on linear maps, eigen-structure, and proof-oriented linear algebra.
- Engine relevance: useful once you want structured objects such as vector spaces and operators rather than only scalar terms.
- Notes:
  - Status:
  - Core objects and definitions:
  - Common proof patterns:
  - Ideas worth encoding in the engine:
  - Candidate example theorems:
  - Open questions:

### Michael Artin, *Algebra* (2nd ed., Pearson)
Link: https://www.pearson.com/en-us/subject-catalog/p/algebra-classic-version/P200000006078/9780134689609

- Why add it: a broad algebra text that stays concrete while moving toward abstract structures.
- Engine relevance: a natural source when you begin formalizing groups, rings, fields, symmetry, and algebraic proofs.
- Notes:
  - Status:
  - Core objects and definitions:
  - Common proof patterns:
  - Ideas worth encoding in the engine:
  - Candidate example theorems:
  - Open questions:

### Kenneth Ireland and Michael Rosen, *A Classical Introduction to Modern Number Theory* (2nd ed., Springer)
Link: https://link.springer.com/book/10.1007/978-1-4757-2103-4

- Why add it: it connects elementary topics to reciprocity, finite fields, zeta functions, Diophantine equations, and elliptic curves.
- Engine relevance: a strong long-term roadmap once natural-number arithmetic and divisibility are represented cleanly.
- Notes:
  - Status:
  - Core objects and definitions:
  - Common proof patterns:
  - Ideas worth encoding in the engine:
  - Candidate example theorems:
  - Open questions:

### Tom M. Apostol, *Introduction to Analytic Number Theory* (Springer)
Link: https://link.springer.com/book/10.1007/978-1-4757-5579-4

- Why later: this is a good step if you want prime-distribution results and arithmetic functions after the algebraic basics feel comfortable.
- Engine relevance: helpful for distinguishing symbolic arithmetic manipulation from genuinely analytic arguments.
- Notes:
  - Status:
  - Core objects and definitions:
  - Common proof patterns:
  - Ideas worth encoding in the engine:
  - Candidate example theorems:
  - Open questions:

## 5. Geometry And Spatial Reasoning

### John M. Lee, *Axiomatic Geometry* (AMS)
Reference review: https://old.maa.org/press/maa-reviews/axiomatic-geometry

- Why add it: it is focused on rigorous axiomatic Euclidean geometry and the nature of models.
- Engine relevance: a strong candidate once the project needs points, lines, incidence, betweenness, and diagram-free proof structures.
- Notes:
  - Status:
  - Core objects and definitions:
  - Common proof patterns:
  - Ideas worth encoding in the engine:
  - Candidate example theorems:
  - Open questions:

### Robin Hartshorne, *Geometry: Euclid and Beyond* (Springer)
Reference review: https://old.maa.org/press/maa-reviews/geometry-euclid-and-beyond

- Why add it: it connects classical Euclidean geometry with modern axiomatic and algebraic viewpoints.
- Engine relevance: useful when the geometry layer must bridge synthetic reasoning and algebraic encodings.
- Notes:
  - Status:
  - Core objects and definitions:
  - Common proof patterns:
  - Ideas worth encoding in the engine:
  - Candidate example theorems:
  - Open questions:

### James R. Munkres, *Topology* (2nd ed., Pearson)
Link: https://www.pearson.com/us/higher-education/program/Munkres-Topology-Classic-Version-2nd-Edition/PGM1714695.html

- Why add it: topology becomes relevant once geometric and analytic structures stop being purely coordinate-driven.
- Engine relevance: a later-stage source for open sets, continuity, compactness, connectedness, and manifold-adjacent reasoning.
- Notes:
  - Status:
  - Core objects and definitions:
  - Common proof patterns:
  - Ideas worth encoding in the engine:
  - Candidate example theorems:
  - Open questions:

## 6. Beautiful Proofs And Formalization Practice

### Martin Aigner and Günter M. Ziegler, *Proofs from THE BOOK* (Springer)
Link: https://link.springer.com/book/10.1007/978-3-662-57265-8

- Why keep nearby: it gives excellent targets for elegant proof reconstruction across several mathematical domains.
- Engine relevance: ideal for choosing motivating medium-sized theorem challenges after the kernel becomes more capable.
- Notes:
  - Status:
  - Core objects and definitions:
  - Common proof patterns:
  - Ideas worth encoding in the engine:
  - Candidate example theorems:
  - Open questions:

### *Mathematics in Lean* (Lean community)
Link: https://leanprover-community.github.io/mathematics_in_lean/mathematics_in_lean.pdf

- Why add it: even if this project stays custom, it is useful to study how a mature theorem-proving community structures formal mathematics.
- Engine relevance: helpful for naming conventions, library organization, theorem statement style, and proof ergonomics.
- Notes:
  - Status:
  - Core objects and definitions:
  - Common proof patterns:
  - Ideas worth encoding in the engine:
  - Candidate example theorems:
  - Open questions:

### *Software Foundations* (official series)
Link: https://softwarefoundations.cis.upenn.edu/

- Why add it: it is more proof-assistant-oriented than pure mathematics, but excellent for learning disciplined formalization and proof scripts.
- Engine relevance: especially useful if the project later mixes mathematics with verified algorithms or verified proof search.
- Notes:
  - Status:
  - Core objects and definitions:
  - Common proof patterns:
  - Ideas worth encoding in the engine:
  - Candidate example theorems:
  - Open questions:
