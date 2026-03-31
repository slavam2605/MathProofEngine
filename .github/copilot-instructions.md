# Copilot Instructions

Use `AGENTS.md` as the primary project map.

When suggesting changes:

- keep the proof kernel small, explicit, and testable
- prefer adding named theories and proof examples over one-off hardcoded cases
- preserve the separation between `model`, `kernel`, `dsl`, and `library`
- treat Kotlin DSL and future parser syntax as two front ends over the same core representation
