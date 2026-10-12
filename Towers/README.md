# Towers — All Lean Proofs

Two sub-towers, built by `lake build Towers` (`lean_lib Towers` in `lakefile.lean`):

- [`Towers/NS/`](NS/README.md) — Navier–Stokes formalization. 134 Lean files, 702 theorems/lemmas, zero `sorry`. The live October 2026 core is Wall266 (trilinear estimates, Sobolev embeddings, Bogovskii operator); the Clay statement `NS_M6_OPEN` remains open and tracked.
- [`Towers/YM/`](YM/README.md) — Yang–Mills auxiliary walls 260/261/263/264. Shared with the `yang-mills-gap` program; independent of the NS Clay statement.

**For the referee:** the import graph is acyclic (Lean enforces this); every folder README states what is proved vs. what is open, with theorem names and commit SHAs.

**Dependencies:** Lean `leanprover/lean4:v4.12.0`, Mathlib `v4.12.0` (pinned repo-wide).
