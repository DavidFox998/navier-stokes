# Towers/YM — Yang–Mills auxiliary walls (Lean 4)

## What this is
Four Lean modules shared with the `yang-mills-gap` program: the H⁴ defect, Coxeter spectral data, and 120-cell vertex geometry that the Navier–Stokes H⁴ analysis reuses. Small, self-contained, and independent of the NS Clay statement.

## What is proved

| File | Theorems | Content | Last commit |
|---|---|---|---|
| `Wall260_ClayReduction.lean` | 1 | Pointwise dependence-defect reduction at threshold `log (7 · C)`. If `I_E x - I_polymer x < log C` and `log… | `f70c63c 2026-10-08` |
| `Wall261_H4Defect.lean` | 10 | Towers / YM / Wall261_H4Defect **The H4 / 120-cell defect improvement — honest CONDITIONAL combinator.**… | `f70c63c 2026-10-08` |
| `Wall263_CoxeterSpectral.lean` | 9 | Wall263 — H4 Coxeter matrix: `φ` is the EDGE WEIGHT, not the spectral radius This brick is the HONEST… | `7fbfc06 2026-07-01` |
| `Wall264_H4Vertices.lean` | 16 | Towers / YM / Wall264_H4Vertices **The 600-cell ("hypericosahedron") vertex geometry — MACHINE-CHECKED.**… | `f70c63c 2026-10-08` |

Zero `sorry`/`admit` in this folder (comment-aware verified 2026-10-12).

## What is open
These are auxiliary walls, not a Clay statement; no `_OPEN` tracks live here. Open questions belong to the `yang-mills-gap` repo's own ledger.

## Dependencies
- Lean `leanprover/lean4:v4.12.0`, Mathlib `v4.12.0` (repo-pinned).

## Workflow
```sh
lake build Towers   # builds YM alongside NS
```

## Chronology
Shared walls 260/261/263/264; see the `yang-mills-gap` repository history for their origin.

## Links
- [Root README](../../README.md) · [Towers README](../README.md)
- https://github.com/DavidFox998/navier-stokes
