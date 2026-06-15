# navier-stokes — Morning Star Project

**Status: OPEN** — NS global regularity (Surface #1) is unproved. Frozen at Clay boundary.

## What is proved

- **80 active bricks** — classical-trio-only, sorry = 0.
  - Energy inequality structure (H¹-norm, finite energy, Galilean/Poincaré invariance).
  - EnergyV2: dissipation non-negativity.
  - Symmetry group actions (translation, rotation, time-reverse, etc.).

## What is NOT proved

- Global regularity `global_smooth_exists` is OPEN (named-Prop hypothesis, not proved).
- Weak existence `weak_solution_exists` is OPEN (modeled surrogate, nonlinear term dropped).
- **NS Towers/ is FROZEN** at the Clay boundary per project invariant.

## Toolchain

```
leanprover/lean4:v4.12.0
mathlib: v4.12.0
```
