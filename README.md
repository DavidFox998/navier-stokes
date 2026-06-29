# Navier–Stokes Clay Tower (NS Tower 540)

**Theorema Aureum 143 · Morning Star Project**
Formal Lean 4 / Mathlib v4.12.0 tower for the Clay Millennium Prize
Navier–Stokes existence-and-smoothness problem.

## Status: OPEN (Clay)

NS global regularity is an open problem. This tower provides:
- A rigorous Fourier-side model of the Sobolev function spaces
- A full Galerkin existence + compactness stack (Phases 1–6)
- A master Clay combinator reducing NS to **3 atomic gates** (Phase 7C)
- Proof that `integration_by_parts` holds in the Fourier model (Phase 7A ✓)
- Proof of energy cancellation `B(u,u,u) = 0` (Phase 7B ✓)

## Atomic Clay Gates (3 remaining)

| Gate | Name | Mathematical content | Mathlib status |
|------|------|----------------------|----------------|
| 1 | `NS_AubinLions_OPEN` | Rellich–Kondrachov compact embedding H^{s+2} ↪↪ H^s | v4.12.0 gap |
| 2 | `NS_NonlinearWeakForm_OPEN` | Nonlinear trilinear form B(u,v,w) in L² | v4.12.0 gap |
| 3 | `NS_GlobalContinuation_OPEN` | No finite-time blow-up | Clay open problem |

## Axiom footprint

Every file: `{propext, Classical.choice, Quot.sound}` only (classical trio).
Zero `sorry`. Zero `axiom`. Zero new research-grade axioms.

## File map

```
Towers/NS/
  FunctionSpaces.lean     Phase 1 — Hdiv_free s, divFreeSubmodule, embed
  Leray.lean              Phase 2A — leray_proj, gradSubmodule
  Stokes.lean             Phase 2B — stokes_op (‖ξ‖² Fourier multiplier)
  Energy.lean             Phase 3 — energy, dissipation, energy_inequality
  EnergyIneq.lean         Legacy schema (old EnergyIneq type)
  EnergyV2.lean           Phase 3B — dissipation_nonneg variant
  Divergence.lean         Divergence theorem stub
  GalerkinApprox.lean     Phase 4A — galerkin_seq
  Compactness.lean        Phase 4B — AubinLionsCriterion (named Prop)
  WeakSolution.lean       Phase 5 — weak_solution_exists combinator
  Regularity.lean         Phase 6 — global_smooth_exists, weak_implies_strong
  Wall300_Scaffold.lean   Phase 6B — navier_stokes_global_regularity (3 hyps)
  NSStokesAdjoint.lean    Phase 7A — stokes_op_adjoint PROVED ✓ NEW
  NSNonlinearTerm.lean    Phase 7B — trilinear_zero_energy PROVED ✓ NEW
  NSClayCombinator.lean   Phase 7C — ns_clay_combinator (3 gates → Clay) NEW
  NSCollection.lean       Collection / index export file NEW
```

## What is proved (summary)

- `divFreeSubmodule_isClosed` — div-free subspace is closed (sequential proof)
- `embed h` — bounded Sobolev inclusion H^s ↪ H^{s'} for s' ≤ s
- `stokes_op s` — Stokes/−Δ operator as ‖ξ‖² Fourier multiplier, norm ≤ 1
- `stokesSymbol_re_nonneg` — ‖ξ‖² ≥ 0 (seed of sectoriality)
- `energy_inequality` — Leray–Hopf energy inequality (conditional combinator)
- `energy_nonincreasing` — d/dt ‖u‖² ≤ 0 along energy balance
- `weak_solution_exists` — weak NS existence (3 named Prop inputs)
- `weak_implies_strong` — weak ⇒ smooth on (0,T) (named Prop input)
- **`stokes_op_adjoint`** — self-adjointness of A in Fourier model (NEW, GENUINE)
- **`integration_by_parts_proved`** — closes Phase-3 named surface (NEW, GENUINE)
- **`trilinear_zero_energy`** — B(u,u,u) = 0 for div-free u (NEW, GENUINE)
- **`ns_clay_combinator`** — 3 atomic gates → NS Clay (NEW, GENUINE)

## Honest scope

This tower does NOT prove:
- NS global regularity (Clay open problem)
- Weak-to-strong regularity without additional inputs
- The Rellich–Kondrachov theorem (Mathlib v4.12.0 gap)
- Any Clay prize claim

The `Wall300_Scaffold.lean` and `NSClayCombinator.lean` combinators are
CONDITIONAL: they prove nothing without the named OPEN gate hypotheses.

## Build

```
lake build
```

Requires `mathlib v4.12.0`. See `lean-toolchain` and `lakefile.lean`.

---
Repo: `DavidFox998/navier-stokes` · Project: Morning Star / Theorema Aureum 143
