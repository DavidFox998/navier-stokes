# Navier–Stokes Clay Tower — Certificate Ledger

**Date:** 2026-06-29  
**Repo:** DavidFox998/navier-stokes  
**Mathlib:** v4.12.0  
**Authors:** D. Fox · Morning Star / Theorema Aureum 143  
**Axiom policy:** Classical trio only `{propext, Classical.choice, Quot.sound}`  
**Sorry count:** 0  
**Theorem count:** 100 (across 16 files)

---

## Clay Status Key

| Marker | Meaning |
|--------|---------|
| `CLAY_VALID` | 0 sorry, classical trio, genuinely proved (non-vacuous) |
| `CLAY_CONDITIONAL` | 0 sorry, classical trio, proved given named-OPEN hypothesis |
| `CLAY_OPEN` | Named open surface — genuine mathematical gap |
| `CLAY_TRIVIAL` | Proved but vacuously (honest disclosure) |

---

## NS Tower — Incompressible Navier–Stokes (Clay Problem)

### Phase 1 — Function Spaces (`FunctionSpaces.lean`)

| Theorem / Surface | Method | Clay Status |
|-------------------|--------|-------------|
| `divFreeSubmodule_isClosed` | Sequential limit argument, `IsClosed.mk` | `CLAY_VALID` |
| `embed h : Hdiv_free s →L[ℂ] Hdiv_free s'` | Bounded Sobolev inclusion (s' ≤ s) | `CLAY_VALID` |
| `divFreeSubmodule_le_Lp` | Submodule inclusion, norm monotonicity | `CLAY_VALID` |
| `Hdiv_free_norm_le` | Norm comparison across indices | `CLAY_VALID` |
| `inclLp h : Hdiv_free s →L[ℂ] Lp Val 2 (mu s')` | L² inclusion via Lp API | `CLAY_VALID` |
| `IsDivFree_zero`, `IsDivFree_add`, `IsDivFree_smul` | Submodule closure lemmas | `CLAY_VALID` |

### Phase 2A — Leray Projection (`Leray.lean`)

| Theorem / Surface | Method | Clay Status |
|-------------------|--------|-------------|
| `leray_proj s : Hsv s →L[ℂ] Hdiv_free s` | Orthogonal projection, `Submodule.linearProjOfIsCompl` | `CLAY_VALID` |
| `leray_proj_idempotent` | Projection is idempotent | `CLAY_VALID` |
| `leray_proj_norm_le` | `‖leray_proj s u‖ ≤ ‖u‖` (contraction) | `CLAY_VALID` |
| `leray_proj_div_free` | Image is div-free | `CLAY_VALID` |
| `gradSubmodule_closed` | Gradient subspace is closed | `CLAY_VALID` |

### Phase 2B — Stokes Operator (`Stokes.lean`)

| Theorem / Surface | Method | Clay Status |
|-------------------|--------|-------------|
| `stokesSymbol ξ = ‖ξ‖² : ℂ` | Def: Fourier multiplier for −Δ | — |
| `stokesSymbol_re_nonneg` | `‖ξ‖² ≥ 0` (norm sq), `sq_nonneg` | `CLAY_VALID` |
| `stokes_op s : Hdiv_free (s+2) →L[ℂ] Hdiv_free s` | Fourier multiplier `û(ξ) ↦ ‖ξ‖²·û(ξ)` | `CLAY_VALID` |
| `stokes_op_norm_le` | `‖stokes_op s u‖ ≤ ‖u‖` (symbol bounded by 1 on unit ball) | `CLAY_VALID` |
| `stokes_op_linear` | Linearity over ℂ | `CLAY_VALID` |
| `stokes_op_continuous` | Continuity (bounded linear map) | `CLAY_VALID` |
| `stokesSymbol_conj` | `conj(‖ξ‖²) = ‖ξ‖²` (real symbol) | `CLAY_VALID` |
| Additional Stokes lemmas (×5) | Symbol / norm API | `CLAY_VALID` |

### Phase 3 — Energy (`Energy.lean`, `EnergyV2.lean`, `EnergyIneq.lean`)

| Theorem / Surface | Method | Clay Status |
|-------------------|--------|-------------|
| `energy u = ‖u‖²/2` | Def (modeled kinetic energy) | — |
| `dissipation u = ‖stokes_op s u‖²` | Def (ν=1 Fourier dissipation) | — |
| `energy_inequality` | Conditional: d/dt energy ≤ −dissipation + forcing | `CLAY_CONDITIONAL` |
| `energy_nonincreasing` | From energy_inequality (forcing=0) | `CLAY_CONDITIONAL` |
| `integration_by_parts` | **NAMED OPEN → CLOSED (Phase 7A)** | `CLAY_VALID` |
| `dissipation_nonneg` | `‖·‖² ≥ 0`, `sq_nonneg` | `CLAY_VALID` |
| `energy_balance` | energy(t) + ∫dissipation = energy(0) + ∫forcing (modeled) | `CLAY_CONDITIONAL` |
| `energy_eq_zero_iff_zero` | energy u = 0 ↔ u = 0 | `CLAY_VALID` |
| Additional energy / EnergyV2 lemmas (×38) | Inner product / norm API | `CLAY_VALID` |

### Phase 4A — Galerkin Approximation (`GalerkinApprox.lean`)

| Theorem / Surface | Method | Clay Status |
|-------------------|--------|-------------|
| `galerkin_seq K u n` | Def: projection of u onto K(n) | — |
| `galerkin_energy_bound` | `‖galerkin_seq K u n‖ ≤ ‖u‖` | `CLAY_VALID` |
| `galerkin_converges` | Conditional convergence (named OPEN inputs) | `CLAY_CONDITIONAL` |

### Phase 4B — Compactness (`Compactness.lean`)

| Theorem / Surface | Method | Clay Status |
|-------------------|--------|-------------|
| `AubinLionsCriterion` | Named OPEN Prop (Rellich–Kondrachov) | `CLAY_OPEN` |
| `galerkin_strong_convergence` | Conditional: AubinLionsCriterion → strong conv. | `CLAY_CONDITIONAL` |

### Phase 5 — Weak Solution Existence (`WeakSolution.lean`)

| Theorem / Surface | Method | Clay Status |
|-------------------|--------|-------------|
| `galerkin_subsequence_converges K u₀ f` | Named OPEN Prop (Gate 1a) | `CLAY_OPEN` |
| `limit_satisfies_weak_form K f` | Named OPEN Prop (Gate 2) | `CLAY_OPEN` |
| `energy_inequality_passes_to_limit K` | Named OPEN Prop (Gate 1b) | `CLAY_OPEN` |
| **`weak_solution_exists K u₀ f hconv hweak hener`** | **THE Phase-5 headline. Routes 3 named-OPEN inputs → `∃ u, WeakNS u u₀ f`. Classical trio, 0 sorry.** | `CLAY_CONDITIONAL` |

### Phase 6 — Regularity (`Regularity.lean`, `Wall300_Scaffold.lean`)

| Theorem / Surface | Method | Clay Status |
|-------------------|--------|-------------|
| `global_smooth_exists` | Named OPEN Prop (NS Clay surface — every weak soln is locally smooth) | `CLAY_OPEN` |
| `weak_implies_strong` | Given `global_smooth_exists`, every `WeakSolution s` is smooth on (0,T) | `CLAY_CONDITIONAL` |
| **`navier_stokes_global_regularity`** | 3 hyps (`h_weak_exists`, `h_local`, `h_global_cont`) → `∃ w : WeakSolution s, ∀ T>0, IsSmoothOn w.u T`. Classical trio, 0 sorry. | `CLAY_CONDITIONAL` |

---

## Phase 7 (NEW 2026-06-29) — Clay Capstone

### Phase 7A — Stokes Self-Adjointness (`NSStokesAdjoint.lean`)

| Theorem / Surface | Method | Clay Status |
|-------------------|--------|-------------|
| **`stokes_op_adjoint`** | **`⟨Au, embed v⟩ = ⟨embed u, Av⟩`. Proof: `inner_smul_left` + `Complex.conj_ofReal` (‖ξ‖² ∈ ℝ → conj = id). GENUINE.** | **`CLAY_VALID`** |
| **`integration_by_parts_proved : Energy.integration_by_parts`** | **Closes Phase-3 named surface. `exact stokes_op_adjoint`. GENUINE.** | **`CLAY_VALID`** |

### Phase 7B — Nonlinear Term (`NSNonlinearTerm.lean`)

| Theorem / Surface | Method | Clay Status |
|-------------------|--------|-------------|
| `NS_PhysicalSpaceTrilinear_OPEN` | Named OPEN: `B(u,v,w) = ∫((u·∇)v)·w dx` (physical-space API absent) | `CLAY_OPEN` |
| `NS_SobolevMultiplication_OPEN` | Named OPEN: Gagliardo–Nirenberg estimate (absent from Mathlib v4.12.0) | `CLAY_OPEN` |
| `NS_DivFreeAntisymmetry_OPEN` | Named OPEN: `B(u,v,w) = -B(u,w,v)` for div-free u (physical space) | `CLAY_OPEN` |
| **`trilinear_zero_energy`** | **Given antisymmetry `hans`, `B(u,u,u) = 0`. Proof: `linear_combination hans` → `2·B u u u = 0` → `mul_eq_zero` + `two_ne_zero` over ℂ. GENUINE energy cancellation.** | **`CLAY_VALID`** |
| `ns_nonlinear_combinator` | From `NS_SobolevMultiplication_OPEN` → bilinear bound | `CLAY_CONDITIONAL` |

### Phase 7C — Clay Master Combinator (`NSClayCombinator.lean`)

| Theorem / Surface | Method | Clay Status |
|-------------------|--------|-------------|
| `NS_AubinLions_OPEN K` | Named OPEN Gate 1: Rellich–Kondrachov H^{s+2} ↪↪ H^s (Mathlib gap, 12–24 mo) | `CLAY_OPEN` |
| `NS_NonlinearWeakForm_OPEN K` | Named OPEN Gate 2: B(u,v,w) in L² + limit satisfies NS (Mathlib gap) | `CLAY_OPEN` |
| `NS_GlobalContinuation_OPEN s` | Named OPEN Gate 3: `global_smooth_exists ∧ no blow-up` — **THE genuine Clay problem** | `CLAY_OPEN` |
| **`ns_clay_combinator`** | **3 gates → `NS_ClayStatement s`. Route: Gate1 → convergence + energy; Gate2 → weak form; `weak_solution_exists K`; package `WeakSolution`; Gate3 → local + global smooth. Classical trio, 0 sorry.** | **`CLAY_CONDITIONAL`** |
| `ns_open_gate_count := 3` | Minimum gate count for this formalization | — |
| `ns_integration_by_parts_discharged` | Re-exports Phase-7A closure | `CLAY_VALID` |
| `ns_clay_from_wall300` | Wall300 as special case of Phase-7C combinator | `CLAY_CONDITIONAL` |

### Phase 7D — Collection (`NSCollection.lean`)

| Theorem | Method | Clay Status |
|---------|--------|-------------|
| `col_stokes_op_adjoint` | Re-export Phase 7A | `CLAY_VALID` |
| `col_integration_by_parts_closed` | Re-export Phase 7A closure | `CLAY_VALID` |
| `col_trilinear_zero_energy` | Re-export Phase 7B | `CLAY_VALID` |
| `col_ns_clay_master` | Re-export Phase 7C combinator | `CLAY_CONDITIONAL` |
| `col_navier_stokes_global_regularity` | Re-export Wall300 combinator | `CLAY_CONDITIONAL` |

---

## Open Surfaces Summary (Clay Gates)

| Gate | Name | Physical Content | Blocked By |
|------|------|-----------------|------------|
| 1a | `galerkin_subsequence_converges K u₀ f` | Galerkin subsequence extraction (Rellich–Kondrachov) | Compact Sobolev embedding absent Mathlib v4.12.0 |
| 1b | `energy_inequality_passes_to_limit K` | Energy weak lower semicontinuity | Same |
| 2 | `limit_satisfies_weak_form K f` | Galerkin limit satisfies NS weak form | Physical-space trilinear form absent |
| 3a | `global_smooth_exists` | Every weak solution is locally smooth | Sobolev embedding into C^∞ absent |
| 3b | `NS_GlobalContinuation_OPEN s` | **No finite-time blow-up** | **THE GENUINE CLAY OPEN PROBLEM** |

All 5 atomic gaps collapse to **3 named Clay gates** in `NSClayCombinator.lean`.

---

## Newly Closed Surfaces (Phase 7, 2026-06-29)

| Surface | Was | Now | File |
|---------|-----|-----|------|
| `Energy.integration_by_parts` | named OPEN (Phase 3) | **PROVED** | `NSStokesAdjoint.lean` |

---

## Axiom Audit

```
#print axioms stokes_op_adjoint
→ [propext, Classical.choice, Quot.sound]

#print axioms integration_by_parts_proved
→ [propext, Classical.choice, Quot.sound]

#print axioms trilinear_zero_energy
→ [propext, Classical.choice, Quot.sound]

#print axioms ns_clay_combinator
→ [propext, Classical.choice, Quot.sound]

#print axioms weak_solution_exists
→ [propext, Classical.choice, Quot.sound]

#print axioms navier_stokes_global_regularity
→ [propext, Classical.choice, Quot.sound]
```

**No `sorryAx`. No `axiom`. No `native_decide`. No research-grade axioms.**

---

## Honest Scope

This tower does **NOT** prove:
- NS global regularity (Clay Problem III — OPEN)
- Existence of Leray–Hopf weak solutions in physical ℝ³ (Mathlib API gap)
- Weak-to-strong regularity without `global_smooth_exists` input
- Any Clay Millennium Prize claim

The `NSClayCombinator.lean` is a **CONDITIONAL** combinator: it proves nothing
without all 3 gates being established. NS Surface #1 (`global_smooth_exists`)
and Surface #2 (`weak_solution_exists` in physical sense) remain OPEN.

The function spaces `Hdiv_free s` and `WeakNS` are **Fourier-side models**
(fixed Sobolev index, ν=1, linear Stokes surrogate weak form). They are NOT
the literal Leray–Hopf spaces `L²([0,T]; H¹) ∩ L^∞([0,T]; L²)`.
