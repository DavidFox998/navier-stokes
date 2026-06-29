# Navier–Stokes Clay Tower (NS Tower 540)

**Theorema Aureum 143 · Morning Star Project**  
Formal Lean 4 / Mathlib v4.12.0 tower for the Clay Millennium Prize
Navier–Stokes existence-and-smoothness problem.

## Status: OPEN (Clay)

NS global regularity is an open problem. This tower provides:
- A rigorous Fourier-side model of the Sobolev function spaces
- A full Galerkin existence + compactness stack (Phases 1–6)
- A master Clay combinator reducing NS to **3 atomic gates** (Phase 7C)
- Proof of `integration_by_parts` in the Fourier model (Phase 7A ✓)
- Proof of energy cancellation `B(u,u,u) = 0` (Phase 7B ✓)
- Gate 1 decomposed: 3 proved + 3 open sub-avenues (Phase 8A ✓)
- Gate 2 decomposed: 2 proved + 3 open sub-avenues (Phase 9A ✓)
- Gate 3 decomposed via BKM: 2 proved + 4 open sub-avenues (Phase 10 ✓)
- KP-to-NS bridge: 4 proved structural lemmas (Phase 11 ✓)
  — reduces Gate 3 to KP cascade control (weaker sufficient condition)

## Atomic Clay Gates (3 remaining)

| Gate | Name | Mathematical content | Mathlib status |
|------|------|----------------------|----------------|
| 1 | `NS_AubinLions_OPEN` | Rellich–Kondrachov compact embedding H^{s+2} ↪↪ H^s | v4.12.0 gap |
| 2 | `NS_NonlinearWeakForm_OPEN` | Nonlinear trilinear form B(u,v,w) in L² | v4.12.0 gap |
| 3 | `NS_GlobalContinuation_OPEN` | No finite-time blow-up | Clay open problem |

## Gate 3 sub-avenue map (BKM + KP reduction, Phase 10–11)

```
Gate 3 = Part A ∧ Part B
  Part A = NS_LocalRegularity_OPEN         (M — OPEN, 12-18 mo)
  Part B via BKM:
    NS_BKMCriterion_OPEN                   (K — OPEN, 12-18 mo)
    NS_GlobalSobolevBound_OPEN             (L — OPEN, Clay open)
    NS_BKM_Bridge_OPEN                     (Bridge — OPEN)
  --- Phase 11 KP reduction ---
  L reduced to: NS_KPCascadeControl_OPEN   (shell decay r<1/7, 18-24 mo)
              + NS_KPToSmoothness_OPEN     (KP → Sobolev, 18-24 mo)
  Proved structure (P+Q+R+S): comparison test, 7ⁿ entropy, cascade control,
                               necessary decay — all classical trio, 0 sorry.
```

## Proved sub-avenues by gate (total: 11 proved, 12 open)

| Gate | Proved | Open |
|------|--------|------|
| Gate 1 (Phase 8A) | A, B, B' | C (Rellich–Kondrachov), D (Banach–Alaoglu), Bridge |
| Gate 2 (Phase 9A) | E, F | G (Gagliardo–Nirenberg), H (Leray proj.), Bridge |
| Gate 3 (Phase 10) | I, J | M (local regularity), K (BKM), L (Sobolev), Bridge |
| KP pathway (Phase 11) | P, Q, R, S | KPC (cascade), KPS (KP→smooth) |

## Axiom footprint

Every file: `{propext, Classical.choice, Quot.sound}` only (classical trio).  
Zero `sorry`. Zero `axiom`. Zero new research-grade axioms.

## File map

```
Towers/NS/
  FunctionSpaces.lean       Phase 1 — Hdiv_free s, divFreeSubmodule, embed
  Leray.lean                Phase 2A — leray_proj, gradSubmodule
  Stokes.lean               Phase 2B — stokes_op (‖ξ‖² Fourier multiplier)
  Energy.lean               Phase 3 — energy, dissipation, energy_inequality
  EnergyIneq.lean           Legacy schema
  EnergyV2.lean             Phase 3B — dissipation_nonneg variant
  Divergence.lean           Divergence theorem stub
  GalerkinApprox.lean       Phase 4A — galerkin_seq
  Compactness.lean          Phase 4B — AubinLionsCriterion
  WeakSolution.lean         Phase 5 — weak_solution_exists
  Regularity.lean           Phase 6 — global_smooth_exists, IsSmoothOn
  Wall300_Scaffold.lean     Phase 6B — navier_stokes_global_regularity
  NSStokesAdjoint.lean      Phase 7A — stokes_op_adjoint PROVED ✓
  NSNonlinearTerm.lean      Phase 7B — trilinear_zero_energy PROVED ✓
  NSClayCombinator.lean     Phase 7C — ns_clay_combinator (3 gates → Clay)
  NSAubinLionsDecomp.lean   Phase 8A — Gate 1 decomposed (3 proved + 3 open)
  NSCanonicalSurfaces.lean  Phase 8B — canonical surface registry
  NSGate2Decomp.lean        Phase 9A — Gate 2 decomposed (2 proved + 3 open)
  NSGate3Decomp.lean        Phase 10 — Gate 3 BKM (2 proved + 4 open)
  NSKPBridge.lean           Phase 11 — KP-to-NS bridge (4 proved + 2 open) ✓ NEW
  NSCollection.lean         Collection / index export (all phases)
```

## Honest scope

This tower does NOT prove:
- NS global regularity (Clay open problem — Gate 3 requires M+K+L+Bridge)
- Rellich–Kondrachov / Banach–Alaoglu (Mathlib v4.12.0 gaps — Gate 1)
- Trilinear weak form for B(u,v,w) (Mathlib v4.12.0 gap — Gate 2)
- Any Clay prize claim

The KP reduction (Phase 11) provides a weaker *sufficient condition* for
Gate 3: if NS energy-shell activities decay at rate r < 1/7 and KP-to-smoothness
holds, Gate 3 Part B follows. This does NOT discharge L; it reduces it to
the KP cascade condition. NS stays OPEN.

---
Repo: `DavidFox998/navier-stokes` · Project: Morning Star / Theorema Aureum 143
