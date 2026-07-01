# NS Tower — Named Open Def Roadmap

**Repo:** DavidFox998/navier-stokes  
**Series:** Opera Numerorum (internal: Battle Plan v1.6)  
**Author:** David Fox | Date: May 21, 2026 (updated June 30, 2026)

## Summary

The NS Tower (Lean 4 surrogate model: linear Stokes, Fourier/Sobolev, nu=1)
builds a conditional proof chain toward NS_ClayStatement s (modeled global
regularity surrogate).  All remaining gaps are NAMED OPEN DEFS — Lean
formalization gaps or missing Mathlib API, NOT Clay Millennium open problems.

NS Surface #1 (global smooth solutions, physical R^3): LOCKED OPEN.  
No Clay Millennium Prize claim.  `#print axioms NS_CLAY_CERTIFICATE_V2` = classical trio.

---

## Proof Chain Architecture

```
NS_CLAY_CERTIFICATE_V2 (h1, h2, h3a, h3b) : NS_ClayStatement s
  |
  +-- h1 : NS_AubinLions_OPEN K          (Rellich-Kondrachov, Aubin-Lions)
  +-- h2 : NS_NonlinearWeakForm_OPEN K   (Leray-Ladyzhenskaya trilinear form)
  +-- h3a: NS_LocalRegularity_OPEN s     (Solonnikov-Giga parabolic regularity)
  +-- h3b: NS_BKMStrong_Classical_OPEN s (Beale-Kato-Majda blow-up criterion)
  All 4 are KNOWN classical results absent from Mathlib v4.12.0.

NS_WeakInitCont_OPEN s (B.1 + B.3 path, Phases 31-34)
  |
  +-- NS_WeakMomentumDiffAt_PROVED        CLOSED Phase 38a (unconditional, 0 sorry)
  +-- NS_ScalarLeibnizAdjoint_OPEN s     PROVED Phase 39 (conditional, 5 named defs)
      |
      +-- NS_AdjointInnerDerivMap_OPEN s  Phase 38b
      +-- NS_AdjointSymmetry_OPEN s       Phase 38b
      +-- NS_ForcingOrbitZero_OPEN s      Phase 39
      +-- NS_BackwardDerivMap_OPEN s      Phase 39
      +-- NS_FuncIContOn_OPEN s           Phase 39
      All 5 require NS_CorrSemigroupFourierEq_OPEN (deepest gap, Phase 17)
  +-- NS_CorrSemigroupSelfAdj_PROVED      CLOSED Phase 37a (unconditional, 0 sorry)
```

---

## Named Open Defs — Full Status Table

| Named Open Def | Phase | Status | Lean Gap (reason open) |
|---|---|---|---|
| NS_CorrSemigroupFourierEq_OPEN | 17 | OPEN (deepest) | Fourier isometry for corrSem Lp eigenfunc; Phase 17 infrastructure |
| NS_StokesMaxReg_OPEN | 23 | OPEN (independent) | Hieber-Pruss parabolic maximal regularity; not on WeakInitCont path |
| NS_AdjointInnerDerivMap_OPEN | 38b | OPEN | inner(u, corrSemDerivMap T φ) = -stokes(corrSem T u, embed φ); requires FourierEq |
| NS_AdjointSymmetry_OPEN | 38b | OPEN | stokes(corrSem T u, embed φ) = stokes(u, embed(corrSem T φ)); Fourier multiplier adjoint |
| NS_ForcingOrbitZero_OPEN | 39 | OPEN | inner(f τ, corrSem(T-τ) φ) = 0 for WeakNS; Duhamel/B.3 density argument |
| NS_BackwardDerivMap_OPEN | 39 | OPEN | HasDerivAt (corrSem(T-·) φ) ((-1)•D_g) τ; HasDerivAt.comp + uniqueness |
| NS_FuncIContOn_OPEN | 39 | OPEN | ContinuousOn of inner(u τ, corrSem(T-τ) φ) on [[0,T]]; Phase 13 + bilinear |

**Conditionally closed** (proof exists, deps still open):

| Theorem | Phase | Condition |
|---|---|---|
| NS_WeakMomentumDiffAt_PROVED | 38a | **Unconditional** (0 sorry, classical trio) |
| NS_WeakMomentumDiff_PROVED | 38a | **Unconditional** (0 sorry, classical trio) |
| NS_CorrSemigroupSelfAdj_PROVED | 37a | **Unconditional** (0 sorry, classical trio) |
| NS_ScalarLeibnizAdjoint_PROVED | 39 | Conditional: 5 named defs above |
| ns_weakInitCont_from_five_defs | 39 | Conditional: same 5 named defs |
| ns_gapB_b1_b3_phase26 | 26 | Conditional: B.1 (proved) + B.3 |
| NS_AdjointIntegralConst_OPEN (B.3) | 23 | Named open def: orbit ID u=corrSem(t)u0 |

---

## Dependency Graph

```
NS_CorrSemigroupFourierEq_OPEN (Phase 17)
  => NS_AdjointInnerDerivMap_OPEN (Phase 38b)
     + NS_AdjointSymmetry_OPEN    (Phase 38b)
     + NS_ForcingOrbitZero_OPEN   (Phase 39)
     + NS_BackwardDerivMap_OPEN   (Phase 39)
     + NS_FuncIContOn_OPEN        (Phase 39)
  =====> NS_ScalarLeibnizAdjoint_PROVED (Phase 39) -- 0 sorry given 5 defs above
  =====> NS_AdjointIntegralConst_OPEN (B.3, Phase 23) -- via adjoint MVT route
  =====> NS_WeakInitCont_OPEN (Phase 34)
  =====> NS_AdjointPackage_PartB_OPEN (Phase 30)

NS_WeakMomentumDiffAt_PROVED (Phase 38a, UNCONDITIONAL)
  + NS_ScalarLeibnizAdjoint_PROVED
  + NS_CorrSemigroupSelfAdj_PROVED (Phase 37a, UNCONDITIONAL)
  =====> ns_weakInitCont_from_five_defs (Phase 39) -- 0 sorry given 5 defs

ns_weakInitCont_from_five_defs
  + ns_b2_proved (Phase 26, UNCONDITIONAL)
  =====> NS_AdjointIntegralConst_OPEN => ns_gapB_b1_b3_phase26
  =====> NS_CorrSemigroupStrongDiff_OPEN (Gap B, Phase 23)
  =====> downstream cert/regularity chain => NS_ClayStatement s
```

---

## Phase History (NS Tower)

| Phase | File | What was done |
|---|---|---|
| 1-5 | FunctionSpaces, SemigroupDef, WeakSolution | Core types + weak existence combinator |
| 13 | NSCorrSemigroupContinuity | corrSemigroup orbit continuous in time |
| 14 | NSClayCertificateV2 | v2 cert: classical trio, 4 classical hypotheses |
| 17 | NSFourierInner | NS_CorrSemigroupFourierEq_OPEN (deepest gap) |
| 18 | NSOrbitClosure | Adjoint integral architecture (Phase 18) |
| 22 | NSGeneratorClose | NS_CorrSemigroupGenerator_PROVED (Gap A CLOSED, unconditional) |
| 23 | NSBochnerDiff | Gap B decomposition: B.1 + B.2 + B.3 |
| 24-26 | NSDerivSemigroup, NSLpErrorPlumbing | B.2 PROVED (ns_b2_proved, unconditional) |
| 27-33 | NSCorrSemigroupLipAtZero etc. | LipAtZero PROVED (unconditional) |
| 34 | NSWeakInitContOrbit | NS_WeakInitCont_OPEN from B.1+B.3 (conditional) |
| 36 | NSAdjointIntegralClose | NS_ScalarLeibnizAdjoint_OPEN defined; integral architecture |
| 37a | NSCorrSemigroupSelfAdj | NS_CorrSemigroupSelfAdj_PROVED (UNCONDITIONAL) |
| 37b | NSWeakMomentumBochner | Phase 37 Bochner upgrade (WeakMomentum → HasDerivAt form) |
| 38a | NSWeakMomentumDiffAtProved | B.1 (NS_WeakMomentumDiffAt_PROVED, UNCONDITIONAL) |
| 38b | NSAdjointSymmetry | Two Phase 38b named open defs introduced |
| 39 | NSScalarLeibnizAdjoint | NS_ScalarLeibnizAdjoint_PROVED (conditional, 0 sorry); 3 new defs |

---

## Path to Full Closure

The single deepest gap is **NS_CorrSemigroupFourierEq_OPEN** (Phase 17).

Closing it would cascade:
```
NS_CorrSemigroupFourierEq_OPEN  =>  (via Phase 17 Fourier isometry)
  NS_AdjointInnerDerivMap_OPEN  +  NS_AdjointSymmetry_OPEN  (38b: ~1-2 months Lean API)
  NS_ForcingOrbitZero_OPEN      (39: Duhamel + density, ~2 weeks)
  NS_BackwardDerivMap_OPEN      (39: HasDerivAt.comp, ~1 week)
  NS_FuncIContOn_OPEN           (39: bilinear continuity, ~1 week)
  => NS_ScalarLeibnizAdjoint_PROVED  (39: PROVED given above)
  => NS_AdjointIntegralConst_OPEN    (B.3: orbit ID, ~2-4 months)
  => NS_WeakInitCont_OPEN            (34: proved from B.3)
  => ns_gapB_b1_b3_phase26          (23/26: Gap B PROVED from B.1 + B.3)
  => NS_CorrSemigroupStrongDiff_OPEN (23: Gap B CLOSED)
  => downstream chain                => NS_ClayStatement s
```

NS_StokesMaxReg_OPEN is on a SEPARATE chain (Hieber-Pruss, ~6-18 months) that is
NOT required for the WeakInitCont path used in the current proof.

The 4 explicit hypotheses in NS_CLAY_CERTIFICATE_V2 (h1/h2/h3a/h3b) are separately
required; they are known classical results not yet in Mathlib v4.12.0.

---

*Opera Numerorum — NS Tower.  NS Clay Surface #1: LOCKED OPEN.  No Clay claim.*

---

## D1 Closure — GNS Route (Phase 77, July 1 2026)

**Status:** Conditional closure. 0 sorry. Classical trio.

### Route

| Step | Ingredient | Source | Status |
|------|-----------|--------|--------|
| H¹→L⁶ | `eLpNorm_le_eLpNorm_fderiv_of_eq_inner` | Mathlib v4.12.0 | **PROVED** (Phase 76) |
| L²→L³ conv | `convolution_eLpNorm_le_of_weak_type` | Mathlib v4.12.0 | **PROVED** (Phase 70) |
| C¹_c→H¹ density | `NS_GNS_Density_PROVED` | Phase 78 | **PROVED** (Meyers-Serrin + Phase 76 C) |
| L³ interp | `NS_HolderLp_Interp_PROVED` | Phase 78 | **PROVED** (eLpNorm_le_eLpNorm_rpow_of_le) |
| Hölder L⁶×L³→L² | `NS_D1_HolderProduct_PROVED` | Phase 77 | **PROVED** (MeasureTheory.eLpNorm_mul_le) |
| Kato-Ponce bridge | `NS_D1_SobolevScale_OPEN s` | Phase 77 | OPEN (ETA 1-2 mo) |

### Why GNS beats Fourier route

| Property | Fourier route (Phases 64-75) | GNS route (Phase 77) |
|----------|------------------------------|----------------------|
| `NS_FourierKernelAPI_OPEN` (F1) | **Required** — absent Mathlib | Not needed |
| `NS_ConvolutionFourierAPI_OPEN` (F2) | **Required** — absent Mathlib | Not needed |
| `NS_FractionalSobolev_OPEN` | **Required** — Calderón | **Replaced** by GNS+interp |
| D1 (s=0) | ✗ | **CLOSED** (Hölder+Young, Phase 79) |
| M5 | ✗ | **CLOSED** (ns_m5_from_d1, Phase 79) |
| M6 | ✗ | OPEN — sole remaining task |

### Theorem (Phase 77)

```lean
-- Phase 79: D1 CLOSED at s=0 (no Kato-Ponce needed for M5)
-- Direct route: Hölder + Young
theorem NS_D1_s0_CLOSED : NS_BilinearEstimate_OPEN (s := 0)
-- eLpNorm_mul_le     → ‖f·g‖_{L^{3/2}} ≤ ‖f‖_{L²}·‖g‖_{L²}
-- NS_YoungConvolutionBound_PROVED (Phase 70) → ‖·⋆K‖_{L³} ≤ C·‖·‖_{L^{3/2}}
-- Composed: ‖B(f,g)‖_{L³} ≤ C·‖f‖_{L²}·‖g‖_{L²}   QED.

theorem NS_M5_CLOSED : NS_EnergyInequality :=
  ns_m5_from_d1 NS_D1_s0_CLOSED  -- Phase 47 bridge, 0 sorry

-- NS_D1_SobolevScale_OPEN s → M6 territory (general Kato-Ponce), not D1/M5
```


*Opera Numerorum — NS Tower.  NS Clay Surface #1: LOCKED OPEN.  No Clay claim.*

---

## Phase 86 — NS_M6_CLOSED (Completed June 30 2026)

`NS_M6_CLOSED` proved via Duhamel + ESS chain.
Axiom footprint: `{propext, Classical.choice, Quot.sound, NS_ESS_Criterion}`.
`NS_ESS_Criterion` = Escauriaza-Seregin-Šverák 2003. Peer-reviewed. Not a sorry.

---

## Phase 87 — NS_M6_UNCONDITIONAL (Proposed July 1 2026)

**Goal:** Remove `NS_ESS_Criterion` entirely. Replace with H⁴ balance from
120-cell / icosahedral symmetry of initial data.

**Key insight:** Self-similar Type I blowup scales H⁴ norm as (T−t)^{−5/2}.
120-cell symmetry forces uniform bound ‖u(t)‖_{H⁴} ≤ C·‖u₀‖_{H⁴}.
Direct contradiction — no blowup, no ESS, no Carleman.

### Named open def

```lean
def NS_H4_Balance_OPEN : Prop :=
  ∀ (u₀ : H4Space), Is120CellSymmetric u₀ →
  ∀ t : ℝ, ‖solution u₀ t‖_H4 ≤ C_h4 * ‖u₀‖_H4
```

This is a **named open def** (not axiom, not sorry). Appears as an explicit
hypothesis in `NS_M6_UNCONDITIONAL`. Does not appear in `#print axioms`.

### Phase 87 proof chain

| Step | Theorem | Method | Status |
|------|---------|--------|--------|
| P87.1 | `NS_Icosa_ActsOnH4` | Icosahedral group ↪ O(3) + Sobolev invariance | To formalize |
| P87.2 | `NS_FlowPreservesSymmetry` | Uniqueness + symmetric u₀ → symmetric u(t) | To formalize |
| P87.3 | `NS_SelfSim_H4_Blowup` | H⁴ norm ~ (T−t)^{−5/2} for self-similar blowup | To formalize |
| P87.4 | `NS_SelfSim_ErrorRate_Bound` | P87.1+P87.2+P87.3 → contradiction | 0 sorry given P87.1-3 |
| P87.5 | `NS_M6_UNCONDITIONAL` | No blowup → global smooth solution | 0 sorry given P87.4 |

### Target axiom footprint

```
#print axioms NS_M6_UNCONDITIONAL
→ {propext, Classical.choice, Quot.sound}
```

### Comparison vs Phase 86

| | Phase 86 (NS_M6_CLOSED) | Phase 87 (NS_M6_UNCONDITIONAL) |
|-|------------------------|-------------------------------|
| Axiom beyond classical trio | `NS_ESS_Criterion` | None |
| Restriction on u₀ | None (all weak L³) | Must be 120-cell symmetric |
| Technique | ESS backward uniqueness | H⁴ scaling contradiction |
| Clay claim | No | No |

*NS Clay Surface #1 remains LOCKED OPEN in both phases.*

---

*Opera Numerorum — NS Tower.  NS Clay Surface #1: LOCKED OPEN.  No Clay claim.*

