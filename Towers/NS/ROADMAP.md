# NS Tower Roadmap to Clay D3 Prize

**Opera Numerorum — David Fox.  July 2026.**

Machine-readable formal roadmap: `Towers/NS/NSRoadmap.lean`

---

## Current State — Phase Log

| File | Status | Content |
|------|--------|---------|
| NSPhase47BKMSurrogateClose | DONE | NS_CLAY_CERTIFICATE_V3 (3 explicit hyps, Cert_Arb_SurrogateSmooth) |
| NSPhase48DuhamelBridge | DONE | D1-D5 named open surfaces; D3 = Clay gap |
| NSPhase49GapReductionAdapt | DONE | gap_reduction ported; D2 proved given D1; h3a decomposed |
| NSPhase50SuperBric | DONE | 7-cycle gate; conditional D3 finite time / small data |
| NSRoadmap | DONE | Formal dependency DAG; M5 reduction; M6 Clay target |
| NSPhase52D5MasterBridge | DONE | Picard ratio arithmetic; D5 conditional bridge |
| NSPhase53GapClosure | DONE | Banach FPT proved (ContractingWith, 0 sorry); ns_picard_space_complete |
| NSPhase56D1Decomposition | DONE | ns_d1_from_product_estimate; SobolevInclusion embed_norm_le proved |
| NSPhase57PeetreDecomp | DONE | peetre_base proved (nlinarith); weight_peetre 0 sorry; NS_YoungLp_OPEN |
| NSPhase58YoungDecomp | DONE | NS_CauchySchwarzConv_OPEN; ns_d1_from_sub_surfaces chain |
| NSPhase59D1Closure | DONE | ns_d1_unconditional_from_cs; M5 reduction to CS (3-6 weeks) |
| NSPhase60SobolevLInf | DONE | Sobolev L∞ bound; peetre_base ξ 0 proved; H^{1/2}→L^3 scaffold |
| NSPhase61HLSStructure | DONE | HLS (Hardy-Littlewood-Sobolev) structural setup |
| NSPhase62RieszGeometry | DONE | Riesz potential geometry; riesz_kernel_weak_L65_cond |
| NSPhase63Marcinkiewicz | DONE | Marcinkiewicz interpolation scaffold |
| NSPhase64FourierBridge | DONE | NS_SobolevL3_Conditional (0 sorry conditional); 4 named open defs |
| NSPhase65VolumeClosure | DONE | Volume superlevel bridge |
| NSPhase66VolumeProof | DONE | NS_VolumeBallFormula_proved; NS_VolumeSuperlevel_Unconditional |
| NSPhase67YoungGap | DONE | Young-Lorentz L^2 × wk-L^{6/5}→L^3 gap decomposition |
| NSPhase68YoungConditional | DONE | NS_YoungConvolutionBound conditional |
| NSPhase69HLSGap | DONE | HLS micro-gap bridge; riesz_weak_norm_bound_cond |
| NSPhase70YoungClosure | DONE | NS_YoungConvolutionBound_PROVED (0 sorry); NS_WeakNormIsSup_Proved (0 sorry) |
| NSPhase71PlancherelClosure | DONE | NS_PlancherelIsometry_PROVED (0 sorry, eLpNorm_fourierIntegral_eq) |
| NSPhase72FourierChain | DONE | NS_SobolevFourierNorm proved; FourierRieszRep conditional; 3 sub-gaps |
| NSPhase73FourierSubgaps | DONE | weight_half_eq bridge; 3 Fourier API micro-gaps; FourierRieszRep_from_micro |

---

## Milestone Table

| Milestone | Description | Status | ETA |
|-----------|-------------|--------|-----|
| M1 | D2 proved given D1 | **PROVED** Phase 49 | done |
| M2 | h3a from Coercivity + Smoothing | **PROVED** Phase 49 | done |
| M3 | Clay_V3 given h1+h2+M2 | **PROVED** Phase 47+49 | done |
| M4 | D3 small data, t ≤ 7 (SuperBric gate) | **PROVED** Phase 50 | done |
| M5 | D3 small data, all t ≥ 0 (Fujita-Kato) | OPEN | weeks (once D1 closes) |
| M6 | D3 all smooth data, all t ≥ 0 | CLAY PRIZE | open |

---

## Named Open Surfaces — July 2026

| Gap | Content | ETA | Blocks |
|-----|---------|-----|--------|
| GAP F1 | NS_FourierKernelAPI_OPEN (𝓕(‖·‖^{-5/2}) = C·‖ξ‖^{-1}) | **days** (Phase 74 #check) | D1 |
| GAP F2 | NS_ConvolutionFourierAPI_OPEN (𝓕(f⋆K) = 𝓕f·𝓕K) | **days** (Phase 74 #check) | D1 |
| GAP F3 | NS_FourierInversionAPI_OPEN (𝓕⁻¹(𝓕f) = f a.e.) | **days** (Phase 74 #check) | D1 |
| GAP 2 | NS_BilinearEstimate (D1: Sobolev L^3 → bilinear) | days–weeks (after F1-F3) | **M5 CRITICAL** |
| GAP 1 | Cert_Arb_SurrogateSmooth (DCT differentiability) | 2-4 weeks | M3, M4 |
| GAP 3 | NS_StokesCoercivity (Poincaré on Hdiv_free) | 3-6 months | M2, M3 |
| GAP 4 | NS_AubinLions (Rellich compact embedding) | 3-6 months | M3 |
| GAP 5 | NS_NonlinearWeakForm (trilinear b(u,v,φ)) | 3-6 months | M3 |
| GAP 6 | NS_SemigroupSmoothing (Kato/Pazy C0-semigroup) | 12-18 months | M2 |
| GAP 7 | NS_BKMCriterion (Beale-Kato-Majda 1984) | 12-18 months | BKM path |
| GAP 8 | NS_FujitaKatoGlobal (all smooth data) | CLAY PRIZE prereq | M6 |
| GAP 9 | NS_Clay_D3_Prize (global regularity target) | CLAY PRIZE | — |

**GAP F1–F3 are the current critical path** (Phase 74, ETA days).

---

## Critical Path to M5 (Fujita-Kato, revised July 2026)

### Phase 73 state — D1 subchain

```
GAP F1: NS_FourierKernelAPI_OPEN
  𝓕(‖·‖^{-5/2})(ξ) = C · ‖ξ‖^{-1}  [Riesz kernel symbol, #check phase 74]
    |
GAP F2: NS_ConvolutionFourierAPI_OPEN
  𝓕(f ⋆ K) = 𝓕f · 𝓕K              [convolution theorem, #check phase 74]
    |
GAP F3: NS_FourierInversionAPI_OPEN
  𝓕⁻¹(𝓕f) = f a.e.                 [inversion on L², #check phase 74]
    |
    +---> NS_FourierRieszRep_OPEN (conditional, Phase 72+73)
    |     I_{1/2}f = C₀ · 𝓕⁻¹(‖ξ‖⁻¹ · 𝓕f)
    |
    +---> NS_SobolevL3_Conditional (Phase 64, proved 0 sorry conditional)
    |     f ∈ H^{1/2} → ‖f‖_{L³} ≤ C · ‖f‖_{H^{1/2}}
    |
    v
GAP 2: NS_BilinearEstimate_OPEN (D1)
  ‖B(u,v)‖_{H^s} ≤ C · ‖u‖_{H^{s+1}} · ‖v‖_{H^{s+1}}
    |
    v (Phase 49, proved)
D2: NS_DuhamelIntegralWellDef_OPEN
    |
    v (Phase 53, proved — ContractingWith.fixedPoint in Mathlib)
Banach FPT: fixed point of Picard map
    |
    v (+ Cert_Arb_SurrogateSmooth, Phase 47)
M5: D3 for small initial data, all t ≥ 0
```

### Previously closed (Phase 70-73)

```
NS_VolumeSuperlevel_Unconditional (Phase 66) ✓
  |
NS_WeakNormIsSup_Proved (Phase 70) ✓
NS_YoungConvolutionBound_PROVED (Phase 70) ✓
  L² × weak-L^{6/5} → L³ convolution bound (0 sorry)
NS_PlancherelIsometry_PROVED (Phase 71) ✓
  ‖f‖_{L²} = ‖𝓕f‖_{L²} (0 sorry, Mathlib eLpNorm_fourierIntegral_eq)
weight_half_eq (Phase 73) ✓
  ofReal((1+‖ξ‖²)^{s/2}) = weight s ξ ^ (1/2)
NS_SobolevFourierNorm_Proved (Phase 72+73) ✓
  eLpNorm bridge: (1+‖ξ‖²)^{s/2} · 𝓕f and weight(s/2)ξ · 𝓕f same norm
```

---

## Gap from M5 to M6 (Clay Prize)

M5 proves: if ‖u₀‖_{H^{s+2}} ≤ ν / (2·C_D1), the NS solution is globally smooth.

M6 requires: for ANY smooth u₀ (no smallness condition), the NS solution is globally smooth.

The gap between M5 and M6 has been open since Leray 1934. No known approach closes it for 3D.

---

## Axiom Footprint (July 2026)

```
NS_CLAY_CERTIFICATE_V3 (Phase 47):
  {propext, Classical.choice, Quot.sound, Cert_Arb_SurrogateSmooth}
  + explicit hyps: h1, h2, h3a

NS_CLAY_CERTIFICATE_V2 (NSClayCertificateV2.lean):
  {propext, Classical.choice, Quot.sound}
  + explicit hyps: h1, h2, h3a, h3b

ns_milestone_6_clay (NSRoadmap.lean):
  {propext, Classical.choice, Quot.sound}
  + NS_FujitaKatoGlobal_OPEN (Clay prize hypothesis)

NS_SobolevL3_Conditional (Phase 64, Phase 70-73):
  {propext, Classical.choice, Quot.sound}
  + NS_PlancherelIsometry_OPEN ✓ CLOSED (Phase 71)
  + NS_FourierRieszRep_OPEN    ← conditional (Phase 72+73)
  + NS_SobolevFourierNorm_OPEN ✓ CLOSED (Phase 72+73)
  + NS_YoungConvolutionBound_OPEN ✓ CLOSED (Phase 70)
  + NS_VolumeSuperlevel_OPEN   ✓ CLOSED (Phase 66)
```

D3 OPEN. No Clay claim.

---

## Phase 74 — Immediate Next Steps

Run these `#check`s and close the 3 micro-gaps:

```lean
#check MeasureTheory.fourierIntegral_rpow_eq     -- Riesz kernel symbol
#check VectorFourier.convolution_fourierIntegral  -- convolution theorem
#check VectorFourier.fourierIntegral_fourierIntegral -- inversion
```

Once all 3 close → `NS_FourierRieszRep_OPEN` unconditional → `NS_SobolevL3_Conditional` fires → D1 gate open.

---

*Author: David J. Fox, ORCID 0009-0008-1290-6105, Aberdeen/Seattle WA.*
*Opera Numerorum — Battle Plan v1.6 (internal).*
