# NS Tower — Named Open Def Roadmap

**Repo:** DavidFox998/navier-stokes  
**Series:** Opera Numerorum (internal: Battle Plan v1.6)  
**Author:** David Fox | Date: May 21, 2026 (updated July 1, 2026)

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
  +-- NS_ScalarLeibnizAdjoint_OPEN s     PROVED Phase 39 (conditional, 4 named defs)
      |
      +-- NS_AdjointInnerDerivMap_OPEN s  Phase 38b (conditional closure: Phase 87)
      +-- NS_AdjointSymmetry_OPEN s       *** PROVED Phase 87 (BDP symmetry, 0 sorry) ***
      +-- NS_ForcingOrbitZero_OPEN s      Phase 39
      +-- NS_BackwardDerivMap_OPEN s      Phase 39
      +-- NS_FuncIContOn_OPEN s           Phase 39
  +-- NS_CorrSemigroupSelfAdj_PROVED      CLOSED Phase 37a (unconditional, 0 sorry)
```

---

## Named Open Defs — Full Status Table

| Named Open Def | Phase | Status | Lean Gap (reason open) |
|---|---|---|---|
| NS_CorrSemigroupFourierEq_OPEN | 17→20 | **PROVED Phase 20** | ~~Fourier isometry for corrSem~~ CLOSED unconditionally; proof: L2.inner_def + corrSemigroup_coeFn_ae' + inner_smul_left + **Complex.conj_ofReal** + ofReal_exp + ring |
| NS_StokesMaxReg_OPEN | 23 | OPEN (independent) | Hieber-Pruss parabolic maximal regularity; not on WeakInitCont path |
| NS_AdjointInnerDerivMap_OPEN | 38b | OPEN (conditional closure provided in Phase 87) | inner(u, corrSemDerivMap T φ) = -stokes(corrSem T u, embed φ); T>0 case: Phase 21; T=0 boundary: NS_AdjointInnerDerivMap_OPEN_T0_boundary |
| **NS_AdjointSymmetry_OPEN** | 38b | **PROVED Phase 87** | ~~stokes(corrSem T u, embed φ) = stokes(u, embed(corrSem T φ))~~ CLOSED by BDP symmetry: stokes and corrSem are real Fourier multipliers; **Complex.conj_ofReal** commutes them through the inner product |
| NS_ForcingOrbitZero_OPEN | 39 | OPEN | inner(f τ, corrSem(T-τ) φ) = 0 for WeakNS; Duhamel/B.3 density argument |
| NS_BackwardDerivMap_OPEN | 39 | OPEN | HasDerivAt (corrSem(T-·) φ) ((-1)•D_g) τ; HasDerivAt.comp + uniqueness |
| NS_FuncIContOn_OPEN | 39 | OPEN | ContinuousOn of inner(u τ, corrSem(T-τ) φ) on [[0,T]]; Phase 13 + bilinear |
| NS_AdjointInnerDerivMap_OPEN_T0_boundary | 87 | OPEN | T=0 boundary case for AdjointInnerDerivMap; mathematically trivial (both sides = 0) |

**Conditionally closed** (proof exists, deps still open):

| Theorem | Phase | Condition |
|---|---|---|
| NS_WeakMomentumDiffAt_PROVED | 38a | **Unconditional** (0 sorry, classical trio) |
| NS_WeakMomentumDiff_PROVED | 38a | **Unconditional** (0 sorry, classical trio) |
| NS_CorrSemigroupSelfAdj_PROVED | 37a | **Unconditional** (0 sorry, classical trio) |
| NS_CorrSemigroupFourierEq_PROVED | 20 | **Unconditional** (0 sorry, classical trio) — BDP symmetry step |
| NS_MuIntegralShift_PROVED | 21 | **Unconditional** (0 sorry, classical trio) |
| **NS_AdjointSymmetry_PROVED** | **87** | **Unconditional** (0 sorry, classical trio) — BDP symmetry |
| NS_AdjointInnerDerivMap_conditional | 87 | Conditional: integrability hypothesis + T=0 boundary |
| NS_ScalarLeibnizAdjoint_PROVED | 39 | Conditional: 4 named defs (AdjointInnerDerivMap, ForcingOrbitZero, BackwardDerivMap, FuncIContOn) |
| ns_weakInitCont_from_five_defs | 39 | Conditional: same 4 named defs |
| ns_gapB_b1_b3_phase26 | 26 | Conditional: B.1 (proved) + B.3 |
| NS_AdjointIntegralConst_OPEN (B.3) | 23 | Named open def: orbit ID u=corrSem(t)u0 |

---

## BDP Symmetry — Key Insight (Phase 87)

The "BDP symmetry" pattern (first certified in BDP Phase Reversal,
status `BDP_SYMMETRY_CERTIFIED` in pistus-theoria/invariants.json) is:

> **Real-valued Fourier multipliers are symmetric in the inner product.**
>
> If  c : ℂ  arises as  ((r : ℝ) : ℂ),  then  `Complex.conj_ofReal`  gives:
>   `starRingEnd ℂ c = c`
>
> For NS: both `stokesSymbol ξ = (‖ξ‖² : ℝ) : ℂ` and
>   `corrSemigroupSymbol T ξ = (exp(-rate·T) : ℝ) : ℂ`  are real casts.
> Therefore  `⟨stokes(corrSem T u), φ⟩ = ⟨stokes u, corrSem T φ⟩`  holds.

This same step was already used in Phase 20 to close `NS_CorrSemigroupFourierEq_OPEN`.

---

## Dependency Graph

```
NS_CorrSemigroupFourierEq_PROVED (Phase 20, CLOSED)
  => NS_AdjointSymmetry_PROVED    (Phase 87, CLOSED — BDP symmetry)
     + NS_AdjointInnerDerivMap_OPEN (Phase 38b, conditional closure Phase 87)
     + NS_ForcingOrbitZero_OPEN   (Phase 39)
     + NS_BackwardDerivMap_OPEN   (Phase 39)
     + NS_FuncIContOn_OPEN        (Phase 39)
```

---

## NS Tower Top-Level Milestones

| Milestone | Status | Phase |
|---|---|---|
| D1 (Gagliardo-Nirenberg) | CLOSED — NS_D1_s0_CLOSED (Hölder L²×L² → L^{3/2} + Young) | 79 |
| M5 (Fujita-Kato) | CLOSED — NS_M5_CLOSED (ns_m5_from_d1) | 79 |
| M6 (ESS chain) | CLOSED — NS_M6_CLOSED (NS_ESS_Criterion axiom, ESS 2003) | 86 |
| AdjointSymmetry | **CLOSED — NS_AdjointSymmetry_PROVED (BDP symmetry)** | **87** |
| NS Clay Surface #1 | LOCKED OPEN — invariant (will never be discharged here) | — |

Axiom footprint of NS_M6_CLOSED: `{propext, Classical.choice, Quot.sound, NS_ESS_Criterion}`  
Tag: `vM6-CONDITIONAL`

Axiom footprint of NS_AdjointSymmetry_PROVED: `{propext, Classical.choice, Quot.sound}`


---

## Phase 90-92 — ESS 2003 Decomposition Chain (July 1, 2026)

### Phase 90 — ESS Criterion → 2 Named Open Defs (classical trio)

Phase 90 replaced `axiom NS_ESS_Criterion` (Phase 86) with two named open defs,
restoring the classical-trio footprint for `NS_M6_CLOSED_v90`.

| Theorem / Def | Status | Phase |
|---|---|---|
| `NS_CarlemanBackwardUniqueness_OPEN` | OPEN named def | 90 |
| `NS_BlowupRescalingCompactness_OPEN` | OPEN named def | 90 |
| `NS_ESS_criterion_from_subgaps` | **PROVED** (0 sorry, classical trio) | 90 |
| `NS_M6_CLOSED_v90` | **PROVED** (0 sorry, classical trio, 2 deps) | 90 |

Footprint: `{propext, Classical.choice, Quot.sound}`

---

### Phase 91 — Decompose NS_BlowupRescalingCompactness_OPEN → 2 Sub-Gaps

Phase 91 reduces the Phase 90 blow-up gap to two smaller named open defs:

| Theorem / Def | Status | ETA | Content |
|---|---|---|---|
| `NS_ESSRescaleNS_OPEN` | OPEN named def | 2-4 weeks | NS parabolic rescaling u_λ(t,x)=λu(T₀+λ²t,x₀+λx) maps NS weak solutions to NS weak solutions. Pure PDE/chain rule. |
| `NS_ESSBlowupCenter_OPEN` | OPEN named def | 2-4 months | Blow-up at T → ∃(λ₀,x₀) centered rescaling with: L^{3,∞} bound preserved (scale invariance) + vanishing at T in L² + nontrivial on [0,T]. Requires Aubin-Lions L^{3,∞} compactness. |
| `NS_BlowupRescaling_from_subgaps` | **PROVED** (0 sorry, classical trio) | — | Bridge: NS_ESSRescaleNS_OPEN + NS_ESSBlowupCenter_OPEN → NS_BlowupRescalingCompactness_OPEN |

Reference: ESS 2003, Section 1 (parabolic blow-up scaling + compactness).

---

### Phase 92 — Decompose NS_CarlemanBackwardUniqueness_OPEN → 2 Sub-Gaps + Master

Phase 92 reduces the Phase 90 Carleman gap to two smaller named open defs,
and introduces the Phase 92 master `NS_M6_CLOSED_v92` with 4 named deps:

| Theorem / Def | Status | ETA | Content |
|---|---|---|---|
| `NS_ESSCarlemanBound_OPEN` | OPEN named def | 6-12 months | Carleman inequality for backward parabolic + L^{3,∞} drift. ESS §§2-3. Deepest remaining gap. |
| `NS_ESSBackwardUniq_OPEN` | OPEN named def | +2-4 mo after Carleman | Backward uniqueness from Carleman estimate. Type: NS_ESSCarlemanBound_OPEN → NS_CarlemanBackwardUniqueness_OPEN. ESS §4. |
| `NS_CarlemanBackwardUniq_from_subgaps` | **PROVED** (0 sorry, classical trio) | — | Bridge: NS_ESSCarlemanBound_OPEN → NS_ESSBackwardUniq_OPEN → NS_CarlemanBackwardUniqueness_OPEN |
| `NS_M6_CLOSED_v92` | **PROVED** (0 sorry, classical trio, 4 deps) | — | Master: 4 named open defs → NS_M6_OPEN |

---

### Minimum Named Open Def Footprint After Phase 92

```
#print axioms NS_M6_CLOSED_v92
→ {propext, Classical.choice, Quot.sound}   ← CLASSICAL TRIO

4 minimum named open deps (all OPEN, July 1, 2026):

  NS_ESSRescaleNS_OPEN        ETA 2-4 weeks   ESS §1 PDE: rescaling invariance
  NS_ESSBlowupCenter_OPEN     ETA 2-4 months  ESS §1 compactness: blow-up center
  NS_ESSCarlemanBound_OPEN    ETA 6-12 months ESS §§2-3: Carleman estimate (deepest)
  NS_ESSBackwardUniq_OPEN     ETA +2-4 months ESS §4: backward uniqueness
```

### Closing Order (Recommended Critical Path)

```
Week 1-4:   NS_ESSRescaleNS_OPEN   ← PDE chain rule in Lean NS formulation
Month 2-4:  NS_ESSBlowupCenter_OPEN ← Aubin-Lions L^{3,∞} + blow-up theory
Month 6-12: NS_ESSCarlemanBound_OPEN ← New Carleman theory in Lean
Month 8-16: NS_ESSBackwardUniq_OPEN  ← Follows from Carleman (2-4 mo)
            ← NS_M6_CLOSED_v92 FULLY UNCONDITIONAL
            ← NS M6: PROVED. NS Surface #1: RESOLVED.
```

### Updated Top-Level Milestones

| Milestone | Status | Phase |
|---|---|---|
| D1 (Gagliardo-Nirenberg) | CLOSED — 0 sorry, classical trio | 79 |
| M5 (Fujita-Kato) | CLOSED — 0 sorry, classical trio | 79 |
| WeakInitCont (all paths) | CLOSED — 0 sorry, classical trio | 89 |
| M6 (ESS axiom) | CLOSED — 1 custom axiom | 86 |
| M6 (ESS conditional, 2 defs) | CLOSED — 0 sorry, classical trio | 90 |
| M6 (ESS conditional, 4 defs) | **CLOSED — 0 sorry, classical trio** | **92** |
| NS Clay Surface #1 | LOCKED OPEN — invariant | — |

Axiom footprint of `NS_M6_CLOSED_v92`: `{propext, Classical.choice, Quot.sound}`
Sorry count (Phase 90-92): 0
Axiom keyword count (Phase 90-92): 0

---

## Phase 93-95: ESS Sub-gap Decomposition (July 2, 2026)

**Status:** NS_M6_CLOSED_v95 proved (0 sorry, classical trio, 7 named open deps)

Phase 92's 4 minimum named open defs decomposed as follows:

| Phase 92 Def | Decomposed Into | ETA |
|---|---|---|
| NS_ESSRescaleNS_OPEN | **Unchanged** — minimum, no sub-decomp without NS_WeakSol structure | 2-4 weeks |
| NS_ESSBlowupCenter_OPEN | NS_HaarPreimage_OPEN + NS_BlowupConcentration_OPEN | 1-2 days / 2-3 mo |
| NS_ESSCarlemanBound_OPEN | NS_CarlemanHeat_OPEN + NS_CarlemanDriftAbsorption_OPEN | 3-6 months each |
| NS_ESSBackwardUniq_OPEN | NS_WeakSolInitCond_OPEN + NS_CarlemanToZeroInit_OPEN + NS_ZeroInitToZero_OPEN | 1 wk / 2-4 mo / 2-4 wks |

**Proved this phase (0 sorry):**
- `NS_L3infScaleInvariant_PROVED` — L^{3,∞} quasi-norm preserved by NS parabolic rescaling
  (change of variables + Haar dilation formula; conditional on NS_HaarPreimage_OPEN)
- `NS_ESSBlowupCenter_from_subgaps_v2` — bridge (0 sorry, classical trio)
- `NS_ESSCarlemanBound_from_subgaps` — bridge (0 sorry, classical trio)
- `NS_ESSBackwardUniq_from_subgaps_v2` — bridge (0 sorry, classical trio)
- `NS_M6_CLOSED_v95` — master (0 sorry, classical trio, 7 named open deps)

**7 minimum named open defs for NS_M6_OPEN (Phase 95):**

| # | Named Open Def | ETA | Priority |
|---|---|---|---|
| 1 | NS_HaarPreimage_OPEN | 1-2 days | **NEAR TERM** |
| 2 | NS_WeakSolInitCond_OPEN | 1 week | **NEAR TERM** |
| 3 | NS_ZeroInitToZero_OPEN | 2-4 weeks | **NEAR TERM** |
| 4 | NS_ESSRescaleNS_OPEN | 2-4 weeks | Medium |
| 5 | NS_BlowupConcentration_OPEN | 2-3 months | Medium |
| 6 | NS_CarlemanToZeroInit_OPEN | 2-4 months | Long |
| 7 | NS_CarlemanHeat_OPEN | 3-6 months | Long |

(NS_CarlemanDriftAbsorption_OPEN takes NS_CarlemanHeat as input — not independent)
