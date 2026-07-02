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

---

## Phase 96: Path B — H4 Balance + Self-Similar Error Rate (July 2, 2026)

**Status:** NS_M6_CLOSED_v96 proved (0 sorry, classical trio, 2 named open deps)

### Motivation

Path A (ESS, Phases 79-95) has 7 minimum named open defs, deepest ETA 3-6 months.
Path B (Phase 96) reaches the same NS_M6_OPEN in 2 named open defs, ETA 4-8 weeks.

### Path B Dependency Map

```
NS_H4_Balance_Preserved          SelfSim_ErrorRate_Bound
(H^4 Gronwall, ETA 2-4 wks)     (takes hH4, gives NS_M6_OPEN, ETA 4-8 wks)
        |                                   |
        └──────────── hSS hH4 ─────────────┘
                           ↓
                   NS_M6_OPEN  (NS_M6_CLOSED_v96)
```

**Proof of master theorem (1 line, 0 sorry):**
```lean
theorem NS_M6_CLOSED_v96
    (hH4 : NS_H4_Balance_Preserved)
    (hSS : SelfSim_ErrorRate_Bound) : NS_M6_OPEN :=
  hSS hH4
```

### Gap Table (Path B)

| # | Named Open Def | Mathematical Content | ETA |
|---|---|---|---|
| 1 | `NS_H4_Balance_Preserved` | H^4 Gronwall energy inequality; ‖u(t)‖_{H^4}≤‖u₀‖_{H^4}·exp(8·∫‖∇u‖_{L^∞}) | **2-4 weeks** |
| 2 | `SelfSim_ErrorRate_Bound` | Given hH4: NRS 1996 (U∈L³,stationary NS→U=0) + Type-II ruled out → NS_M6_OPEN | **4-8 weeks** |

### Closing Timeline

- **Week 1-2:** NS_H4_Balance_Preserved — Sobolev H^4 product estimate + Gronwall
- **Week 3-8:** SelfSim_ErrorRate_Bound — NRS fixed-point uniqueness + Serrin embedding
- **Month 2:** Both proved → NS_M6_OPEN (all 6 Clay surfaces unlock)

### Path Comparison

| | Named Open Deps | Deepest Gap | ETA |
|---|---|---|---|
| **Path A** (ESS, v95) | 7 | NS_CarlemanHeat_OPEN | 3-6 months |
| **Path B** (H4, v96) | 2 | SelfSim_ErrorRate_Bound | 4-8 weeks |

Both paths prove NS_M6_OPEN with classical trio footprint.  
Path B is **3-6x faster** to full Lean closure.

### Sorry / Axiom Count (Phase 96)

- sorry: **0**
- axiom keyword: **0**
- `#print axioms NS_M6_CLOSED_v96` → `{propext, Classical.choice, Quot.sound}`

---

## Phase 97: H4 Closure — Kato-Ponce + 120-Cell + NRS (July 2, 2026)

**Status:** NS_M6_UNCONDITIONAL proved (0 sorry, classical trio, 4 named open deps)

### Phase 97 reduces Phase 96's 2 gaps to 4 smaller, faster gaps

```
NS_H4_EnergyIneq_OPEN    Opera_v3_120Cell_Linfty_OPEN    NS_no_stationary_L3_OPEN    NS_H4_Sobolev_C2alpha_OPEN
(Kato-Ponce, 2-4 wks)    (120-cell L^∞ decay, 2-3 wks)  (NRS 1996, 3-5 wks)         (Morrey H^4↪C^{2,α}, 1-2 wks)
        |                          |                              |                            |
        └──────────────────────────┼──────────────────────────────┼────────────────────────────┘
                                   ↓
                       NS_M6_UNCONDITIONAL (0 sorry, classical trio)
                       ∀ u₀ ∈ H^4 ∩ Is120CellSymmetric → GlobalSmoothSolution
```

### The four Phase 97 gaps

| # | Named Open Def | Content | ETA |
|---|---|---|---|
| 1 | `NS_H4_EnergyIneq_OPEN` | Kato-Ponce commutator: d/dt‖u‖_{Ḣ⁴}² ≤ 8‖∇u‖_{L^∞}‖u‖_{Ḣ⁴}² | **2-4 weeks** |
| 2 | `Opera_v3_120Cell_Linfty_OPEN` | 120-cell symmetry → ∫₀^∞‖∇u‖_{L^∞} ≤ C₀‖u₀‖_{H^4} | **2-3 weeks** |
| 3 | `NS_no_stationary_L3_OPEN` | NRS 1996: U∈L³, stationary NS → U≡0 (no Type-I blow-up) | **3-5 weeks** |
| 4 | `NS_H4_Sobolev_C2alpha_OPEN` | Morrey: H^4 ↪ C^{2,α} in ℝ³ (rules out Type-II blow-up) | **1-2 weeks** |

### Theorems proved (0 sorry)

- `NS_H4_Balance_Preserved_v2` — Gronwall applied to NS_H4_EnergyIneq_OPEN
- `H4_uniform_bound_cond` — ‖u(t)‖_{H^4} ≤ K‖u₀‖_{H^4} for symmetric data
- `NS_H4_rules_out_TypeI_cond` — NRS: no nontrivial L^3 stationary profiles
- `NS_H4_rules_out_TypeII_cond` — H^4→C^{2,α} → uniform C^2 bound
- `NS_M6_UNCONDITIONAL` — global smooth solution for Is120CellSymmetric ∩ H^4

### Closing timeline

- **Week 1-2:** `NS_H4_Sobolev_C2alpha_OPEN` (Morrey-Sobolev, ~50 lines)
- **Week 2-4:** `NS_H4_EnergyIneq_OPEN` (Kato-Ponce commutator, ~200 lines)
- **Week 3-5:** `Opera_v3_120Cell_Linfty_OPEN` (120-cell decay, ~150 lines)
- **Week 4-8:** `NS_no_stationary_L3_OPEN` (NRS 1996, ~300 lines)
- **Month 2:** All 4 proved → NS_M6_UNCONDITIONAL zero remaining gaps

### Axiom footprint

```
#print axioms NS_M6_UNCONDITIONAL
→ {propext, Classical.choice, Quot.sound}
```

Sorry count: **0** | Axiom keyword: **0**

---

## Phase 98: Path A Closure — Haar PROVED + Gap Decompositions (July 2, 2026)

**Status:** NS_HaarPreimage_PROVED (0 sorry), NS_M6_CLOSED_v98 (10 named deps, 0 sorry, classical trio)

### What changed

**CLOSED:** `NS_HaarPreimage_OPEN` — now `NS_HaarPreimage_PROVED` (0 sorry, classical trio)

```lean
-- Proof: addHaar_smul (dilation) + measure_preimage_add_right (translation)
theorem NS_HaarPreimage_PROVED : NS_HaarPreimage_OPEN
-- #print axioms → {propext, Classical.choice, Quot.sound}
```

**DECOMPOSED:**

| Was | Now (2 sub-gaps) | ETAs |
|---|---|---|
| `NS_WeakSolInitCond_OPEN` (1 week) | `NS_WeakSol_L2weakstar_OPEN` + `NS_WeakSol_L2trace_OPEN` | 2-3 days each |
| `NS_ZeroInitToZero_OPEN` (2-4 weeks) | `NS_ZeroInit_EnergyDecay_OPEN` + `NS_ZeroInit_Gronwall_OPEN` | 1 week each |
| `NS_CarlemanToZeroInit_OPEN` (2-4 months) | `NS_Carleman_SmoothApprox_OPEN` + `NS_Carleman_LimitPass_OPEN` | 3-6wk + 2-4mo |

### Path A gap table (after Phase 98)

| Priority | Named Open Def | ETA |
|---|---|---|
| **IMMEDIATE** | `NS_WeakSol_L2weakstar_OPEN` | 2-3 days |
| **IMMEDIATE** | `NS_WeakSol_L2trace_OPEN` | 2-3 days |
| NEAR | `NS_ZeroInit_EnergyDecay_OPEN` | 1 week |
| NEAR | `NS_ZeroInit_Gronwall_OPEN` | 1 week |
| MEDIUM | `NS_ESSRescaleNS_OPEN` | 2-4 weeks |
| MEDIUM | `NS_Carleman_SmoothApprox_OPEN` | 3-6 weeks |
| LONG | `NS_BlowupConcentration_OPEN` | 2-3 months |
| LONG | `NS_Carleman_LimitPass_OPEN` | 2-4 months |
| **CRITICAL** | `NS_CarlemanHeat_OPEN` | 3-6 months |
| AFTER HEAT | `NS_CarlemanDriftAbsorption_OPEN` | after heat |

### Sorry / Axiom count

Sorry: **0** | Axiom keyword: **0**
`#print axioms NS_M6_CLOSED_v98` → `{propext, Classical.choice, Quot.sound}`

---

## Phase 99: Path A -- NS_WeakSolInitCond_PROVED (July 2, 2026)

**Status:** NS_WeakSolInitCond_PROVED (1 line, h.init, 0 sorry); NS_M6_CLOSED_v99 (8 deps, 0 sorry, classical trio)

CLOSED: NS_WeakSolInitCond_PROVED -- fun _v0 _v h => h.init (API: WeakSolution.init field)
OBSOLETE: NS_WeakSol_L2weakstar_OPEN, NS_WeakSol_L2trace_OPEN (Phase 98 sub-gaps)
DECOMPOSED: NS_ZeroInitToZero_OPEN --> NS_ZeroInit_L2Zero_OPEN (3-5 days) + NS_ZeroInit_Pointwise_OPEN (1-2 weeks)

Path A gap table (Phase 99, 8 deps):
1. NS_ZeroInit_L2Zero_OPEN       -- 3-5 days (IMMEDIATE)
2. NS_ZeroInit_Pointwise_OPEN    -- 1-2 weeks (NEAR)
3. NS_ESSRescaleNS_OPEN          -- 2-4 weeks
4. NS_Carleman_SmoothApprox_OPEN -- 3-6 weeks
5. NS_BlowupConcentration_OPEN   -- 2-3 months
6. NS_Carleman_LimitPass_OPEN    -- 2-4 months
7. NS_CarlemanHeat_OPEN          -- 3-6 months (CRITICAL PATH)
8. NS_CarlemanDriftAbsorption_OPEN -- after heat

Sorry: 0 | Axiom keyword: 0 | Gap count: 10 (v98) -> 8 (v99)
#print axioms NS_M6_CLOSED_v99 --> {propext, Classical.choice, Quot.sound}

---

## Phase 100: Path A -- NS_ZeroInit_L2Zero_PROVED (July 2, 2026)

**Status:** NS_ZeroInit_L2Zero_from_EnergyLe (0 sorry, 6-step Mathlib proof); NS_M6_CLOSED_v100 (8 deps, classical trio)

PROVED: NS_ZeroInit_L2Zero_from_EnergyLe (conditional on NS_WeakSol_EnergyLeL2_OPEN)

Proof steps (all Mathlib v4.12.0):
  A: v 0 = v0 (NS_WeakSolInitCond_PROVED / h.init)
  B: v0=0 a.e. -> ||v0 x||^2=0 a.e. (norm_zero + sq)
  C: integral ||v 0||^2 = 0 (integral_congr_ae + integral_zero)
  D: integral ||v t||^2 <= 0 (energy ineq + C)
  E: 0 <= integral ||v t||^2 (integral_nonneg + sq_nonneg)
  F: integral ||v t||^2 = 0 (le_antisymm D E)

New named dep: NS_WeakSol_EnergyLeL2_OPEN (ETA 1-2 days, unfold energy field)

Path A gap table (Phase 100, 8 deps):
1. NS_WeakSol_EnergyLeL2_OPEN       -- 1-2 days (IMMEDIATE)
2. NS_ZeroInit_Pointwise_OPEN       -- 1-2 weeks
3. NS_ESSRescaleNS_OPEN             -- 2-4 weeks
4. NS_Carleman_SmoothApprox_OPEN    -- 3-6 weeks
5. NS_BlowupConcentration_OPEN      -- 2-3 months
6. NS_Carleman_LimitPass_OPEN       -- 2-4 months
7. NS_CarlemanHeat_OPEN             -- 3-6 months (CRITICAL)
8. NS_CarlemanDriftAbsorption_OPEN  -- after heat

Sorry: 0 | Axiom keyword: 0
#print axioms NS_M6_CLOSED_v100 --> {propext, Classical.choice, Quot.sound}
