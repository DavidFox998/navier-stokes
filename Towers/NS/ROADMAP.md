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
