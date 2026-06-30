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
