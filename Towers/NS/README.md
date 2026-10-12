# Towers/NS — Navier–Stokes formalization (Lean 4)

## What this is
A Lean 4 formalization program for the Clay Navier–Stokes existence-and-smoothness problem: do globally smooth solutions exist for smooth, square-integrable initial data on ℝ³? The program's live core (October 2026, Wall266) is machine-checked analytic infrastructure — trilinear estimates, Sobolev embeddings, and the Bogovskii divergence-correction operator.

## What is proved

Marquee results (theorem names + file + last-touch commit):

| Theorem | File | Content | Commit |
|---|---|---|---|
| `H4_BKM_constant_lt_11` | `Wall266_TrilinearForm.lean` | Explicit H⁴ trilinear constant C = (1+φ)/(2−φ)/5 < 11 | `f70c63c 2026-10-08` |
| `H4_controls_trilinear` | `Wall266_TrilinearForm.lean` | Trilinear form controlled by H⁴ norm (120-cell symmetric data) | `f70c63c 2026-10-08` |
| `trilinearForm_bound` | `Wall266_L2Extension.lean` | L² extension: |b| ≤ C·‖w‖ via Phase 104 mollification | `f70c63c 2026-10-08` |
| `H4_controls_trilinear_REAL` | `Wall266_L2Extension.lean` | Real-typed form of the trilinear bound | `f70c63c 2026-10-08` |
| `H1_embedding_L4` | `Wall266_H4L4.lean` | H¹ → L⁴ Sobolev embedding (+ compact/GN variants) | `f70c63c 2026-10-08` |
| `sobolevConstant_H4_eq / _pos` | `NSPhase97aSobolevC2alphaClose.lean` | H⁴ → C^{2,α} embedding, constant π/(4√2) | `f70c63c 2026-10-08` |
| `BogovskiiDiv_closed` | `Wall266_Bogovskii.lean` | Bogovskii divergence identity (branch claude-bogovskii-kernel-closed) | `9400ca7 2026-10-09` |
| `bogovskii_L2_bound` | `Wall266_Bogovskii.lean` | ‖Bf‖₂ ≤ 16·M·vol(B(0,1))·R·‖f‖₂ (branch, lemma) | `9400ca7 2026-10-09` |
| `NS_M6_CLOSED_v104` | `NSPhase104SmoothApprox.lean` | Zero-initial-datum case only, conditional on four OPEN hypotheses | `f70c63c 2026-10-08` |

Full tree: **702 theorems/lemmas across 134 files, zero `sorry`/`admit`** (comment-aware verified 2026-10-12). **9 named axioms**, all disclosed: `Cert_Arb_NS_Gate1`, `Cert_Arb_NS_Gate2`, `Cert_Arb_NS_LocalReg`, `Cert_Arb_NS_BKMStrong` (`NSExpDecayClose.lean`), `Cert_Arb_ExpIntegralZero`, `Cert_Arb_WeakForcingIsZero`, `Cert_Arb_StokesMaxReg`, `Cert_Arb_SurrogateSmooth`, `NS_ESS_Criterion` (`NSPhase86M6Close.lean`).

Per-file ledger (theorems proved · `_OPEN`s declared · last commit):

| File | Theorems | OPENs | Last commit |
|---|---|---|---|
| `Compactness.lean` | 2 | 0 | `383adf7 2026-06-21` |
| `Divergence.lean` | 8 | 0 | `383adf7 2026-06-21` |
| `Energy.lean` | 5 | 0 | `383adf7 2026-06-21` |
| `EnergyIneq.lean` | 21 | 0 | `383adf7 2026-06-21` |
| `EnergyV2.lean` | 24 | 0 | `383adf7 2026-06-21` |
| `FunctionSpaces.lean` | 7 | 0 | `383adf7 2026-06-21` |
| `GalerkinApprox.lean` | 3 | 0 | `383adf7 2026-06-21` |
| `H4_Averaging.lean` | 6 | 0 | `f6caa69 2026-07-01` |
| `H4_Energy.lean` | 4 | 0 | `a2f3823 2026-07-01` |
| `H4_Forcing.lean` | 3 | 0 | `53976b7 2026-07-01` |
| `H4_UniformBound.lean` | 4 | 0 | `7500857 2026-07-01` |
| `Leray.lean` | 6 | 0 | `383adf7 2026-06-21` |
| `NSAdjointArgument.lean` | 4 | 2 | `5f2b30b 2026-06-29` |
| `NSAdjointIntegralClose.lean` | 6 | 2 | `3f882a8 2026-06-30` |
| `NSAdjointPackageClose.lean` | 6 | 1 | `f378585 2026-06-29` |
| `NSAdjointPackagePartBClose.lean` | 5 | 1 | `3cf5b11 2026-06-29` |
| `NSAdjointSymmetry.lean` | 2 | 2 | `90bb2d3 2026-06-30` |
| `NSAubinLionsDecomp.lean` | 5 | 3 | `444099f 2026-06-28` |
| `NSBochnerDiff.lean` | 3 | 3 | `ddcc0fc 2026-06-29` |
| `NSCanonicalSurfaces.lean` | 7 | 1 | `d29ac39 2026-06-28` |
| `NSClayCertificate.lean` | 6 | 0 | `ba3de97 2026-07-01` |
| `NSClayCertificateV2.lean` | 3 | 0 | `13661f7 2026-06-30` |
| `NSClayCombinator.lean` | 3 | 3 | `7a184a9 2026-06-28` |
| `NSCollection.lean` | 24 | 0 | `90cbf3c 2026-07-01` |
| `NSCorrSemigroupContinuity.lean` | 7 | 1 | `6d37adc 2026-06-30` |
| `NSCorrSemigroupLipAtZero.lean` | 4 | 0 | `0a2684e 2026-06-30` |
| `NSCorrSemigroupSelfAdj.lean` | 3 | 0 | `a1fb022 2026-06-30` |
| `NSCorrSemigroupSmooth.lean` | 4 | 1 | `78338d8 2026-06-29` |
| `NSDerivSemigroup.lean` | 14 | 1 | `d50abda 2026-06-30` |
| `NSExpDecayClose.lean` | 9 | 0 | `3b9044f 2026-07-01` |
| `NSFourierInner.lean` | 4 | 1 | `025a1b7 2026-06-29` |
| `NSGate2Decomp.lean` | 4 | 3 | `152b517 2026-06-28` |
| `NSGate3Decomp.lean` | 4 | 4 | `e57639d 2026-06-28` |
| `NSGeneratorClose.lean` | 6 | 2 | `82daf0b 2026-06-29` |
| `NSKPBridge.lean` | 6 | 2 | `7a8aaef 2026-06-28` |
| `NSLPKPCertificate.lean` | 3 | 0 | `4d4cda6 2026-06-28` |
| `NSLPProjectors.lean` | 11 | 1 | `843dd6a 2026-06-28` |
| `NSLittlewoodPaley.lean` | 5 | 1 | `5e61d74 2026-06-28` |
| `NSLpErrorPlumbing.lean` | 8 | 0 | `73ff5e6 2026-06-29` |
| `NSMuIntegralShift.lean` | 10 | 0 | `294a2aa 2026-06-29` |
| `NSNonlinearTerm.lean` | 2 | 3 | `1d85939 2026-06-28` |
| `NSOrbitClosure.lean` | 3 | 5 | `c8338b6 2026-06-29` |
| `NSParametricDiff.lean` | 9 | 0 | `3e062cc 2026-06-29` |
| `NSPhase100L2ZeroClose.lean` | 3 | 1 | `d0e75ef 2026-07-01` |
| `NSPhase101EnergyLeL2.lean` | 5 | 10 | `ae9ef09 2026-07-01` |
| `NSPhase102ZeroInitPointwise.lean` | 5 | 7 | `c0407fa 2026-07-01` |
| `NSPhase103ESSRescaling.lean` | 5 | 6 | `e2165d2 2026-07-01` |
| `NSPhase104SmoothApprox.lean` | 6 | 8 | `f70c63c 2026-10-08` |
| `NSPhase105BlowupConcentration.lean` | 2 | 6 | `84a9186 2026-07-01` |
| `NSPhase106CarlemanHeat.lean` | 2 | 6 | `7526f7a 2026-07-01` |
| `NSPhase107CarlemanDrift.lean` | 2 | 4 | `aab0107 2026-07-01` |
| `NSPhase108LimitPass.lean` | 3 | 3 | `d2029d5 2026-07-01` |
| `NSPhase40AdjClose.lean` | 6 | 0 | `42c00bf 2026-06-30` |
| `NSPhase41ThreeGaps.lean` | 4 | 0 | `e699a9c 2026-06-30` |
| `NSPhase42ZeroForcing.lean` | 4 | 0 | `640ddbb 2026-06-30` |
| `NSPhase43ForcingOrbitZero.lean` | 7 | 2 | `95b3741 2026-06-30` |
| `NSPhase44ExpIntegral.lean` | 4 | 0 | `564786c 2026-06-30` |
| `NSPhase45WeakForcingIsZero.lean` | 5 | 0 | `5dfc716 2026-06-30` |
| `NSPhase46StokesMaxReg.lean` | 3 | 0 | `2ccdea9 2026-06-30` |
| `NSPhase47BKMSurrogateClose.lean` | 4 | 0 | `cb04336 2026-06-30` |
| `NSPhase48DuhamelBridge.lean` | 1 | 5 | `1d34e18 2026-06-30` |
| `NSPhase49GapReductionAdapt.lean` | 5 | 2 | `e912018 2026-06-30` |
| `NSPhase50SuperBric.lean` | 8 | 1 | `15df785 2026-06-30` |
| `NSPhase52D5MasterBridge.lean` | 7 | 5 | `518190e 2026-06-30` |
| `NSPhase53GapClosure.lean` | 10 | 0 | `2259aa5 2026-06-30` |
| `NSPhase56D1Decomposition.lean` | 5 | 1 | `6547f04 2026-06-30` |
| `NSPhase57PeetreDecomp.lean` | 4 | 1 | `c7e3c9a 2026-06-30` |
| `NSPhase58YoungDecomp.lean` | 2 | 2 | `41392c1 2026-06-30` |
| `NSPhase59D1Closure.lean` | 2 | 0 | `b0ee3bc 2026-06-30` |
| `NSPhase60SobolevLInf.lean` | 7 | 6 | `99514eb 2026-06-30` |
| `NSPhase61HLSStructure.lean` | 1 | 8 | `cb7fdf4 2026-06-30` |
| `NSPhase62RieszGeometry.lean` | 2 | 4 | `d3807b1 2026-06-30` |
| `NSPhase63Marcinkiewicz.lean` | 0 | 5 | `1302725 2026-07-01` |
| `NSPhase64FourierBridge.lean` | 2 | 4 | `4359499 2026-07-01` |
| `NSPhase65VolumeClosure.lean` | 3 | 1 | `923f2a6 2026-07-01` |
| `NSPhase66VolumeProof.lean` | 3 | 0 | `cedae3e 2026-07-01` |
| `NSPhase67YoungGap.lean` | 1 | 3 | `8edf28e 2026-07-01` |
| `NSPhase68YoungConditional.lean` | 2 | 0 | `186cbe5 2026-07-01` |
| `NSPhase69HLSGap.lean` | 1 | 2 | `70fc109 2026-07-01` |
| `NSPhase70YoungClosure.lean` | 4 | 0 | `ea9969d 2026-07-01` |
| `NSPhase71PlancherelClosure.lean` | 1 | 0 | `ea9969d 2026-07-01` |
| `NSPhase72FourierChain.lean` | 2 | 3 | `a4ec749 2026-07-01` |
| `NSPhase73FourierSubgaps.lean` | 7 | 3 | `2d78bde 2026-07-01` |
| `NSPhase74FourierAudit.lean` | 4 | 3 | `e42d0a2 2026-07-01` |
| `NSPhase75ExponentCorrection.lean` | 1 | 3 | `f971823 2026-07-01` |
| `NSPhase76GNSRoute.lean` | 2 | 3 | `8a7d0d1 2026-07-01` |
| `NSPhase77D1Closure.lean` | 2 | 1 | `a444322 2026-07-01` |
| `NSPhase78GNSInterpClose.lean` | 3 | 0 | `569e934 2026-07-01` |
| `NSPhase79D1M5Closed.lean` | 2 | 1 | `3bb1d57 2026-07-01` |
| `NSPhase80M6Routes.lean` | 2 | 3 | `b3dc2d8 2026-07-01` |
| `NSPhase81ESSRoute.lean` | 3 | 2 | `5a6a4d9 2026-07-01` |
| `NSPhase82HeatDuhamel.lean` | 3 | 1 | `b35a153 2026-07-01` |
| `NSPhase83DuhamelBound.lean` | 3 | 1 | `c4b715b 2026-07-01` |
| `NSPhase84DuhamelFinal.lean` | 4 | 1 | `54a008f 2026-07-01` |
| `NSPhase85Minkowski.lean` | 3 | 0 | `acf7da8 2026-07-01` |
| `NSPhase86M6Close.lean` | 2 | 0 | `db84970 2026-07-01` |
| `NSPhase87AdjSymmetry.lean` | 4 | 1 | `ea1d835 2026-07-01` |
| `NSPhase88WeakInitCont.lean` | 8 | 2 | `82cac5b 2026-07-01` |
| `NSPhase89AdjointClose.lean` | 8 | 0 | `130a262 2026-07-01` |
| `NSPhase90ESSDecomposition.lean` | 3 | 2 | `8e532a2 2026-07-01` |
| `NSPhase91BlowupDecomp.lean` | 2 | 2 | `ab2bad9 2026-07-01` |
| `NSPhase92CarlemanDecomp.lean` | 3 | 2 | `4cac75d 2026-07-01` |
| `NSPhase93BlowupSubgaps.lean` | 3 | 2 | `265a1c8 2026-07-01` |
| `NSPhase94BackwardUniqSubgaps.lean` | 2 | 3 | `3e0e53c 2026-07-01` |
| `NSPhase95CarlemanSubgaps.lean` | 3 | 2 | `fd8e099 2026-07-01` |
| `NSPhase96H4BalancePath.lean` | 2 | 0 | `fcb97b3 2026-07-01` |
| `NSPhase97H4Closure.lean` | 15 | 4 | `0e76921 2026-07-03` |
| `NSPhase97aSobolevC2alphaClose.lean` | 2 | 0 | `f70c63c 2026-10-08` |
| `NSPhase97bH4EnergyClose.lean` | 6 | 0 | `535c02a 2026-07-23` |
| `NSPhase97c120CellLinftyClose.lean` | 5 | 0 | `becc11e 2026-07-23` |
| `NSPhase97dNoStationaryL3Close.lean` | 6 | 0 | `a1b03c7 2026-07-23` |
| `NSPhase98PathAClosure.lean` | 6 | 6 | `dc579e0 2026-07-01` |
| `NSPhase99InitCondClose.lean` | 4 | 2 | `3a32c84 2026-07-01` |
| `NSRoadmap.lean` | 4 | 3 | `3c1c938 2026-07-01` |
| `NSScalarLeibnizAdjoint.lean` | 4 | 3 | `4fd34f6 2026-06-30` |
| `NSSemigroupDef.lean` | 0 | 0 | `c208ef1 2026-06-29` |
| `NSStokesAdjoint.lean` | 3 | 0 | `29563aa 2026-06-28` |
| `NSStokesMaxReg.lean` | 3 | 1 | `971bcee 2026-06-29` |
| `NSStokesSmoothing.lean` | 3 | 1 | `94ca572 2026-06-29` |
| `NSWeakInitContClose.lean` | 4 | 1 | `2b974c8 2026-06-30` |
| `NSWeakInitContDirect.lean` | 2 | 0 | `b0e940e 2026-06-30` |
| `NSWeakInitContOrbit.lean` | 4 | 0 | `38f533f 2026-06-30` |
| `NSWeakMomentumDiffAtClose.lean` | 3 | 1 | `0c80eca 2026-06-30` |
| `NSWeakMomentumDiffAtProved.lean` | 3 | 0 | `6a49c25 2026-06-30` |
| `NSWeakSolutionClay.lean` | 1 | 0 | `f70c63c 2026-10-08` |
| `NSWeakSolutionScaffold.lean` | 0 | 2 | `f70c63c 2026-10-08` |
| `Regularity.lean` | 1 | 0 | `383adf7 2026-06-21` |
| `Stokes.lean` | 12 | 0 | `383adf7 2026-06-21` |
| `Wall266_Bogovskii.lean` | 8 | 2 | `9400ca7 2026-10-09` |
| `Wall266_H4L4.lean` | 61 | 0 | `f70c63c 2026-10-08` |
| `Wall266_L2Extension.lean` | 28 | 0 | `f70c63c 2026-10-08` |
| `Wall266_TrilinearForm.lean` | 7 | 0 | `f70c63c 2026-10-08` |
| `Wall300_Scaffold.lean` | 1 | 0 | `383adf7 2026-06-21` |
| `WeakSolution.lean` | 1 | 0 | `ff4ee7a 2026-07-01` |

## What is open

- `NS_M6_OPEN` — the Clay statement itself (global smooth solutions for arbitrary L² data). Open by definition; tracked at `NSPhase101EnergyLeL2.lean:128`.
- `BogovskiiCZ_OPEN` — H¹ bound for the Bogovskii operator (L² bound closed on branch `claude-bogovskii-kernel-closed`; gradient piece not proved).
- Energy inequality, Picard map well-definedness, Marcinkiewicz interpolation (Phase 63), three Phase-104 convolution obligations, the Carleman program (heat, drift, limit-pass), BKM criterion / global continuation.
- 171 unique declared `_OPEN` names repo-wide; ~27 in the live October-core files, the rest in July legacy scaffold. Every gap is a named `Prop` — never a silent hole.
- `H4_UniformBound.lean`, `NSWeakSolutionScaffold.lean` contain `Prop := True` placeholders (4 occurrences, disclosed here).

## Dependencies
- Lean `leanprover/lean4:v4.12.0`, Mathlib `v4.12.0` (pinned in `lean-toolchain` / `lakefile.lean`).
- `lean_lib Towers` roots include the four Wall266 modules plus Phase 97a–d, 101–108 and legacy phase files (see `lakefile.lean`).

## Workflow
```sh
lake build Towers.NS.Wall266_Bogovskii Towers.NS.Wall266_H4L4 Towers.NS.Wall266_TrilinearForm Towers.NS.Wall266_L2Extension  # CI core
lake build Towers   # everything
```

## Chronology

| Date | Commit | Event |
|---|---|---|
| 2026-10-07 | `94e0692` | Merge PR #2 — Wall266 trilinear-form infrastructure |
| 2026-10-07 | `c547251` | Merge PR #3 — H⁴ bound, explicit constant < 11 |
| 2026-10-07 | `da28c3e` | Merge PR #4 — Phase 97a H⁴→C^{2,α}, constant π/(4√2) |
| 2026-10-07 | `8885d9e` | Merge PR #5 — L² extension bound |
| 2026-10-07 | `53e0eaa` | Tag `v1.9-phase97a` |
| 2026-10-09 | `f70c63c` | Merge PR #6 — Path A complete, first axiom-free file |
| 2026-10-09 | `9400ca7` | Merge PR #8 — Bogovskii OPENs tracked |
| 2026-10-10/11 | branch `claude-bogovskii-kernel-closed` | Hardy–Littlewood weak (1,1), Bogovskii div + L² closed; PR #9 open |

## Links
- [Root README](../..) · [Towers README](../README.md)
- Repo: https://github.com/DavidFox998/navier-stokes
- Zenodo (existing record): https://doi.org/10.5281/zenodo.22049018 · concept: https://doi.org/10.5281/zenodo.22049016 (fresh mint for current state planned)
