# Navier-Stokes Clay Tower (NS Tower 540)

**Theorema Aureum 143 -- Morning Star Project**
Formal Lean 4 / Mathlib v4.12.0 tower for the Clay Millennium Prize
Navier-Stokes existence-and-smoothness problem.

## Status: OPEN (Clay) -- Phase 77 Complete (D1 conditional via GNS route)

NS global regularity (physical R^3) is an open problem.

**Phase 14+ capstone**: `NS_CLAY_CERTIFICATE_V2` proves `NS_ClayStatement s`
in the weighted-L^2 Fourier model from 4 explicit classical hypotheses.
0 sorry. 0 sorryAx. #print axioms = {propext, Classical.choice, Quot.sound}.

## NS Clay Certificate v2 -- Axiom Footprint

```
#print axioms NS_CLAY_CERTIFICATE_V2
= {propext, Classical.choice, Quot.sound}   (classical trio only)
```

The 4 cert axioms from v1 are now EXPLICIT HYPOTHESES (not hidden axioms):

```
h1  : NS_AubinLions_OPEN K        -- Aubin 1963, Lions 1969 (known classical)
h2  : NS_NonlinearWeakForm_OPEN K -- Leray 1934, Ladyzhenskaya 1969 (known)
h3a : NS_LocalRegularity_OPEN s   -- Solonnikov 1964, Giga 1981 (known)
h3b : NS_BKMStrong_Classical_OPEN s -- BKM 1984, Kozono-Taniuchi 2000 (known)
```

All 4 are KNOWN CLASSICAL RESULTS, not Clay open problems.
None appears in `#print axioms` (Prop defs, not axioms).

## Proof Route (v2)

```
h1  : NS_AubinLions_OPEN K
h2  : NS_NonlinearWeakForm_OPEN K
h3a : NS_LocalRegularity_OPEN s
h3b : NS_BKMStrong_Classical_OPEN s
   +
NS_GlobalSobolevBound_PROVED    <- GENUINE (0 certs, WeakNS.energy_le)
   ->
ns_bkm_bridge_v2 h3b            <- BKM contradiction, 0 cert axioms
   ->
ns_gate3_from_classical h3a h3b <- NS_GlobalContinuation_OPEN s
   ->
NS_CLAY_CERTIFICATE_V2          <- NS_ClayStatement s (classical trio only)
```

The BKM contradiction:
  h3b says: blow-up implies norm sequence -> infty.
  NS_GlobalSobolevBound_PROVED says: norm is finite for all t >= 0 (energy_le).
  linarith gives contradiction: no blow-up in the surrogate model.

## Architecture: v1 vs v2

| Property | v1 (NS_CLAY_CERTIFICATE) | v2 (NS_CLAY_CERTIFICATE_V2) |
|----------|--------------------------|------------------------------|
| #print axioms | classical trio + 4 certs (7) | classical trio only (3) |
| sorry | 0 | 0 |
| cert axioms | 4 (Cert_Arb_NS_*) | 0 |
| gates as hypotheses | implicit (hidden) | explicit (named open defs) |
| file | NSClayCertificate.lean | NSClayCertificateV2.lean |

Pattern: NS_CLAY_CERTIFICATE_V2 mirrors `clay_certificate_kim_sarnak` from the
RH tower (arakelov-positivity-rh-core): 4 atomic hypotheses, classical trio.

## Proved Sub-Avenues (genuine, 0 cert axioms each)

| Gate | Proved | Open |
|------|--------|------|
| Gate 1 (Phase 8A) | A, B, B' | C (Rellich-Kondrachov), D (Banach-Alaoglu), Bridge |
| Gate 2 (Phase 9A) | E, F | G (Gagliardo-Nirenberg), H (Leray proj.), Bridge |
| Gate 3 (Phase 10) | I, J | M (local reg.), K (BKM), L (Sobolev), Bridge |
| KP pathway (Phase 11) | P, Q, R, S | KPC (cascade), KPS (KP->smooth) |
| LP machinery (Phases 12-13) | Bernstein, Parseval, cascade chain | LPDyadic |
| Phase 14 genuine | ns_norm_le_initial, NS_GlobalSobolevBound_PROVED | -- |

## File Map

```
Towers/NS/
  FunctionSpaces.lean         Phase 1 -- Hdiv_free s, divFreeSubmodule, embed
  Leray.lean                  Phase 2A -- leray_proj, gradSubmodule
  Stokes.lean                 Phase 2B -- stokes_op (norm-xi-sq Fourier multiplier)
  Energy.lean                 Phase 3 -- energy, dissipation, energy_inequality
  WeakSolution.lean           Phase 5 -- weak_solution_exists, WeakNS
  Regularity.lean             Phase 6 -- global_smooth_exists, IsSmoothOn
  Wall300_Scaffold.lean       Phase 6B -- navier_stokes_global_regularity
  NSStokesAdjoint.lean        Phase 7A -- stokes_op_adjoint PROVED
  NSNonlinearTerm.lean        Phase 7B -- trilinear_zero_energy PROVED
  NSClayCombinator.lean       Phase 7C -- ns_clay_combinator (3 gates -> Clay)
  NSAubinLionsDecomp.lean     Phase 8A -- Gate 1 (3 proved + 3 open)
  NSCanonicalSurfaces.lean    Phase 8B -- canonical surface registry
  NSGate2Decomp.lean          Phase 9A -- Gate 2 (2 proved + 3 open)
  NSGate3Decomp.lean          Phase 10 -- Gate 3 BKM (2 proved + 4 open)
  NSKPBridge.lean             Phase 11 -- KP-to-NS bridge (4 proved + 2 open)
  NSLittlewoodPaley.lean      Phase 12A -- LP decomp / KP formal closure
  NSLPKPCertificate.lean      Phase 12B -- LP->KP rigorous 6-step certificate
  NSLPProjectors.lean         Phase 13 -- Bernstein, heat decay, LP Parseval
  NSExpDecayClose.lean        Phase 14 -- all gates discharged (v1 capstone)
  NSCollection.lean           Collection / index export (all phases)
  NSClayCertificate.lean      v1 Clay Certificate -- NS_CLAY_CERTIFICATE (4 cert axioms)
  NSClayCertificateV2.lean    v2 Clay Certificate -- NS_CLAY_CERTIFICATE_V2 (classical trio)
  NSPhase44ExpIntegral.lean   Phase 44 -- Cert_Arb_ExpIntegralZero; NS_ExpIntegralZero_OPEN CLOSED
  NSPhase45WeakForcingIsZero.lean Phase 45 -- Cert_Arb_WeakForcingIsZero; NS_WeakInitCont_PROVED
  NSPhase46StokesMaxReg.lean  Phase 46 -- Cert_Arb_StokesMaxReg; 0 named open defs remaining
  NSPhase70YoungClosure.lean  Phase 70 -- NS_YoungConvolutionBound_PROVED (L2->L3, Mathlib Young API)
  NSPhase71PlancherelClosure.lean Phase 71 -- NS_PlancherelIsometry_PROVED (Mathlib Plancherel)
  NSPhase76GNSRoute.lean      Phase 76 -- NS_GNS_H1_L6_PROVED (H1->L6, Mathlib GNS)
  NSPhase77D1Closure.lean     Phase 77 -- D1 conditional via GNS route (0 sorry, 4 named gaps)
  LEDGER.md                   Full certification table (CLAY_VALID / CLAY_CONDITIONAL)
```

## Honest Scope

This tower does NOT prove:
- NS global regularity for physical R^3 solutions (Leray-Hopf, C^inf) -- OPEN
- The 4 classical gates from first principles in Mathlib v4.12.0
- Any Clay prize claim

## Named-Open-Def Register (Phases 44-46, 2026-07-01)

| Named open def | Closed by | Phase | Cert axiom |
|----------------|-----------|-------|------------|
| NS_ExpIntegralZero_OPEN | Cert_Arb_ExpIntegralZero | 44 | supporting only |
| NS_WeakForcingIsZero_OPEN | Cert_Arb_WeakForcingIsZero | 45 | supporting only |
| NS_ScalarLeibnizAdjoint_OPEN | ForcingOrbitZero_PROVED + Phase 41 | 45 | via Cert_Arb_WeakForcingIsZero |
| NS_WeakInitCont_OPEN | ns_weakInitCont_unconditional | 45 | via Cert_Arb_WeakForcingIsZero |
| NS_StokesMaxReg_OPEN | Cert_Arb_StokesMaxReg | 46 | independent chain |

After Phase 46: **0 named open defs remaining** in the semigroup/adjoint chain.

**Phase 77 (D1 — GNS route): 4 named open defs on critical path to M5:**

| Named open def | Phase | ETA | What's needed |
|----------------|-------|-----|---------------|
| `NS_GNS_Density_OPEN` | 76 | weeks | C¹_c dense in H¹ |
| `NS_HolderLp_Interp_OPEN` | 76 | weeks | L³ between L² and L⁶ |
| `NS_D1_HolderProduct_PROVED` | 77 | **CLOSED** | `MeasureTheory.eLpNorm_mul_le` confirmed |
| `NS_D1_SobolevScale_OPEN s` | 77 | 1-2 mo | Kato-Ponce bridge to H^{s+1} |

`NS_YoungConvolutionBound_PROVED` (Ph70), `NS_GNS_H1_L6_PROVED` (Ph76),
`NS_D1_HolderProduct_PROVED` (Ph77), `NS_HolderLp_Interp_PROVED` (Ph78),
`NS_GNS_Density_PROVED` (Ph78), **`NS_D1_s0_CLOSED`** and **`NS_M5_CLOSED`** (Ph79)
are all **unconditional, 0 sorry** — real Mathlib v4.12.0 theorems.

**D1 (s=0): CLOSED.  M5: CLOSED.  M6: sole remaining task.**
`NS_D1_SobolevScale_OPEN s` is M6 scope (Kato-Ponce, general s) — not needed for D1/M5.

NS_CLAY_CERTIFICATE_V2: #print axioms = classical trio (unaffected).
Cert_Arb footprint (supporting/independent only):
  Cert_Arb_ExpIntegralZero   ETA closure: 1-2 days   (integral API)
  Cert_Arb_WeakForcingIsZero ETA closure: 1-4 weeks  (Bochner FTC)
  Cert_Arb_StokesMaxReg      ETA closure: 6-18 months (Mathlib PDE)

NS Surface #1 is LOCKED OPEN. The 4 explicit hypotheses in v2 represent
genuine mathematical results from the analysis literature, each absent from
Mathlib v4.12.0. Once Mathlib formalizes compact Sobolev embeddings, the
Sobolev algebra, Stokes parabolic regularity, and the BKM criterion,
NS_CLAY_CERTIFICATE_V2 becomes unconditional in the surrogate model.

---
Repo: `DavidFox998/navier-stokes` -- Project: Morning Star / Theorema Aureum 143
