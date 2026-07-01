# NS Tower Roadmap to Clay D3 Prize

**Opera Numerorum -- David Fox.  July 2026.**

Machine-readable formal roadmap: `Towers/NS/NSRoadmap.lean`

---

## Current State

| File | Status | Content |
|------|--------|---------|
| NSPhase47BKMSurrogateClose | DONE | NS_CLAY_CERTIFICATE_V3 (3 explicit hyps, Cert_Arb_SurrogateSmooth) |
| NSPhase48DuhamelBridge | DONE | D1-D5 named open surfaces; D3 = Clay gap |
| NSPhase49GapReductionAdapt | DONE | gap_reduction ported; D2 proved given D1; h3a decomposed |
| NSPhase50SuperBric | DONE | 7-cycle gate; conditional D3 finite time / small data |
| NSRoadmap | DONE | Formal dependency DAG; M5 reduction; M6 Clay target |

---

## Milestone Table

| Milestone | Description | Status | ETA |
|-----------|-------------|--------|-----|
| M1 | D2 proved given D1 | **PROVED** Phase 49 | done |
| M2 | h3a from Coercivity + Smoothing | **PROVED** Phase 49 | done |
| M3 | Clay_V3 given h1+h2+M2 | **PROVED** Phase 47+49 | done |
| M4 | D3 small data, t <= 7 (SuperBric gate) | **PROVED** Phase 50 | done |
| M5 | D3 small data, all t >= 0 (Fujita-Kato) | OPEN | 3-6 months |
| M6 | D3 all smooth data, all t >= 0 | CLAY PRIZE | open |

---

## Nine Named Open Surfaces

| Gap | Content | ETA | Blocks |
|-----|---------|-----|--------|
| GAP 1 | Cert_Arb_SurrogateSmooth (DCT differentiability) | 2-4 weeks | M3, M4 |
| GAP 2 | NS_BilinearEstimate (D1: Gagliardo-Nirenberg) | 3-6 months | **M5 CRITICAL** |
| GAP 3 | NS_StokesCoercivity (Poincare on Hdiv_free) | 3-6 months | M2, M3 |
| GAP 4 | NS_AubinLions (Rellich compact embedding) | 3-6 months | M3 |
| GAP 5 | NS_NonlinearWeakForm (trilinear b(u,v,phi)) | 3-6 months | M3 |
| GAP 6 | NS_SemigroupSmoothing (Kato/Pazy C0-semigroup) | 12-18 months | M2 |
| GAP 7 | NS_BKMCriterion (Beale-Kato-Majda 1984) | 12-18 months | BKM path |
| GAP 8 | NS_FujitaKatoGlobal (all smooth data) | CLAY PRIZE prereq | M6 |
| GAP 9 | NS_Clay_D3_Prize (global regularity target) | CLAY PRIZE | - |

---

## Critical Path to M5 (Fujita-Kato, ETA 3-6 months)

```
GAP 2 (D1: Gagliardo-Nirenberg)
  |
  v
D2 PROVED (ns_d2_from_d1, Phase 49)
  |
  v (+ Banach FPT in Mathlib + corrSem contraction proved)
  v
M5: D3 for small initial data, all t >= 0
```

The Banach fixed-point theorem is in Mathlib v4.12.0 (`ContractingWith.fixedPoint`).
corrSem contraction is proved (`corrSemigroupRate_nonneg`, Phase 43).
D2 is proved given D1 (Phase 49).

**GAP 2 (D1) is the single remaining ingredient for M5.**

---

## Gap from M5 to M6 (Clay Prize)

M5 proves: if ||u0||_{H^{s+2}} <= nu / (2*C_D1), then the NS solution is globally smooth.

M6 requires: for ANY smooth u0 (no smallness condition), the NS solution is globally smooth.

The gap between M5 and M6 has been open since Leray 1934. No known approach closes it for 3D.

---

## Axiom Footprint (July 2026)

```
NS_CLAY_CERTIFICATE_V3 (Phase 47):
  {propext, Classical.choice, Quot.sound, Cert_Arb_SurrogateSmooth}
  + explicit hyps: h1, h2, h3a

ns_phase49_master_conditional (Phase 49):
  {propext, Classical.choice, Quot.sound}
  + explicit hyps: GAP1, GAP2, GAP3, GAP4, GAP5, GAP6

ns_d3_superbric (Phase 50):
  {propext, Classical.choice, Quot.sound}
  + explicit hyps: 7 stamp conditions

ns_milestone_6_clay (NSRoadmap):
  {propext, Classical.choice, Quot.sound}
  + NS_FujitaKatoGlobal_OPEN (Clay prize hypothesis)
```

D3 OPEN. No Clay claim.

---

*Author: David J. Fox, ORCID 0009-0008-1290-6105, Aberdeen/Seattle WA.*
*Opera Numerorum -- Battle Plan v1.6 (internal).*
