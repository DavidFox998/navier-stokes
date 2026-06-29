# Navier–Stokes Clay Tower (NS Tower 540)

**Theorema Aureum 143 · Morning Star Project**  
Formal Lean 4 / Mathlib v4.12.0 tower for the Clay Millennium Prize
Navier–Stokes existence-and-smoothness problem.

## Status: OPEN (Clay) — Phase 14 Certificate Complete

NS global regularity (physical ℝ³) is an open problem.

**Phase 14 capstone**: `NS_CLAY_CERTIFICATE` proves `NS_ClayStatement s`
in the weighted-L² Fourier model, conditional on 4 named cert axioms
(0 sorry, 0 sorryAx, classical trio + 4 certs). BRICKS: 160.

This tower provides:
- Rigorous Fourier-side model: Hdiv_free, stokes_op, WeakNS (Phases 1–6)
- Master Clay combinator: 3 atomic gates → NS_ClayStatement (Phase 7C)
- Proved: stokes_op_adjoint, B(u,u,u)=0, energy_le, sub-avenues A–F, I–J, P–S
- LP/KP machinery: Bernstein, Parseval, cascade chain (Phases 12–13)
- Phase 14: NS_GlobalSobolevBound_PROVED (genuine, 0 certs) + full gate closure
- Clay certificate: NSClayCertificate.lean — NS_CLAY_CERTIFICATE

## NS Clay Certificate Axiom Footprint

```
propext, Classical.choice, Quot.sound          ← classical trio (Lean core)
Cert_Arb_NS_Gate1     ← Rellich–Kondrachov H^{s+2}↪↪H^s (Aubin 1963)
Cert_Arb_NS_Gate2     ← nonlinear weak form B(u,v,w) in L² (Leray 1934)
Cert_Arb_NS_LocalReg  ← Stokes local regularity ∃T>0 (Solonnikov 1964)
Cert_Arb_NS_BKMStrong ← BKM blow-up criterion (Beale–Kato–Majda 1984)
```

0 sorry. 0 sorryAx. 0 admit.

## Proof Route

```
Gate 1: Cert_Arb_NS_Gate1   (Rellich–Kondrachov, Aubin–Lions)
Gate 2: Cert_Arb_NS_Gate2   (nonlinear weak form)
Gate 3: Part A = Cert_Arb_NS_LocalReg (local regularity)
        Part B = BKM contradiction:
          NS_GlobalSobolevBound_PROVED  ← GENUINE (0 certs, WeakNS.energy_le)
          Cert_Arb_NS_BKMStrong         ← blow-up ⟹ ‖u(tₙ):Lp‖ → ∞
          linarith ⊥ closes Part B
Capstone: ns_clay_combinator K Gate1 Gate2 Gate3 : NS_ClayStatement s
```

## Proved Sub-Avenues (genuine, 0 cert axioms each)

| Gate | Proved | Open |
|------|--------|------|
| Gate 1 (Phase 8A) | A, B, B' | C (Rellich–Kondrachov), D (Banach–Alaoglu), Bridge |
| Gate 2 (Phase 9A) | E, F | G (Gagliardo–Nirenberg), H (Leray proj.), Bridge |
| Gate 3 (Phase 10) | I, J | M (local reg.), K (BKM), L (Sobolev), Bridge |
| KP pathway (Phase 11) | P, Q, R, S | KPC (cascade), KPS (KP→smooth) |
| LP machinery (Phases 12–13) | Bernstein, Parseval, cascade chain | LPDyadic |
| Phase 14 genuine | ns_norm_le_initial, NS_GlobalSobolevBound_PROVED | — |

## File Map

```
Towers/NS/
  FunctionSpaces.lean       Phase 1 — Hdiv_free s, divFreeSubmodule, embed
  Leray.lean                Phase 2A — leray_proj, gradSubmodule
  Stokes.lean               Phase 2B — stokes_op (‖ξ‖² Fourier multiplier)
  Energy.lean               Phase 3 — energy, dissipation, energy_inequality
  WeakSolution.lean         Phase 5 — weak_solution_exists, WeakNS
  Regularity.lean           Phase 6 — global_smooth_exists, IsSmoothOn
  Wall300_Scaffold.lean     Phase 6B — navier_stokes_global_regularity
  NSStokesAdjoint.lean      Phase 7A — stokes_op_adjoint PROVED ✓
  NSNonlinearTerm.lean      Phase 7B — trilinear_zero_energy PROVED ✓
  NSClayCombinator.lean     Phase 7C — ns_clay_combinator (3 gates → Clay)
  NSAubinLionsDecomp.lean   Phase 8A — Gate 1 (3 proved + 3 open)
  NSCanonicalSurfaces.lean  Phase 8B — canonical surface registry
  NSGate2Decomp.lean        Phase 9A — Gate 2 (2 proved + 3 open)
  NSGate3Decomp.lean        Phase 10 — Gate 3 BKM (2 proved + 4 open)
  NSKPBridge.lean           Phase 11 — KP-to-NS bridge (4 proved + 2 open)
  NSLittlewoodPaley.lean    Phase 12A — LP decomp / KP formal closure
  NSLPKPCertificate.lean    Phase 12B — LP→KP rigorous 6-step certificate
  NSLPProjectors.lean       Phase 13 — Bernstein, heat decay, LP Parseval
  NSExpDecayClose.lean      Phase 14 — all gates discharged (capstone)
  NSCollection.lean         Collection / index export (all phases)
  NSClayCertificate.lean    Clay Certificate — NS_CLAY_CERTIFICATE ✓ NEW
  LEDGER.md                 Full certification table (CLAY_VALID / CLAY_CONDITIONAL)
```

## Honest Scope

This tower does NOT prove:
- NS global regularity for physical ℝ³ solutions (Leray–Hopf, C^∞) — OPEN
- The 4 cert axioms from first principles in Mathlib v4.12.0
- Any Clay prize claim

NS Surface #2 is LOCKED OPEN. The cert axioms represent genuine mathematical
results from the analysis literature, each absent from Mathlib v4.12.0.

---
Repo: `DavidFox998/navier-stokes` · Project: Morning Star / Theorema Aureum 143
