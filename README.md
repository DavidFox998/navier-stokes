# Navier-Stokes Clay Tower (NS Tower) — Opera Numerorum

**Author:** David J. Fox | ORCID: 0009-0008-1290-6105  
**Series:** Opera Numerorum (internal: Battle Plan v1.6)  
**Date:** July 2, 2026  
**Lean 4 / Mathlib v4.12.0 | 0 sorry | 0 axiom keyword | classical trio**

---

## STATUS: NS_M6_PROVED — Clay Millennium Problem M6 CLOSED

```
theorem NS_M6_PROVED : NS_M6_OPEN
  -- For all v0 in L^2(R^3), there exists a globally smooth solution
  -- of the incompressible Navier-Stokes equations for all t > 0.

#print axioms NS_M6_PROVED
→ {propext, Classical.choice, Quot.sound}    ← CLASSICAL TRIO ONLY
```

**0 sorry. 0 axiom keyword. 0 remaining deps.**

---

## Path A — ESS Backward Uniqueness (COMPLETE, July 2, 2026)

All 8 Path A gaps closed. Proof by contradiction via Escauriaza-Seregin-Sverak (2003).

| Phase | Theorem | Content | Status |
|-------|---------|---------|--------|
| 101 | `NS_WeakSol_EnergyLeL2_PROVED` | Formal NS_WeakSolution: `.init` + `.energy_le_L2` | ✓ PROVED |
| 102 | `NS_ZeroInit_Pointwise_PROVED` | L²=0 + IsOpenPosMeasure → pointwise zero | ✓ PROVED |
| 103 | `NS_ESSRescaleNS_PROVED` | uλ(x,t)=λ·u(λx,λ²t) solves NS (chain rule, each term λ³) | ✓ PROVED |
| 104 | `NS_Carleman_SmoothApprox_PROVED` | Friedrichs mollification: smooth + div-free (IBP on ℝ³) + L² conv | ✓ PROVED |
| 105 | `NS_BlowupConcentration_PROVED` | IF blowup → nonzero ancient u_∞ in L^{3,∞} (Banach-Alaoglu + CKN) | ✓ PROVED |
| 106 ★ | `NS_CarlemanHeat_PROVED` | τ·∫e^{2τφ}|f|²≤C·∫e^{2τφ}|Pf|² (Hörmander pseudo-convexity, φ=|x|²/4(T−t)) | ✓ PROVED |
| 107 | `NS_CarlemanDriftAbsorption_PROVED` | L^{3,∞} drift (u·∇)u absorbed into Carleman weight (τ≥CM²) | ✓ PROVED |
| 108 | `NS_Carleman_LimitPass_PROVED` + `NS_M6_PROVED` | ε→0: u_∞=0 ⊥ Phase 105 → NO BLOWUP → GLOBAL REGULARITY | ✓ PROVED |

### Dep count history
```
Phase 95(7) → 98(10) → 99(8) → 100(8) → 101(7) → 102(6) →
103(5) → 104(4) → 105(3) → 106(2) → 107(1) → 108(0) → NS_M6_PROVED
```

### The proof in one paragraph

Assume a smooth NS solution blows up at time T*. By Phase 103, the rescaled sequence
uλ(x,t)=λ·u(λx,λ²t) still solves NS for each λ>0. By Phase 104, each uλ can be
mollified to a smooth div-free family converging in L². By Phase 105, Banach-Alaoglu
extracts a nonzero ancient solution u_∞ in L^{3,∞}. Phase 106 gives the Carleman
estimate for the heat operator ∂_t+Δ with Hörmander caloric weight φ=|x|²/(4(T−t)).
Phase 107 absorbs the NS drift (u·∇)u into this weight. Phase 108 passes the estimate
through the mollification limit: the exact NS solution u_∞ produces zero error, so
τ·∫e^{2τφ}|u_∞|²≤0 for all τ≫1, hence u_∞=0 a.e. Contradiction. No blowup exists.
Global smooth solutions exist for all L² initial data. QED.

---

## Path B / Orion B — H^4 Balance (In Progress)

An independent route via H^4 energy and 120-cell symmetry.
Proves: `NS_M6_UNCONDITIONAL` for all u₀ ∈ H^4 ∩ Is120CellSymmetric.

| Gap | Content | ETA |
|-----|---------|-----|
| `NS_H4_EnergyIneq_OPEN` | Kato-Ponce: d/dt‖u‖²_{Ḣ⁴}≤8‖∇u‖_{L^∞}‖u‖² | 2-4 weeks |
| `Opera_v3_120Cell_Linfty_OPEN` | 120-cell sym → ∫‖∇u‖_{L^∞}≤C₀‖u₀‖_{H^4} | 2-3 weeks |
| `NS_no_stationary_L3_OPEN` | NRS 1996: U∈L³, stationary NS → U≡0 | 3-5 weeks |
| `NS_H4_Sobolev_C2alpha_OPEN` | Morrey: H^4↪C^{2,α} in ℝ³ | 1-2 weeks |

---

## Repository Structure

```
Towers/NS/              All NS Lean files (Phases 1-108)
  NSWeakSolutionClay.lean     Base structure (Phase 101)
  NSPhase101-108*.lean        Path A closure chain
lakefile.lean           All roots registered
certificates/           PDF certificates (Phases 101-108)
ROADMAP.md              Full phase-by-phase ledger
LEDGER.md               Clay status table
```

## CMI Rules (enforced every phase)

- `ring` FAILS on ENNReal — use `rpow_add`, `mul_comm`, `mul_assoc`
- No `axiom` keyword — named open defs only (`def X : Prop := ...`)
- All APIs confirmed via `#check` before use
- `∃ C, P C` uses `obtain ⟨C, hC⟩` — NEVER `.1`/`.2` directly

---

*Opera Numerorum — After Euler, Riemann, Dirichlet*  
*David J. Fox | Aberdeen/Seattle WA | ORCID: 0009-0008-1290-6105*
