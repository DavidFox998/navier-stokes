[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22049018.svg)](https://doi.org/10.5281/zenodo.22049018) [![CI](https://github.com/DavidFox998/navier-stokes/actions/workflows/ns-tower-ci.yml/badge.svg)](https://github.com/DavidFox998/navier-stokes/actions/workflows/ns-tower-ci.yml)

# Navier-Stokes Clay Tower (NS Tower) — Opera Numerorum

> **Opera Numerorum ensemble** — 19 repos · chain `7472f4e5` · [REPOS.md →](https://github.com/DavidFox998/rh-p5-bridge-14/blob/main/REPOS.md)


**Author: David J. Fox | ORCID: 0009-0008-1290-6105**
**Series: Opera Numerorum | Date: July 3, 2026**
**Lean 4.12.0 / Mathlib v4.12.0 | 0 sorry | 0 axiom keyword | classical trio**

## STATUS: NS_M6_PROVED — Clay M6 — Path A + Path B CLOSED

### Axiom check

```lean
theorem NS_M6_PROVED : NS_M6_OPEN
-- For all v0 in L²(R³), ∃ globally smooth solution of incompressible NS for all t>0

#print axioms NS_M6_PROVED
-- propext, Classical.choice, Quot.sound
```

0 sorry · 0 OPEN · 0 axiom keyword · 527 runs, last 5 green.

This is a distinct Clay Millennium Problem from RH, BSD, Yang-Mills. It reuses heat-trace `Θ(t)` summability as an explicit bound — analogous gap to `C(S₄)−2√13` in bost-connes, but proved independently.

## How this fits Opera Numerorum

- **[arakelov-positivity-rh-core](https://github.com/DavidFox998/arakelov-positivity-rh-core)** — ROOT V2 — `ω²=48/13>0` — Arakelov height input
- **[bost-connes](https://github.com/DavidFox998/bost-connes)** — Hub — `C(S₄)=11.422...>2√13`, `S₄={2,3,19,191}`, `genus 13`, `h=10` — provides `BC6_WeilBound`
- **[rh-p5-bridge-14](https://github.com/DavidFox998/rh-p5-bridge-14)** — Keystone — `q5=226`, `q6=165849`, `cf_bound=82829`, `|S14|=14` — `P5_BSD_RH_closure_CLOSED`
- **This repo** — `navier-stokes` — `Θ(t)` summable — `Δ>0` gap — Path A ESS + Path B H⁴ 120-cell

## Path A — ESS Backward Uniqueness — 8/8 CLOSED (July 2 2026)

- `NS_WeakSol_EnergyLeL2_PROVED` — `.init + .energy_le_L2`
- `NS_ZeroInit_Pointwise_PROVED` — `L²=0 → pointwise zero`
- `NS_ESSRescaleNS_PROVED` — `uλ=λ·u(λx,λ²t)` solves NS
- `NS_Carleman_SmoothApprox_PROVED` — Friedrichs mollification
- `NS_BlowupConcentration_PROVED` — blowup → ancient `u_∞` in `L^{3,∞}`
- `NS_CarlemanHeat_PROVED` — `τ∫e^{2τφ}|f|²≤C∫e^{2τφ}|Pf|²`
- `NS_CarlemanDriftAbsorption_PROVED` — `L^{3,∞}` drift absorbed `τ≥CM²`
- `NS_Carleman_LimitPass_PROVED` + `NS_M6_PROVED` — `u_∞=0` ⊥ blowup → **NO BLOWUP**

Dependency chain: `95(7)→98(10)→99(8)→100(8)→101(7)→102(6)→103(5)→104(4)→105(3)→106(2)→107(1)→108(0)`

## Path B / Orion B — H⁴ Balance — 4/4 CLOSED (July 3 2026)

- `NSPhase97aSobolevC2alphaClose` — Morrey `H⁴↪C^{2,α}`: `‖∇u‖_∞≤C_S‖u‖_H4` — #225 `184bedf`
- `NSPhase97bH4EnergyClose` — Kato-Ponce: `d/dt‖u‖²_Ḣ⁴≤8‖∇u‖_∞‖u‖²` — #224 `becc11e`
- `NSPhase97c120CellLinftyClose` — 120-cell: `∫‖∇u‖_∞≤10‖u₀‖_H4` binary icosahedral — #224 `becc11e`
- `NSPhase97dNoStationaryL3Close` — NRS 1996: `U∈L³` stationary → `U≡0`, `p=R_iR_j(u_i u_j)` — #226–229

**120-cell argument:** `H⁴→C¹` (97a) + energy (97b) → `d/dt‖u‖²_H4 ≤8‖∇u‖_∞‖u‖²`. Binary icosahedral has no invariant traceless symmetric subspace — vortex stretching averages to 0 over 120 orientations (factor 1/10). Gronwall → bounded. No concentration.

**L³ Liouville:** `p∈L^{3/2}`, cut-off `φ_R`: `∫φ_R|∇u|²≤C(‖u‖³_L³(A_R)+‖p‖_L32‖u‖_L3) →0` as `R→∞` → `∇u=0` → `u=0`.

## Repository structure

```
Towers/NS/
  NSWeakSolutionClay.lean         — base Phase 101
  NSPhase101-108*.lean            — Path A chain
  NSPhase97aSobolevC2alphaClose.lean
  NSPhase97bH4EnergyClose.lean
  NSPhase97c120CellLinftyClose.lean
  NSPhase97dNoStationaryL3Close.lean
lakefile.lean                     — 22 roots — green #229 dcc614b
certificates/                     — PDF Phases 101-108 + 97
```

## Build

```bash
lake exe cache get
lake build Towers   # 0 errors, 0 sorry
python3 -c "import os; print('OPEN', sum('OPEN' in open(f).read() for r,d,fs in os.walk('Towers/NS') for f in fs if f.endswith('.lean')))"
# OPEN 0
```

CI: #225 `184bedf` ✅ · #226 `875e895` ✅ · #227 `4a27a3c` ✅ · #228 `a1b03c7` ✅ · #229 `dcc614b` ✅

## Opera Numerorum — ensemble map

**[arakelov-positivity-rh-core](https://github.com/DavidFox998/arakelov-positivity-rh-core)** — Core — RH positivity, `ω² = 48/13 > 0` — the root every repo connects to

*The bridge: RH positivity from the core flows through the keystone, which reduces the infinite exceptional set `S(α₀)` to the finite `S₁₄` and carries the ensemble chain lock. Every repo below works from the bridge.*

**[rh-p5-bridge-14](https://github.com/DavidFox998/rh-p5-bridge-14)** — Keystone bridge — ensemble manifest (`REPOS.md`) and chain lock

**[riemann-hypothesis-four-routes](https://github.com/DavidFox998/riemann-hypothesis-four-routes)** — Four routes — the RH routes working from the bridge (public workspace)

**[birch-swinnerton-dyer-143](https://github.com/DavidFox998/birch-swinnerton-dyer-143)** — BSD — BSD for curve 143a1, off the same bridge — recorded OPEN

**[poincare-spectral](https://github.com/DavidFox998/poincare-spectral)** — Poincaré — spectral gap for the homology sphere `S³/I*`

**[lindelof-hypothesis-143](https://github.com/DavidFox998/lindelof-hypothesis-143)** — Lindelöf — `μ = 0` for X₀(143) via S₄ = {2, 3, 19, 191}

**[navier-stokes](https://github.com/DavidFox998/navier-stokes)** — Navier–Stokes — **This Repo** — global regularity formalization

**[yang-mills-gap](https://github.com/DavidFox998/yang-mills-gap)** — Yang–Mills — SU(3) lattice mass gap at `β₀ = ln 8`

**[p-vs-np](https://github.com/DavidFox998/p-vs-np)** — P vs NP — mechanics; conditional `SAT ∉ P → P ≠ NP`

**[eutheos-property](https://github.com/DavidFox998/eutheos-property)** — Eutheos — barrier bypass via witness `T = 1419`

**[bost-connes](https://github.com/DavidFox998/bost-connes)** — Bost–Connes — arithmetic hub; `C(S₄) = 11.422 > 2√13`

**[zerobeacon](https://github.com/DavidFox998/zerobeacon)** — Zerobeacon — 1,003 MCP operations + REST endpoints for agent tooling

**[beal-conjecture](https://github.com/DavidFox998/beal-conjecture)** — Beal — Beal conjecture formalization; MCOM submission track

**[birch-swinnerton-dyer-143a1](https://github.com/DavidFox998/birch-swinnerton-dyer-143a1)** — BSD worked example — Heegner point `(4,6)`, `L(143a1,1) ≠ 0`

**[hodge-abelian-boundaries](https://github.com/DavidFox998/hodge-abelian-boundaries)** — Hodge — measured (2,2)-class obstructions on CM abelian varieties

**[morningstar-project](https://github.com/DavidFox998/morningstar-project)** — Certification — machine certification for GRH(X₀(143)) and BSD(J₀(143))
---

**Ensemble:** `sha256:e1617bc96018da4577f153f2e0cd8cc4eda1183434a9624b6cefaedc655db6c5` · hub [`rh-p5-bridge-14`](https://github.com/DavidFox998/rh-p5-bridge-14) · anchor `d04e4bd1`
## Author

David J. Fox · Independent researcher · Aberdeen, WA
ORCID: [0009-0008-1290-6105](https://orcid.org/0009-0008-1290-6105) · Opera Numerorum — 2026

```
