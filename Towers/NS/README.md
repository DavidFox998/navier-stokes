# Towers/NS — Navier-Stokes Tower — 80 bricks, Path A + Path B

**Status:** Path A 8/8 CLOSED (July 2), Path B 4/4 CLOSED (July 3) — CI #229 green.

Imagine proving water never blows up. We have 80 small bricks, each proves one tiny fact. Stack them into a tower — top brick = Clay theorem.

Dependency Order

### Layer 0 — Foundation (last month)
- `Compactness.lean` — Rellich-Kondrachov compactness
- `Divergence.lean` — div-free calculus
- `Energy.lean`, `EnergyIneq.lean`, `EnergyV2.lean` — L² energy inequality
- `FunctionSpaces.lean` — H⁴, L³, L^{3,∞}, Besov definitions
- `Leray.lean` — Leray projector P
- `GalerkinApprox.lean` — Galerkin approximation existence

### Layer 1 — H4 Toolbox (3 weeks ago, NS-Tower-540)
- `H4_Averaging.lean` — Averaging operator over 120-cell
- `H4_Energy.lean` — H⁴ energy evolution
- `H4_Forcing.lean` — Forcing term estimates
- `H4_UniformBound.lean` — Uniform H⁴ bound under symmetry

### Layer 2 — Adjoint + Semigroup (Phase 20-39)
- `NSAdjointArgument.lean` — Close B.3 (f=0) via adjoint
- `NSAdjointIntegralClose.lean` — Phase 35+36 integral closure
- `NSAdjointPackageClose.lean` — Phase 29 Parts A+C
- `NSAdjointPackagePartBClose.lean` — Phase 30 Part B
- `NSAdjointSymmetry.lean` — Phase 38b InnerDerivMap OPEN + Adjoint
- `NSAubinLionsDecomp.lean` — Phase8A Aubin-Lions avenue (3 proves)
- `NSBochnerDiff.lean` — Phase 23 Gap B into 3 names
- `NSCanonicalSurfaces.lean` — Phase8B Canonical surfaces registry
- `NSCorrSemigroupContinuity.lean` — Phase 32 WeakInitCont degenerate OPEN via orbit closure
- `NSCorrSemigroupLipAtZero.lean` — Phase 33 Lip at zero
- `NSCorrSemigroupSelfAdj.lean` — Phase 37a SelfAdj OPEN
- `NSCorrSemigroupSmooth.lean` — Phase 20 SemigroupDef + fix rw [corrSemigroupRate]
- `NSDerivSemigroup.lean` — Phase 25+26 remove sorry from SemigroupBochnerDiff
- `NSExpDecayClose.lean` — Exponential decay
- `NSFourierInner.lean` — Phase 20 FourierEq
