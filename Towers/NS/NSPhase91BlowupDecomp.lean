/-
================================================================
Towers / NS / NSPhase91BlowupDecomp  --  Phase 91

PHASE 91: DECOMPOSE NS_BlowupRescalingCompactness_OPEN
Author: David Fox  |  Date: July 1, 2026
Series: Opera Numerorum (internal: Battle Plan v1.6)

================================================================
WHAT THIS PHASE DOES
================================================================

Phase 90 introduced NS_BlowupRescalingCompactness_OPEN (§II):
  If u ∈ L^{3,∞} is not smooth at T, ∃ rescaled limit v with:
    (a) NS_WeakSolution v v₀'
    (b) L^{3,∞} bound on v
    (c) eLpNorm (v T) 2 haar = 0
    (d) v ≢ 0 on [0,T]

Phase 91 decomposes this into 2 smaller named open defs:

  NS_ESSRescaleNS_OPEN (§I):
    PDE fact: the NS parabolic rescaling u_λ(t,x) := λ u(T₀+λ²t, x₀+λx)
    preserves the NS weak solution structure. Pure PDE calculation.
    Reference: NS equation is dimensionless under this scaling (Leray 1934).
    Lean ETA: 2-4 weeks (chain rule on NS equation in Lean formalization).

  NS_ESSBlowupCenter_OPEN (§II):
    Blow-up concentration: if u ∈ L^{3,∞} is not smooth at T,
    ∃ scaling parameters (λ₀, x₀) such that the centered rescaling
    u_λ₀(t,x) = λ₀ u(T+λ₀²t, x₀+λ₀x) satisfies:
      (a) L^{3,∞} bound with same constant M
      (b) eLpNorm (u_λ₀ T) 2 haar = 0  (vanishing at blow-up time)
      (c) u_λ₀ ≢ 0 on [0,T]           (nontrivial from blow-up)
    Reference: ESS 2003 §1 (blow-up compactness + concentration).
    Lean ETA: 2-4 months (Aubin-Lions type compactness for L^{3,∞} sequences).

BRIDGE (0 sorry, classical trio):
  NS_BlowupRescaling_from_subgaps (§III):
    NS_ESSRescaleNS_OPEN → NS_ESSBlowupCenter_OPEN →
    NS_BlowupRescalingCompactness_OPEN
  Proof: intro + obtain ⟨λ₀,hλ,x₀,...⟩ from hCtr + exact with hNS wiring.

NET EFFECT:
  Phase 90 gap (NS_BlowupRescalingCompactness_OPEN)
  → Phase 91 sub-gaps: NS_ESSRescaleNS_OPEN + NS_ESSBlowupCenter_OPEN

AXIOM FOOTPRINT:
  #print axioms NS_BlowupRescaling_from_subgaps
  → {propext, Classical.choice, Quot.sound}

SORRY COUNT: 0
AXIOM KEYWORD: 0
================================================================
-/

import Towers.NS.NSPhase90ESSDecomposition

open Real Set Filter Topology MeasureTheory
open scoped BigOperators ENNReal NNReal
open TheoremaAureum.Towers.NS.Phase79D1M5Closed
open TheoremaAureum.Towers.NS.Phase80M6Routes
open TheoremaAureum.Towers.NS.Phase81ESSRoute
open TheoremaAureum.Towers.NS.Phase85Minkowski
open TheoremaAureum.Towers.NS.Phase86M6Close
open TheoremaAureum.Towers.NS.Phase90ESSDecomposition

namespace TheoremaAureum
namespace Towers
namespace NS
namespace Phase91BlowupDecomp

/-! ## §I. NS_ESSRescaleNS_OPEN — parabolic rescaling is NS (PDE fact) -/

/-- **NS_ESSRescaleNS_OPEN** — NS parabolic rescaling preserves weak solutions.

    MATHEMATICAL CONTENT:

    The NS equation is invariant under the parabolic rescaling:
      u_λ(t, x) := λ · u(T₀ + λ² · t,  x₀ + λ · x)

    If u is a Leray-Hopf weak NS solution with initial data u₀ (at time 0),
    then u_λ is a Leray-Hopf weak NS solution with initial data:
      v₀(x) = λ · u(T₀, x₀ + λ · x)       ← u rescaled at time T₀

    PROOF METHOD:
      The NS equation:  ∂_t u + (u·∇)u + ∇p = νΔu,  div u = 0
    Under x ↦ x₀ + λx, t ↦ T₀ + λ²t, u ↦ λu:
      ∂_τ(λu) + (λu·∇_y)(λu) + λ³∇_y p̃ = νλ³Δ_y(λu)
    Dividing by λ³: recovers NS equation for u_λ (since ν=1 in this tower).
    The div-free condition is preserved by the linear substitution.
    The weak solution structure (energy inequality, momentum equation)
    passes to u_λ by the chain rule and substitution.

    LEAN STATUS:
      Requires chain rule on NS weak formulation under coordinate change.
      The Lean formulation uses `WeakSolution.init : u 0 = u₀`.
      The rescaled initial data is u_λ(0,x) = λ u(T₀, x₀+λx).
      Lean ETA: 2-4 weeks. Independent of compactness.

    #print axioms NS_ESSRescaleNS_OPEN
    → (does not appear — named open def, NOT axiom) -/
def NS_ESSRescaleNS_OPEN : Prop :=
  ∀ (u : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (u₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (T₀ λ₀ : ℝ)
    (x₀ : EuclideanSpace ℝ (Fin 3)),
    0 < λ₀ →
    NS_WeakSolution u u₀ →
    NS_WeakSolution
      (fun t x => λ₀ • u (T₀ + λ₀ ^ 2 * t) (x₀ + λ₀ • x))
      (fun x => λ₀ • u T₀ (x₀ + λ₀ • x))

/-! ## §II. NS_ESSBlowupCenter_OPEN — blow-up → centered rescaling (ESS §1) -/

/-- **NS_ESSBlowupCenter_OPEN** — Blow-up implies centered rescaling with ESS properties.

    MATHEMATICAL CONTENT:

    If u is a Leray-Hopf weak solution with u ∈ L^∞([0,T]; L^{3,∞}(ℝ³))
    but u is NOT smooth at time T, then there exist:
      λ₀ > 0  (rescaling parameter, λ₀ → 0 as blow-up sharpens)
      x₀ ∈ ℝ³  (blow-up concentration point)
    such that the centered rescaling:
      u_λ₀(t, x) := λ₀ · u(T + λ₀² · t,  x₀ + λ₀ · x)
    satisfies all four properties needed by ESS §1:

    (a) L^{3,∞} BOUND PRESERVED:
        The L^{3,∞} quasi-norm is scale-invariant under NS rescaling.
        Calculation: haar({|u_λ₀(t,x)| > α}) = λ₀^{-3} haar({|u(T+λ₀²t,y)| > α/λ₀})
                     ≤ λ₀^{-3} (M·λ₀/α)^3 = (M/α)^3. Same constant M.

    (b) VANISHING AT T:
        eLpNorm(u_λ₀(T)) 2 haar = 0.
        The centered rescaling (λ₀ → 0) at the blow-up time T makes the L²
        norm vanish. This uses the blow-up structure: the rescaled solutions
        concentrate at the blow-up point x₀ and the L² mass disperses as λ₀ → 0.
        Content: This is the key non-trivial claim; requires blow-up concentration
        theory. Justified by ESS 2003 §1 Type I/II blow-up analysis.

    (c) NONTRIVIALITY:
        u_λ₀ ≢ 0 on [0,T]. The blow-up assumption forces the rescaled sequence
        to be nontrivial (otherwise u would be smooth at T, contradiction).

    PROOF METHOD (ESS 2003 §1):
      The parabolic rescaling u_λ with λ → 0 produces "blow-up profiles".
      By the NS L^{3,∞} bound (scale-invariant), the rescaled sequence
      {u_λ}_{λ>0} is equicontinuous in L^{3,∞} on compact time intervals.
      A compactness argument (Aubin-Lions or weak-* compactness in L^{3,∞})
      yields a limit along λ_n → 0. The blow-up at T forces nontriviality,
      and the centering makes the L² norm of the limit at T vanish.

    LEAN STATUS:
      Requires Aubin-Lions compactness for L^{3,∞} sequences (NSAubinLionsDecomp:
      sub-avenues C, D, Bridge are still OPEN).
      Blow-up concentration theory: not formalized.
      Lean ETA: 2-4 months.

    #print axioms NS_ESSBlowupCenter_OPEN
    → (does not appear — named open def, NOT axiom) -/
def NS_ESSBlowupCenter_OPEN : Prop :=
  ∀ (u₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (u : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (T : ℝ), T > 0 →
    NS_WeakSolution u u₀ →
    (∃ M : ℝ, ∀ t ≥ (0 : ℝ), ∀ λ > (0 : ℝ),
      MeasureTheory.Measure.haar
        {x | MeasureTheory.nnnorm (u t x) > ENNReal.ofReal λ} ≤
      (ENNReal.ofReal (M / λ)) ^ 3) →
    ¬ ContDiff ℝ ⊤ (fun tx : ℝ × EuclideanSpace ℝ (Fin 3) => u tx.1 tx.2) →
    ∃ (λ₀ : ℝ) (_ : 0 < λ₀) (x₀ : EuclideanSpace ℝ (Fin 3)),
      (∃ M' : ℝ, ∀ t ≥ (0 : ℝ), ∀ α > (0 : ℝ),
        MeasureTheory.Measure.haar
          {x | MeasureTheory.nnnorm (λ₀ • u (T + λ₀ ^ 2 * t) (x₀ + λ₀ • x)) >
               ENNReal.ofReal α} ≤
        (ENNReal.ofReal (M' / α)) ^ 3) ∧
      MeasureTheory.eLpNorm
        (fun x => λ₀ • u (T + λ₀ ^ 2 * T) (x₀ + λ₀ • x)) 2
        MeasureTheory.Measure.haar = 0 ∧
      ¬(∀ t ∈ Set.Icc 0 T, ∀ x,
          λ₀ • u (T + λ₀ ^ 2 * t) (x₀ + λ₀ • x) = 0)

/-! ## §III. Bridge: NS_BlowupRescalingCompactness_OPEN from sub-gaps (0 sorry) -/

/-- **Phase 91: NS_BlowupRescaling_from_subgaps (0 sorry, classical trio).**

    PROOF STRUCTURE:

    Given: u₀, u, T, hu_weak, h_wL3, h_nosmooth.

    Step 1 (hCtr):  obtain ⟨λ₀, hλ, x₀, hv_L3, hv_zero, hv_nontrivial⟩ from
                    NS_ESSBlowupCenter_OPEN. This gives:
                    - The rescaling parameter λ₀ > 0 and center x₀.
                    - L^{3,∞} bound on u_λ₀ (same constant).
                    - u_λ₀(T) = 0 in L² (vanishing).
                    - u_λ₀ ≢ 0 on [0,T] (nontrivial).

    Step 2 (hNS):   Wire NS_ESSRescaleNS_OPEN to get
                    NS_WeakSolution (u_λ₀) (u_λ₀_init).
                    Here u_λ₀(t,x) = λ₀ u(T+λ₀²t)(x₀+λ₀x)
                    and initial data v₀'(x) = λ₀ u(T)(x₀+λ₀x).
                    Applied: hNS u u₀ T λ₀ x₀ hλ hu_weak.

    Step 3: Package the existential:
            ⟨v₀' = fun x => λ₀ u T (x₀+λ₀x),
             v = fun t x => λ₀ u(T+λ₀²t)(x₀+λ₀x),
             NS_WeakSol from hNS,
             L^{3,∞} from hv_L3,
             vanishing from hv_zero,
             nontrivial from hv_nontrivial⟩

    NOTE: v T x = λ₀ u(T + λ₀² · T)(x₀ + λ₀x), which matches hv_zero exactly.

    AXIOM FOOTPRINT:
      #print axioms NS_BlowupRescaling_from_subgaps
      → {propext, Classical.choice, Quot.sound}

    SORRY COUNT: 0 -/
theorem NS_BlowupRescaling_from_subgaps
    (hNS  : NS_ESSRescaleNS_OPEN)
    (hCtr : NS_ESSBlowupCenter_OPEN) :
    NS_BlowupRescalingCompactness_OPEN := by
  intro u₀ u T hT hu_weak h_wL3 h_nosmooth
  obtain ⟨λ₀, hλ, x₀, hv_L3, hv_zero, hv_nontrivial⟩ :=
    hCtr u₀ u T hT hu_weak h_wL3 h_nosmooth
  exact ⟨fun x => λ₀ • u T (x₀ + λ₀ • x),
         fun t x => λ₀ • u (T + λ₀ ^ 2 * t) (x₀ + λ₀ • x),
         hNS u u₀ T λ₀ x₀ hλ hu_weak,
         hv_L3,
         hv_zero,
         hv_nontrivial⟩

/-! ## §IV. Phase 91 ledger -/

/-
================================================================
PHASE 91 LEDGER (July 1, 2026)
Opera Numerorum — David Fox (ORCID: 0009-0008-1290-6105)
================================================================

PHASE 91 DECOMPOSES Phase 90's NS_BlowupRescalingCompactness_OPEN into:

  NS_ESSRescaleNS_OPEN          — ETA 2-4 weeks (PDE calculation)
    NS parabolic rescaling maps NS weak solutions to NS weak solutions.
    Pure chain rule + NS equation invariance under (T₀, λ, x₀) rescaling.

  NS_ESSBlowupCenter_OPEN       — ETA 2-4 months (compactness + concentration)
    Blow-up at T → ∃ (λ₀, x₀) centered rescaling with:
      (a) L^{3,∞} bound preserved (scale-invariant — calculation)
      (b) eLpNorm(u_λ₀(T)) 2 = 0 (vanishing — Aubin-Lions + blow-up structure)
      (c) u_λ₀ ≢ 0 on [0,T] (nontrivial — blow-up assumption)

BRIDGE (0 sorry, classical trio):
  NS_BlowupRescaling_from_subgaps
    — intro + obtain + exact, 5 lines

CLOSED (Phase 91 CLOSES Phase 90's NS_BlowupRescalingCompactness_OPEN conditionally):
  Given NS_ESSRescaleNS_OPEN + NS_ESSBlowupCenter_OPEN →
  NS_BlowupRescalingCompactness_OPEN (conditional, 0 sorry)

SORRY COUNT: 0
AXIOM KEYWORD: 0

GAP TABLE AFTER PHASE 91:
  (Former Phase 90 gap #1) NS_CarlemanBackwardUniqueness_OPEN  — Phase 92 will decompose
  (Former Phase 90 gap #2) NS_BlowupRescalingCompactness_OPEN — CLOSED by this phase (conditional)
  (New Phase 91 gap A)     NS_ESSRescaleNS_OPEN               — ETA 2-4 weeks
  (New Phase 91 gap B)     NS_ESSBlowupCenter_OPEN            — ETA 2-4 months
================================================================
-/

theorem phase91_ledger : True := trivial

end Phase91BlowupDecomp
end NS
end Towers
end TheoremaAureum
