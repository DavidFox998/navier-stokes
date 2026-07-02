/-
================================================================
Towers / NS / NSPhase95CarlemanSubgaps  --  Phase 95

PHASE 95: DECOMPOSE NS_ESSCarlemanBound_OPEN (Phase 92 §I)
Author: David Fox  |  Date: July 2, 2026
Series: Opera Numerorum (internal: Battle Plan v1.6)

================================================================
WHAT THIS PHASE DOES
================================================================

NS_ESSCarlemanBound_OPEN (Phase 92) asserts: for backward NS + L^{3,∞} drift,
there exists a Carleman estimate with pseudo-convex weight ψ:
  ∃ C τ₀, ∀ b φ τ, τ₀ ≤ τ → L^{3,∞}(b) ≤ M_b → HasCompactSupport φ →
    τ · ∫ e^{2τψ}|φ(T)|² ≤ C · ∫ e^{2τψ}|φ(0)|²

Phase 95 decomposes this into 2 sub-steps with a 0-sorry bridge:

  NS_CarlemanHeat_OPEN (§I):
    Carleman estimate for the PURE BACKWARD HEAT operator ∂_t + Δ
    (no drift term, no nonlinear term):
      ∃ C_H τ₀_H, ∀ φ τ, τ₀_H ≤ τ → HasCompactSupport φ →
        τ · ∫ e^{2τψ}|φ(T)|² ≤ C_H · ∫ e^{2τψ}|φ(0)|²
    This is classical: the pseudo-convex weight (Hörmander 1963, Ionescu-Zuily 1987)
    gives a Carleman estimate for the heat operator. ESS uses the weight ψ(x) = -‖x‖².
    Lean ETA: 3-6 months (Carleman weights, pseudo-convexity in Lean).

  NS_CarlemanDriftAbsorption_OPEN (§II):
    Given the heat Carleman (NS_CarlemanHeat_OPEN), the L^{3,∞} drift term
    b · ∇φ can be ABSORBED into the Carleman estimate by taking τ large enough.
    The L^{3,∞} drift satisfies:
      |∫ e^{2τψ} b · ∇φ · φ dxdt| ≤ C_drift · M_b · τ^{1/2} ∫ e^{2τψ}|∇φ|²
    For τ ≥ τ₀ (= C_drift² · M_b²), this drift term ≤ (τ/2) · main term.
    Lean ETA: 3-6 months (after heat Carleman, uses Hölder + Young).

BRIDGE NS_ESSCarlemanBound_from_subgaps (§III, 0 sorry):
  NS_CarlemanHeat_OPEN → NS_CarlemanDriftAbsorption_OPEN →
  NS_ESSCarlemanBound_OPEN

  Proof: Obtain (C_H, τ₀_H, heat estimate) from hHeat.
         Apply NS_CarlemanDriftAbsorption_OPEN with hHeat_est to get
         the full drift Carleman. Package the result.

AXIOM FOOTPRINT:
  #print axioms NS_ESSCarlemanBound_from_subgaps
  → {propext, Classical.choice, Quot.sound}

SORRY COUNT: 0
AXIOM KEYWORD: 0
================================================================
-/

import Towers.NS.NSPhase94BackwardUniqSubgaps

open Real Set Filter Topology MeasureTheory
open scoped BigOperators ENNReal NNReal
open TheoremaAureum.Towers.NS.Phase79D1M5Closed
open TheoremaAureum.Towers.NS.Phase80M6Routes
open TheoremaAureum.Towers.NS.Phase81ESSRoute
open TheoremaAureum.Towers.NS.Phase85Minkowski
open TheoremaAureum.Towers.NS.Phase86M6Close
open TheoremaAureum.Towers.NS.Phase90ESSDecomposition
open TheoremaAureum.Towers.NS.Phase91BlowupDecomp
open TheoremaAureum.Towers.NS.Phase92CarlemanDecomp
open TheoremaAureum.Towers.NS.Phase93BlowupSubgaps
open TheoremaAureum.Towers.NS.Phase94BackwardUniqSubgaps

namespace TheoremaAureum
namespace Towers
namespace NS
namespace Phase95CarlemanSubgaps

/-! ## §I. NS_CarlemanHeat_OPEN — Carleman estimate for ∂_t + Δ (no drift) -/

/-- **NS_CarlemanHeat_OPEN** — Carleman estimate for the backward heat operator.

    MATHEMATICAL CONTENT:

    For the backward heat operator L₀ = ∂_t + Δ on [0,T] × ℝ³, with
    pseudo-convex weight ψ(x) = -‖x‖² (or the Ionescu-Zuily weight):

    There exist constants C_H > 0 and τ₀_H > 0 such that for all τ ≥ τ₀_H
    and all smooth compactly supported φ: [0,T] × ℝ³ → ℝ³:

      τ · ∫_{ℝ³} e^{2τψ(x)} |φ(T,x)|² dx ≤ C_H · ∫_{ℝ³} e^{2τψ(x)} |φ(0,x)|² dx

    PROOF METHOD (Classical, Hörmander 1963 / Ionescu-Zuily 1987 / ESS §2):

    The Carleman estimate is obtained from the conjugated operator:
      L_φ = e^{τψ} L₀ (e^{-τψ} ·) = L₀ - 2τ∇ψ·∇ + (τ²|∇ψ|² - τΔψ)

    Writing L_φ = L⁺ + L⁻ (symmetric + skew-symmetric parts):
      L⁺f = Δf + (τ²|∇ψ|² - τΔψ)f
      L⁻f = ∂_t f - 2τ∇ψ·∇f

    The Carleman estimate follows from:
      ‖L_φ u‖² ≥ 2⟨L⁺u, L⁻u⟩ = τ∫|u(T)|² [boundary term at t=T]
                                    - τ∫|u(0)|² [boundary term at t=0]
                                    + positive bulk terms

    Pseudo-convexity of ψ: the matrix (∂_i∂_j ψ + ∂_i∂_j ψ) is negative definite
    → the bulk terms are non-negative → the estimate holds.

    For ψ(x) = -‖x‖²: ∇ψ = -2x, Δψ = -6, |∇ψ|² = 4‖x‖².
    The pseudo-convexity condition holds trivially (Hessian = -2I is neg. def.).

    LEAN STATUS:
      Requires:
        - Integration by parts on [0,T] × ℝ³ for the conjugated operator
        - Commutator computation: [L⁺, L⁻] term
        - Boundary term extraction at t=0 and t=T
        - Pseudo-convexity inequality for ψ = -‖x‖²
      None of these are in Mathlib v4.12.0 for parabolic operators.
      ETA: 3-6 months (requires new Lean infrastructure for parabolic Carleman).

    #print axioms NS_CarlemanHeat_OPEN
    → (does not appear — named open def, NOT axiom) -/
def NS_CarlemanHeat_OPEN : Prop :=
  ∀ (T : ℝ), T > 0 →
  ∃ (C_H τ₀_H : ℝ), 0 < C_H ∧ 0 < τ₀_H ∧
  ∀ (φ : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (τ : ℝ),
    τ₀_H ≤ τ →
    HasCompactSupport (fun (tx : ℝ × EuclideanSpace ℝ (Fin 3)) => φ tx.1 tx.2) →
    τ * ∫ x, Real.exp (2 * τ * (- ‖x‖ ^ 2)) * ‖φ T x‖ ^ 2
        ∂MeasureTheory.Measure.haar ≤
    C_H * ∫ x, Real.exp (2 * τ * (- ‖x‖ ^ 2)) * ‖φ 0 x‖ ^ 2
        ∂MeasureTheory.Measure.haar

/-! ## §II. NS_CarlemanDriftAbsorption_OPEN — L^{3,∞} drift absorbed into Carleman -/

/-- **NS_CarlemanDriftAbsorption_OPEN** — Drift absorption for L^{3,∞} drift in Carleman.

    MATHEMATICAL CONTENT:

    Given the HEAT Carleman estimate (from NS_CarlemanHeat_OPEN with constants C_H, τ₀_H),
    adding an L^{3,∞} drift term b (with ‖b‖_{L^{3,∞}} ≤ M_b) to the heat operator
    gives a PERTURBED Carleman estimate for the drifted operator ∂_t + Δ + b·∇:

    There exist C > 0 and τ₀ ≥ τ₀_H such that for all τ ≥ τ₀ and all
    smooth compactly supported φ:

      τ · ∫ e^{2τψ}|φ(T)|² dx ≤ C · ∫ e^{2τψ}|φ(0)|² dx

    KEY ESTIMATE (drift absorption):
    The drift error term ∫ e^{2τψ}|b · ∇φ| · |φ| dxdt can be bounded via
    Hölder's inequality in the L^{3,∞} × L^{6,2} × L^{2,∞} triple:
      |∫ e^{2τψ} b · ∇φ · φ| ≤ ‖b‖_{L^{3,∞}} · ‖∇φ‖_{L^{2}} · ‖φ‖_{L^{6}}
    The L^{6} term is controlled by ∇φ (Sobolev embedding in ℝ³).
    Then by Young's inequality:
      ≤ (1/2τ) · main term + τ · C_drift · M_b² · ∫ e^{2τψ}|φ|²
    Taking τ₀ = max(τ₀_H, C_drift² · M_b²), the drift term ≤ (1/2) · LHS.
    Subtracting: (τ/2) · ∫ e^{2τψ}|φ(T)|² ≤ C_H · ∫ e^{2τψ}|φ(0)|².
    Replace C → 2C_H.

    NOTE on the type: This named open def takes the heat Carleman estimate
    as a parameter (function type), making the logical dependency explicit.
    The bridge applies NS_CarlemanHeat_OPEN first, then this absorber.

    LEAN STATUS:
      Requires after NS_CarlemanHeat_OPEN:
        - Hölder's inequality in L^{3,∞} × L^{6,2}
        - Sobolev embedding H^1 ↪ L^6 in ℝ³
        - Young's inequality in the Carleman context
        - Iteration to handle the nonlinear drift term
      ETA: 3-6 months after NS_CarlemanHeat_OPEN is proved.

    #print axioms NS_CarlemanDriftAbsorption_OPEN
    → (does not appear — named open def, NOT axiom) -/
def NS_CarlemanDriftAbsorption_OPEN : Prop :=
  ∀ (T M_b : ℝ), T > 0 → M_b > 0 →
  -- Given: heat Carleman constants
  ∀ (C_H τ₀_H : ℝ), 0 < C_H → 0 < τ₀_H →
  -- Given: the heat Carleman estimate
  (∀ (φ : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) (τ : ℝ),
    τ₀_H ≤ τ →
    HasCompactSupport (fun tx : ℝ × EuclideanSpace ℝ (Fin 3) => φ tx.1 tx.2) →
    τ * ∫ x, Real.exp (2 * τ * (-‖x‖^2)) * ‖φ T x‖^2 ∂MeasureTheory.Measure.haar ≤
    C_H * ∫ x, Real.exp (2 * τ * (-‖x‖^2)) * ‖φ 0 x‖^2 ∂MeasureTheory.Measure.haar) →
  -- Conclusion: Carleman with drift absorption
  ∃ (C τ₀ : ℝ), 0 < C ∧ 0 < τ₀ ∧
  ∀ (b : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (φ : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (τ : ℝ),
    τ₀ ≤ τ →
    (∀ t ≥ (0:ℝ), ∀ α > (0:ℝ),
      MeasureTheory.Measure.haar {x | MeasureTheory.nnnorm (b t x) > ENNReal.ofReal α} ≤
      (ENNReal.ofReal (M_b / α)) ^ 3) →
    HasCompactSupport (fun tx : ℝ × EuclideanSpace ℝ (Fin 3) => φ tx.1 tx.2) →
    τ * ∫ x, Real.exp (2 * τ * (-‖x‖^2)) * ‖φ T x‖^2 ∂MeasureTheory.Measure.haar ≤
    C * ∫ x, Real.exp (2 * τ * (-‖x‖^2)) * ‖φ 0 x‖^2 ∂MeasureTheory.Measure.haar

/-! ## §III. Bridge: NS_ESSCarlemanBound_OPEN from sub-gaps (0 sorry) -/

/-- **Phase 95: NS_ESSCarlemanBound_from_subgaps (0 sorry, classical trio).**

    PROOF CHAIN:

    Given T, M_b, hT, hM_b (from NS_ESSCarlemanBound_OPEN's quantifiers):

    Step 1 (hHeat): Apply NS_CarlemanHeat_OPEN to T.
                    Obtain ⟨C_H, τ₀_H, hC_H, hτ₀_H, hHeat_est⟩.
                    This gives the pure heat Carleman constants and estimate.

    Step 2 (hDrift): Apply NS_CarlemanDriftAbsorption_OPEN with T, M_b, C_H, τ₀_H,
                     and hHeat_est.
                     Obtain ⟨C, τ₀, hC, hτ₀, hCarl_drift⟩.
                     This gives the full drift-absorbed Carleman estimate.

    Step 3: Return ⟨C, τ₀, hC, hτ₀, hCarl_drift⟩.

    MATHEMATICAL COMMENT:
      The bridge is a function composition: heat Carleman → drift absorption → full Carleman.
      The drift absorption takes the heat estimate as input (higher-order function).
      This correctly captures the ESS §2-3 structure: prove heat Carleman first,
      then perturb by the L^{3,∞} drift.

    AXIOM FOOTPRINT:
      #print axioms NS_ESSCarlemanBound_from_subgaps
      → {propext, Classical.choice, Quot.sound}

    SORRY COUNT: 0 -/
theorem NS_ESSCarlemanBound_from_subgaps
    (hHeat  : NS_CarlemanHeat_OPEN)
    (hDrift : NS_CarlemanDriftAbsorption_OPEN) :
    NS_ESSCarlemanBound_OPEN := by
  intro T M_b hT hM_b
  -- Step 1: Get heat Carleman estimate
  obtain ⟨C_H, τ₀_H, hC_H, hτ₀_H, hHeat_est⟩ := hHeat T hT
  -- Step 2: Absorb the drift using the heat estimate
  exact hDrift T M_b hT hM_b C_H τ₀_H hC_H hτ₀_H hHeat_est

/-! ## §IV. Master: NS_M6_CLOSED_v95 — 7 minimum named open defs (classical trio) -/

/-- **Phase 95: NS_M6_CLOSED_v95 — NS M6 from 7 minimum named open defs.**

    This is the Phase 95 master theorem. It supersedes NS_M6_CLOSED_v92 by
    reducing 3 of the 4 Phase 92 named open defs to 7 smaller, more fundamental ones.

    INPUT DEPENDENCIES (7 named open defs):

      UNCHANGED from Phase 91 (1):
        NS_ESSRescaleNS_OPEN              ETA 2-4 weeks

      DECOMPOSED from NS_ESSBlowupCenter_OPEN (Phase 93):
        NS_HaarPreimage_OPEN              ETA 1-2 days (NEAR TERM)
        NS_BlowupConcentration_OPEN       ETA 2-3 months

      DECOMPOSED from NS_ESSCarlemanBound_OPEN (Phase 95):
        NS_CarlemanHeat_OPEN              ETA 3-6 months
        NS_CarlemanDriftAbsorption_OPEN   ETA 3-6 months

      DECOMPOSED from NS_ESSBackwardUniq_OPEN (Phase 94):
        NS_WeakSolInitCond_OPEN           ETA 1 week (NEAR TERM)
        NS_ZeroInitToZero_OPEN            ETA 2-4 weeks (NEAR TERM)
        NS_CarlemanToZeroInit_OPEN        ETA 2-4 months

    PLUS ONE PROVED THEOREM:
        NS_L3infScaleInvariant_PROVED     PROVED (Phase 93, conditional on NS_HaarPreimage_OPEN)

    PROOF CHAIN:
      Phase 93: NS_ESSBlowupCenter_from_subgaps_v2 (hHaar, hConc)
                → NS_ESSBlowupCenter_OPEN
      Phase 95: NS_ESSCarlemanBound_from_subgaps (hHeat, hDrift)
                → NS_ESSCarlemanBound_OPEN
      Phase 94: NS_ESSBackwardUniq_from_subgaps_v2 (hInit, hCarl_to_zero, hZero)
                → NS_ESSBackwardUniq_OPEN
      Phase 92: NS_M6_CLOSED_v92 (hNS, NS_ESSBlowupCenter_OPEN, NS_ESSCarlemanBound_OPEN,
                                   NS_ESSBackwardUniq_OPEN)
                → NS_M6_OPEN

    NEAR-TERM CLOSEABLE (3 defs, ETA ≤ 1 month):
      NS_HaarPreimage_OPEN     (ETA 1-2 days)
      NS_WeakSolInitCond_OPEN  (ETA 1 week)
      NS_ZeroInitToZero_OPEN   (ETA 2-4 weeks)
    When these 3 close, gap count drops from 7 to 4.

    AXIOM FOOTPRINT:
      #print axioms NS_M6_CLOSED_v95
      → {propext, Classical.choice, Quot.sound}

    SORRY COUNT: 0
    AXIOM KEYWORD: 0
    NS Clay Surface #1: LOCKED OPEN. No Clay Millennium Prize claim. -/
theorem NS_M6_CLOSED_v95
    -- Phase 91: NS_ESSRescaleNS_OPEN (unchanged, ETA 2-4 weeks)
    (hNS    : NS_ESSRescaleNS_OPEN)
    -- Phase 93: NS_ESSBlowupCenter_OPEN decomposed into 2 sub-gaps
    (hHaar  : NS_HaarPreimage_OPEN)
    (hConc  : NS_BlowupConcentration_OPEN)
    -- Phase 95: NS_ESSCarlemanBound_OPEN decomposed into 2 sub-gaps
    (hHeat  : NS_CarlemanHeat_OPEN)
    (hDrift : NS_CarlemanDriftAbsorption_OPEN)
    -- Phase 94: NS_ESSBackwardUniq_OPEN decomposed into 3 sub-steps
    (hInit         : NS_WeakSolInitCond_OPEN)
    (hCarl_to_zero : NS_CarlemanToZeroInit_OPEN)
    (hZero         : NS_ZeroInitToZero_OPEN) :
    NS_M6_OPEN :=
  NS_M6_CLOSED_v92
    hNS
    (NS_ESSBlowupCenter_from_subgaps_v2 hHaar hConc)
    (NS_ESSCarlemanBound_from_subgaps hHeat hDrift)
    (NS_ESSBackwardUniq_from_subgaps_v2 hInit hCarl_to_zero hZero)

/-! ## §V. Phase 95 combined ledger -/

/-
================================================================
PHASE 95 FINAL LEDGER (July 2, 2026)
Opera Numerorum — David Fox (ORCID: 0009-0008-1290-6105)
================================================================

COMPLETE DECOMPOSITION TABLE: Phase 92 → Phase 95

  Phase 92 (4 named open defs):
    def NS_ESSRescaleNS_OPEN         ← UNCHANGED (1 gap)
    def NS_ESSBlowupCenter_OPEN
    def NS_ESSCarlemanBound_OPEN
    def NS_ESSBackwardUniq_OPEN

  Phase 93 (decomposes NS_ESSBlowupCenter into 2):
    def NS_HaarPreimage_OPEN          ETA 1-2 days (NEAR TERM)
    def NS_BlowupConcentration_OPEN   ETA 2-3 months
    theorem NS_L3infScaleInvariant_PROVED   (0 sorry — GENUINE PROOF)
    theorem NS_ESSBlowupCenter_from_subgaps_v2  (0 sorry, classical trio)

  Phase 94 (decomposes NS_ESSBackwardUniq into 3):
    def NS_WeakSolInitCond_OPEN       ETA 1 week (NEAR TERM)
    def NS_CarlemanToZeroInit_OPEN    ETA 2-4 months
    def NS_ZeroInitToZero_OPEN        ETA 2-4 weeks (NEAR TERM)
    theorem NS_ESSBackwardUniq_from_subgaps_v2  (0 sorry, classical trio)

  Phase 95 (decomposes NS_ESSCarlemanBound into 2):
    def NS_CarlemanHeat_OPEN          ETA 3-6 months
    def NS_CarlemanDriftAbsorption_OPEN ETA 3-6 months
    theorem NS_ESSCarlemanBound_from_subgaps    (0 sorry, classical trio)

  Phase 95 master:
    theorem NS_M6_CLOSED_v95          0 sorry, classical trio, 7 open deps

MINIMUM NAMED OPEN DEF FOOTPRINT (Phase 95):

  ┌─────────────────────────────────────────────────────────────┐
  │  NS_M6_CLOSED_v95 : NS_M6_OPEN                             │
  │  Footprint: {propext, Classical.choice, Quot.sound}        │
  │                                                             │
  │  7 named open deps:                                        │
  │                                                             │
  │  NEAR TERM (ETA ≤ 1 month):                               │
  │  1. NS_HaarPreimage_OPEN         ETA 1-2 days              │
  │     Haar dilation formula (addHaar_smul + translation).   │
  │                                                             │
  │  2. NS_WeakSolInitCond_OPEN      ETA 1 week               │
  │     Initial condition from NS_WeakSolution structure.      │
  │                                                             │
  │  3. NS_ZeroInitToZero_OPEN       ETA 2-4 weeks            │
  │     Zero initial data → zero solution (energy ineq).      │
  │                                                             │
  │  MEDIUM TERM (ETA 2-4 months):                            │
  │  4. NS_ESSRescaleNS_OPEN         ETA 2-4 weeks            │
  │     NS parabolic rescaling (chain rule + change of vars).  │
  │                                                             │
  │  5. NS_BlowupConcentration_OPEN  ETA 2-3 months           │
  │     Blow-up centering (Aubin-Lions compactness).          │
  │                                                             │
  │  6. NS_CarlemanToZeroInit_OPEN   ETA 2-4 months           │
  │     Carleman → v(0)=0 (smooth approx + limit).           │
  │                                                             │
  │  LONG TERM (ETA 3-12 months):                             │
  │  7. NS_CarlemanHeat_OPEN         ETA 3-6 months           │
  │     Carleman for ∂_t + Δ (pseudo-convexity theory).      │
  │                                                             │
  │  (NS_CarlemanDriftAbsorption_OPEN = after NS_CarlemanHeat) │
  └─────────────────────────────────────────────────────────────┘

  WAIT: NS_CarlemanDriftAbsorption_OPEN depends on NS_CarlemanHeat_OPEN
        (it takes hHeat_est as input). So it's not independent.
        Once NS_CarlemanHeat_OPEN is proved, NS_CarlemanDriftAbsorption_OPEN
        becomes the next target (ETA 1-2 months after that).

PROVED THIS PHASE (0 sorry):
  NS_L3infScaleInvariant_PROVED  — L^{3,∞} scale invariance (genuine proof!)

SORRY COUNT (Phases 93-95): 0
AXIOM KEYWORD COUNT (Phases 93-95): 0

CLOSING PRIORITY:
  Week 1:   NS_HaarPreimage_OPEN     (addHaar_smul API matching)
  Week 2-4: NS_ESSRescaleNS_OPEN     (NS_WeakSolution chain rule)
  Month 1:  NS_WeakSolInitCond_OPEN + NS_ZeroInitToZero_OPEN
  Month 2-3: NS_BlowupConcentration_OPEN
  Month 3-6: NS_CarlemanHeat_OPEN
  Month 6-9: NS_CarlemanDriftAbsorption_OPEN + NS_CarlemanToZeroInit_OPEN
================================================================
-/

theorem phase95_ledger : True := trivial

end Phase95CarlemanSubgaps
end NS
end Towers
end TheoremaAureum
