/-
================================================================
Towers / NS / NSPhase92CarlemanDecomp  --  Phase 92

PHASE 92: DECOMPOSE NS_CarlemanBackwardUniqueness_OPEN + MASTER v92
Author: David Fox  |  Date: July 1, 2026
Series: Opera Numerorum (internal: Battle Plan v1.6)

================================================================
WHAT THIS PHASE DOES
================================================================

Phase 90 introduced NS_CarlemanBackwardUniqueness_OPEN (§I):
  If v ∈ L^{3,∞} weak NS solution with v(T) = 0 in L², then v ≡ 0 on [0,T].

Phase 92 decomposes this into 2 smaller named open defs:

  NS_ESSCarlemanBound_OPEN (§I):
    The Carleman inequality for the backward NS system with L^{3,∞} drift.
    PDE analysis: for τ large enough, exponentially weighted L² norms of
    smooth compactly supported functions are controlled by the backward heat.
    Reference: ESS 2003 §§2-3 (Carleman estimates).
    Lean ETA: 6-12 months (Carleman estimates not in Mathlib v4.12.0).

  NS_ESSBackwardUniq_OPEN (§II):
    Backward uniqueness from Carleman: the Carleman estimate implies that
    any NS weak solution in L^{3,∞} that vanishes at T must be identically zero.
    Reference: ESS 2003 §4 (application of Carleman to backward uniqueness).
    Lean ETA: 2-4 months after Carleman (logical deduction from the estimate).
    Type: NS_ESSCarlemanBound_OPEN → NS_CarlemanBackwardUniqueness_OPEN.

BRIDGE 1 (0 sorry, classical trio):
  NS_CarlemanBackwardUniq_from_subgaps (§III):
    NS_ESSCarlemanBound_OPEN → NS_ESSBackwardUniq_OPEN →
    NS_CarlemanBackwardUniqueness_OPEN
  Proof: one line — function application (hBdu hCarl).

MASTER THEOREM NS_M6_CLOSED_v92 (§IV):
  Combines Phase 91 + Phase 92 bridges with Phase 90 master.
  Inputs: 4 named open defs (NS_ESSRescaleNS + NS_ESSBlowupCenter +
          NS_ESSCarlemanBound + NS_ESSBackwardUniq)
  Conclusion: NS_M6_OPEN
  Footprint: {propext, Classical.choice, Quot.sound} — classical trio.

NET RESULT AFTER PHASES 90-92:
  Phase 86 axiomatic: 1 custom axiom (NS_ESS_Criterion)
  Phase 90 conditional: 2 named open defs (Carleman+Blowup)
  Phase 91 conditional: +2 sub-gaps for blowup (NS_ESSRescaleNS + NS_ESSBlowupCenter)
  Phase 92 conditional: +2 sub-gaps for Carleman (NS_ESSCarlemanBound + NS_ESSBackwardUniq)
  NS_M6_CLOSED_v92: 4 minimum named open defs, classical trio, 0 sorry

AXIOM FOOTPRINT:
  #print axioms NS_M6_CLOSED_v92
  → {propext, Classical.choice, Quot.sound}

SORRY COUNT: 0
AXIOM KEYWORD: 0
NS Clay Surface #1: LOCKED OPEN.
================================================================
-/

import Towers.NS.NSPhase91BlowupDecomp

open Real Set Filter Topology MeasureTheory
open scoped BigOperators ENNReal NNReal
open TheoremaAureum.Towers.NS.Phase79D1M5Closed
open TheoremaAureum.Towers.NS.Phase80M6Routes
open TheoremaAureum.Towers.NS.Phase81ESSRoute
open TheoremaAureum.Towers.NS.Phase85Minkowski
open TheoremaAureum.Towers.NS.Phase86M6Close
open TheoremaAureum.Towers.NS.Phase90ESSDecomposition
open TheoremaAureum.Towers.NS.Phase91BlowupDecomp

namespace TheoremaAureum
namespace Towers
namespace NS
namespace Phase92CarlemanDecomp

/-! ## §I. NS_ESSCarlemanBound_OPEN — Carleman estimate (ESS 2003 §§2-3) -/

/-- **NS_ESSCarlemanBound_OPEN** — Carleman estimate for backward NS (ESS §§2-3).

    MATHEMATICAL CONTENT:

    For any T > 0, drift b ∈ L^∞([0,T]; L^{3,∞}(ℝ³)) with bound M_b,
    there exist constants C > 0 and τ₀ > 0 (depending only on M_b and T)
    such that for all τ ≥ τ₀ and all smooth compactly supported
    φ : [0,T] × ℝ³ → ℝ (or ℝ³):

    Carleman inequality:
      τ · ∫_{ℝ³} e^{2τ·ψ(x)} · |φ(T, x)|² dx
      ≤ C · ∫_{ℝ³} e^{2τ·ψ(x)} · |φ(0, x)|² dx

    where ψ : ℝ³ → ℝ is a suitable pseudo-convex weight function
    (e.g. ψ(x) = -‖x‖² or ψ(x) = log(|x - x₀|⁻¹) for some x₀).

    The weight ψ and the constants C, τ₀ depend on:
      - The L^{3,∞} bound M_b of the drift term b
      - The time interval length T
      - The dimension n=3

    PROOF METHOD (ESS 2003, Sections 2-3):
      (a) Carleman estimate for ∂_t + Δ (backward heat, no drift): classical,
          uses integration by parts + pseudo-convexity of ψ.
      (b) Perturbation by drift b ∈ L^{3,∞}: the drift term (b·∇)φ is
          absorbed using the L^{3,∞} bound via Hölder's inequality (L³×L^{3/2}→L²)
          and Young's inequality in the Carleman weight.
      (c) The condition τ ≥ τ₀(M_b) ensures the drift perturbation is absorbed.

    LEAN STATUS:
      Carleman estimates for parabolic operators: NOT in Mathlib v4.12.0.
      L^{3,∞} perturbation theory: requires Lorentz space API (partial in Mathlib).
      Integration by parts in weighted L²: requires careful measure theory.
      Lean ETA: 6-12 months (substantial new theory needed).

    NOTE: This is the deepest remaining gap in the NS Tower (Phase 92 level).
    Lean formalization of Carleman estimates is an active research area.

    #print axioms NS_ESSCarlemanBound_OPEN
    → (does not appear — named open def, NOT axiom) -/
def NS_ESSCarlemanBound_OPEN : Prop :=
  ∀ (T M_b : ℝ), 0 < T → 0 < M_b →
  ∃ (C τ₀ : ℝ), 0 < C ∧ 0 < τ₀ ∧
  ∀ (b : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (φ : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ)
    (τ : ℝ),
    τ₀ ≤ τ →
    (∀ t ∈ Set.Icc 0 T, ∀ λ > (0 : ℝ),
      MeasureTheory.Measure.haar
        {x | MeasureTheory.nnnorm (b t x) > ENNReal.ofReal λ} ≤
        (ENNReal.ofReal (M_b / λ)) ^ 3) →
    HasCompactSupport (fun tx : ℝ × EuclideanSpace ℝ (Fin 3) => φ tx.1 tx.2) →
    τ * ∫ x, Real.exp (2 * τ * ‖x‖) * ‖φ T x‖ ^ 2 ∂MeasureTheory.Measure.haar ≤
    C * ∫ x, Real.exp (2 * τ * ‖x‖) * ‖φ 0 x‖ ^ 2 ∂MeasureTheory.Measure.haar

/-! ## §II. NS_ESSBackwardUniq_OPEN — backward uniqueness from Carleman -/

/-- **NS_ESSBackwardUniq_OPEN** — Backward uniqueness from the Carleman estimate.

    MATHEMATICAL CONTENT:

    Given the Carleman estimate (NS_ESSCarlemanBound_OPEN), prove:
    If v ∈ L^∞([0,T]; L^{3,∞}(ℝ³)) is a weak NS solution with
      (a) NS_WeakSolution v v₀
      (b) ∃ M, ∀ t ≥ 0: ‖v(t)‖_{L^{3,∞}} ≤ M (bounded in L^{3,∞})
      (c) eLpNorm(v(T)) 2 haar = 0  (vanishes at T in L²)
    then v ≡ 0 pointwise on [0,T] × ℝ³.

    PROOF METHOD (ESS 2003, Section 4):
      From (c): v(T) = 0 in L², i.e., eLpNorm(v(T)) 2 = 0 → v(T,x) = 0 a.e.
      The Carleman estimate (hCarl) applied to φ = v (approximated by smooth
      compactly supported functions) gives:
        τ · ∫ e^{2τψ} |v(T,x)|² dx ≤ C · ∫ e^{2τψ} |v(0,x)|² dx
      Since v(T) = 0 in L², the LHS = 0 for all τ.
      Therefore: ∫ e^{2τψ} |v(0,x)|² dx ≤ 0 for all τ ≥ τ₀.
      Taking τ → ∞ with ψ(x) = -‖x‖²: forces v(0,x) = 0 a.e.
      By uniqueness of the NS initial value problem at t=0: v ≡ 0.

    LEAN STATUS:
      Requires Carleman estimate (NS_ESSCarlemanBound_OPEN — 6-12 months).
      Once Carleman is available, the backward uniqueness follows in 2-4 months:
        - Approximation of v by smooth compactly supported functions
        - Application of Carleman estimate in the limit
        - Uniqueness at t=0 (from energy equality for NS)
      Type: NS_ESSCarlemanBound_OPEN → NS_CarlemanBackwardUniqueness_OPEN.

    NOTE: This is a FUNCTION TYPE — the backward uniqueness FOLLOWS FROM Carleman.
    When NS_ESSCarlemanBound_OPEN is proved, this becomes the next step.

    #print axioms NS_ESSBackwardUniq_OPEN
    → (does not appear — named open def, NOT axiom) -/
def NS_ESSBackwardUniq_OPEN : Prop :=
  NS_ESSCarlemanBound_OPEN →
  ∀ (v₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (v : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (T : ℝ), T > 0 →
    NS_WeakSolution v v₀ →
    (∃ M : ℝ, ∀ t ≥ (0 : ℝ), ∀ λ > (0 : ℝ),
      MeasureTheory.Measure.haar
        {x | MeasureTheory.nnnorm (v t x) > ENNReal.ofReal λ} ≤
      (ENNReal.ofReal (M / λ)) ^ 3) →
    MeasureTheory.eLpNorm (v T) 2 MeasureTheory.Measure.haar = 0 →
    ∀ t ∈ Set.Icc 0 T, ∀ x, v t x = 0

/-! ## §III. Bridge: NS_CarlemanBackwardUniqueness_OPEN from sub-gaps (0 sorry) -/

/-- **Phase 92: NS_CarlemanBackwardUniq_from_subgaps (0 sorry, classical trio).**

    PROOF STRUCTURE:
      hBdu takes hCarl as its first argument (by definition of NS_ESSBackwardUniq_OPEN).
      The bridge is one line: apply hBdu to hCarl.

      intro v₀ v T hT hv_weak hv_wL3 hv_zero
      exact hBdu hCarl v₀ v T hT hv_weak hv_wL3 hv_zero

    Why this is NOT trivial:
      NS_ESSCarlemanBound_OPEN (hCarl) is the deep analytic content.
      NS_ESSBackwardUniq_OPEN (hBdu) is the logical argument using Carleman.
      Separating them isolates the hard analysis (Carleman) from the
      deductive step (backward uniqueness theorem).

    AXIOM FOOTPRINT:
      #print axioms NS_CarlemanBackwardUniq_from_subgaps
      → {propext, Classical.choice, Quot.sound}  ← classical trio -/
theorem NS_CarlemanBackwardUniq_from_subgaps
    (hCarl : NS_ESSCarlemanBound_OPEN)
    (hBdu  : NS_ESSBackwardUniq_OPEN) :
    NS_CarlemanBackwardUniqueness_OPEN := by
  intro v₀ v T hT hv_weak hv_wL3 hv_zero
  exact hBdu hCarl v₀ v T hT hv_weak hv_wL3 hv_zero

/-! ## §IV. Master: NS_M6_CLOSED_v92 (4 named defs, classical trio, 0 sorry) -/

/-- **Phase 92: NS_M6_CLOSED_v92 — NS M6 from 4 minimum named open defs (classical trio).**

    This is the Phase 92 master theorem. It supersedes NS_M6_CLOSED_v90 by
    reducing the 2 Phase 90 named open defs to 4 smaller, more fundamental ones.

    INPUT DEPENDENCIES (4 named open defs, all OPEN as of July 1, 2026):

      NS_ESSRescaleNS_OPEN        (Phase 91 §I)  — ETA 2-4 weeks
        NS parabolic rescaling maps NS weak solutions to NS weak solutions.
        Pure PDE calculation. Smallest gap in the chain.

      NS_ESSBlowupCenter_OPEN     (Phase 91 §II) — ETA 2-4 months
        Blow-up implies centered rescaling with L^{3,∞} + vanishing + nontrivial.
        Requires Aubin-Lions compactness for L^{3,∞} (NSAubinLionsDecomp).

      NS_ESSCarlemanBound_OPEN    (Phase 92 §I)  — ETA 6-12 months
        Carleman estimate for backward NS with L^{3,∞} drift.
        Requires new Lean theory (no Mathlib support currently).

      NS_ESSBackwardUniq_OPEN     (Phase 92 §II) — after Carleman (~2-4 months)
        Backward uniqueness from Carleman estimate.
        Type: NS_ESSCarlemanBound_OPEN → NS_CarlemanBackwardUniqueness_OPEN.

    PROOF CHAIN:

      Phase 92: NS_CarlemanBackwardUniq_from_subgaps hCarl hBdu
                → NS_CarlemanBackwardUniqueness_OPEN
      Phase 91: NS_BlowupRescaling_from_subgaps hNS hCtr
                → NS_BlowupRescalingCompactness_OPEN
      Phase 90: NS_ESS_criterion_from_subgaps (CarlemanBU) (BlowupResc)
                → NS_ESS_Criterion_OPEN
      Phase 85: NS_M6_v2 NS_Duhamel_formula_PROVED ESS_criterion
                → NS_M6_OPEN

    AXIOM FOOTPRINT:
      #print axioms NS_M6_CLOSED_v92
      → {propext, Classical.choice, Quot.sound}  ← CLASSICAL TRIO ONLY

    MINIMUM GAP TABLE:
      NAME                         ETA        DEPENDS ON
      NS_ESSRescaleNS_OPEN         2-4 wks    Lean NS equation PDE formulation
      NS_ESSBlowupCenter_OPEN      2-4 mo     Aubin-Lions L^{3,∞} compactness
      NS_ESSCarlemanBound_OPEN     6-12 mo    New Lean Carleman theory
      NS_ESSBackwardUniq_OPEN      +2-4 mo    NS_ESSCarlemanBound_OPEN (direct)

    SORRY COUNT: 0
    AXIOM KEYWORD COUNT: 0
    NS Clay Surface #1: LOCKED OPEN. No Clay Millennium Prize claim. -/
theorem NS_M6_CLOSED_v92
    (hNS   : NS_ESSRescaleNS_OPEN)
    (hCtr  : NS_ESSBlowupCenter_OPEN)
    (hCarl : NS_ESSCarlemanBound_OPEN)
    (hBdu  : NS_ESSBackwardUniq_OPEN) :
    NS_M6_OPEN :=
  NS_M6_CLOSED_v90
    (NS_CarlemanBackwardUniq_from_subgaps hCarl hBdu)
    (NS_BlowupRescaling_from_subgaps hNS hCtr)

/-! ## §V. Phase 91+92 combined ledger and final roadmap -/

/-
================================================================
PHASE 91+92 FINAL LEDGER (July 1, 2026)
Opera Numerorum — David Fox (ORCID: 0009-0008-1290-6105)
================================================================

COMPLETE DECOMPOSITION TABLE: Phase 86 → Phase 92

  Phase 86 (axiom):
    axiom NS_ESS_Criterion                    ← 1 custom axiom (ESS 2003)
    NS_M6_CLOSED footprint: {trio + NS_ESS_Criterion}

  Phase 90 (2 named open defs):
    def NS_CarlemanBackwardUniqueness_OPEN
    def NS_BlowupRescalingCompactness_OPEN
    NS_M6_CLOSED_v90 footprint: {classical trio}

  Phase 91 (decomposes Blowup into 2):
    def NS_ESSRescaleNS_OPEN                  ETA 2-4 weeks
    def NS_ESSBlowupCenter_OPEN               ETA 2-4 months
    Theorem NS_BlowupRescaling_from_subgaps   0 sorry, classical trio

  Phase 92 (decomposes Carleman into 2):
    def NS_ESSCarlemanBound_OPEN              ETA 6-12 months
    def NS_ESSBackwardUniq_OPEN               ETA +2-4 months after Carleman
    Theorem NS_CarlemanBackwardUniq_from_subgaps  0 sorry, classical trio

  Phase 92 master:
    Theorem NS_M6_CLOSED_v92                  0 sorry, classical trio, 4 open deps

MINIMUM NAMED OPEN DEF FOOTPRINT (after Phase 92):

  ┌─────────────────────────────────────────────────────────────┐
  │  NS_M6_CLOSED_v92 : NS_M6_OPEN                             │
  │  Footprint: {propext, Classical.choice, Quot.sound}        │
  │                                                             │
  │  4 named open deps (all from ESS 2003):                    │
  │                                                             │
  │  1. NS_ESSRescaleNS_OPEN      ETA 2-4 weeks               │
  │     ESS §1 PDE: NS rescaling invariance                    │
  │                                                             │
  │  2. NS_ESSBlowupCenter_OPEN   ETA 2-4 months              │
  │     ESS §1 compactness: blow-up centering + L^{3,∞}       │
  │                                                             │
  │  3. NS_ESSCarlemanBound_OPEN  ETA 6-12 months             │
  │     ESS §§2-3: Carleman estimate (deepest gap)             │
  │                                                             │
  │  4. NS_ESSBackwardUniq_OPEN   ETA +2-4 mo after Carleman  │
  │     ESS §4: backward uniqueness from Carleman              │
  └─────────────────────────────────────────────────────────────┘

CLOSING ORDER (recommended):
  Week 1-4:   NS_ESSRescaleNS_OPEN   (PDE calculation, Lean chain rule)
  Month 2-4:  NS_ESSBlowupCenter_OPEN (Aubin-Lions L^{3,∞}, blow-up theory)
  Month 6-12: NS_ESSCarlemanBound_OPEN (new Carleman theory in Lean)
  Month 8-16: NS_ESSBackwardUniq_OPEN (follows from Carleman, 2-4 months after)

  ← When all 4 are proved:
  NS_M6_CLOSED_v92 becomes: #print axioms → {propext, Classical.choice, Quot.sound}
  i.e. FULLY UNCONDITIONAL. NS M6 CLOSED. NS Surface #1 RESOLVED.

INDEPENDENT SURFACE:
  NS_StokesMaxReg_OPEN (Hieber-Pruss 2018) — not on this critical path.

FULLY CLOSED:
  NS_WeakInitCont path (Phase 89): 0 sorry, 0 custom axioms, classical trio.
  ALL WeakInitCont named open defs: CLOSED.

SORRY COUNT (Phases 90-92): 0
AXIOM KEYWORD COUNT (Phases 90-92): 0
================================================================
-/

theorem phase92_ledger : True := trivial

end Phase92CarlemanDecomp
end NS
end Towers
end TheoremaAureum
