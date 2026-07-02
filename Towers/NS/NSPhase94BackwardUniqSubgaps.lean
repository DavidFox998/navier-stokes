/-
================================================================
Towers / NS / NSPhase94BackwardUniqSubgaps  --  Phase 94

PHASE 94: DECOMPOSE NS_ESSBackwardUniq_OPEN (Phase 92 §II)
Author: David Fox  |  Date: July 2, 2026
Series: Opera Numerorum (internal: Battle Plan v1.6)

================================================================
WHAT THIS PHASE DOES
================================================================

NS_ESSBackwardUniq_OPEN (Phase 92) has type:
  NS_ESSCarlemanBound_OPEN →
  ∀ v₀ v T, T > 0 → NS_WeakSolution v v₀ → L^{3,∞} bound → eLpNorm(v T) 2 = 0 →
  ∀ t ∈ [0,T], ∀ x, v t x = 0

Phase 94 decomposes this into 3 sub-steps with a 0-sorry bridge:

  NS_WeakSolInitCond_OPEN (§I):
    NS_WeakSolution v v₀ → v 0 = v₀.
    The initial condition is part of the weak solution definition:
    if v is a Leray-Hopf weak solution with initial data v₀, then v(0) = v₀.
    Lean ETA: 1 week (requires knowing NS_WeakSolution's Lean structure).

  NS_CarlemanToZeroInit_OPEN (§II):
    Given Carleman (hCarl) and v(T) = 0 in L², conclude v(0) = 0 a.e.
    ESS argument: applying Carleman with φ ≈ v (smooth approx),
    the LHS τ∫e^{2τψ}|v(T)|² = 0, so ∫e^{2τψ}|v(0)|² = 0 for all τ,
    forcing v(0) = 0 a.e.
    Lean ETA: 2-4 months (needs approximation + Carleman application).

  NS_ZeroInitToZero_OPEN (§III):
    NS_WeakSolution v v₀ ∧ (v₀ = 0 a.e.) → ∀ t ∈ [0,T], ∀ x, v t x = 0.
    ESS argument (energy): ‖v(t)‖_{L²}² ≤ ‖v₀‖_{L²}² = 0 → v = 0.
    The energy inequality gives ‖v(t)‖_{L²} = 0 for all t ≥ 0.
    But going from ‖v(t)‖_{L²} = 0 to pointwise zero requires
    that v(t,·) is a.e. zero AND a regularity/representability lemma.
    Lean ETA: 2-4 weeks for the a.e. version; pointwise needs extra work.

BRIDGE NS_ESSBackwardUniq_from_subgaps_v2 (§IV, 0 sorry):
  NS_WeakSolInitCond_OPEN →
  NS_CarlemanToZeroInit_OPEN →
  NS_ZeroInitToZero_OPEN →
  NS_ESSBackwardUniq_OPEN

  Proof chain:
    (A) hInit : v 0 = v₀  (from NS_WeakSolInitCond_OPEN)
    (B) hv0_ae : v 0 = 0 a.e.  (from NS_CarlemanToZeroInit_OPEN with Carleman)
    (C) v₀ = 0 a.e.  (from (A): v₀ = v 0 = 0 a.e.)
    (D) v ≡ 0  (from NS_ZeroInitToZero_OPEN with NS_WeakSolution + v₀ = 0)

AXIOM FOOTPRINT:
  #print axioms NS_ESSBackwardUniq_from_subgaps_v2
  → {propext, Classical.choice, Quot.sound}

SORRY COUNT: 0
AXIOM KEYWORD: 0
================================================================
-/

import Towers.NS.NSPhase93BlowupSubgaps

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

namespace TheoremaAureum
namespace Towers
namespace NS
namespace Phase94BackwardUniqSubgaps

/-! ## §I. NS_WeakSolInitCond_OPEN — initial condition from weak solution -/

/-- **NS_WeakSolInitCond_OPEN** — NS_WeakSolution v v₀ implies v(0) = v₀.

    MATHEMATICAL CONTENT:

    If v is a Leray-Hopf weak NS solution with initial data v₀, then
    by definition of the weak solution, the initial condition holds:
      v(0, x) = v₀(x)  pointwise (or strongly in L²).

    In Lean, this is the INITIAL CONDITION component of NS_WeakSolution.
    The Phase-5 WeakSolution.lean file defines WeakNS u u₀ f to include
    `u 0 = u₀` as one of the defining conditions.

    For the ESS-route NS_WeakSolution (Phase 80+), the initial condition
    should similarly be encoded. Once NS_WeakSolution is formalized with
    an explicit `v 0 = v₀` component, this theorem follows by extracting
    the component from the conjunction.

    LEAN STATUS:
      Depends on the exact Lean structure of NS_WeakSolution.
      Once NS_WeakSolution is defined concretely, this is immediate.
      ETA: 1 week (requires NS_WeakSolution formalization).

    #print axioms NS_WeakSolInitCond_OPEN
    → (does not appear — named open def, NOT axiom) -/
def NS_WeakSolInitCond_OPEN : Prop :=
  ∀ (v₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (v : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)),
    NS_WeakSolution v v₀ →
    v 0 = v₀

/-! ## §II. NS_CarlemanToZeroInit_OPEN — Carleman implies v(0) = 0 a.e. -/

/-- **NS_CarlemanToZeroInit_OPEN** — From Carleman + v(T) = 0, conclude v(0) = 0 a.e.

    MATHEMATICAL CONTENT:

    Given NS_ESSCarlemanBound_OPEN (hCarl) and a weak NS solution v in L^{3,∞}
    with eLpNorm(v T) 2 haar = 0 (v vanishes at T in L²):

    Conclusion: v(0, x) = 0 for almost every x ∈ ℝ³.

    PROOF METHOD (ESS 2003, Section 3-4):

    Step 1: From hv_zero, v(T,x) = 0 a.e. (by eLpNorm = 0 iff a.e. zero).

    Step 2: Approximate v by a sequence {φ_n} of smooth compactly supported
            functions φ_n : [0,T] × ℝ³ → ℝ³ with φ_n(T,·) → 0 in L².

    Step 3: Apply NS_ESSCarlemanBound_OPEN (hCarl) to each φ_n with
            the pseudo-convex weight ψ(x) = -‖x‖² (or log(|x-x₀|⁻¹)):
              τ · ∫ e^{2τψ} |φ_n(T,x)|² dx ≤ C · ∫ e^{2τψ} |φ_n(0,x)|² dx
            For τ ≥ τ₀ fixed, take n → ∞:
              LHS → 0  (since φ_n(T,·) → 0 in L²).
            Therefore: ∫ e^{2τψ} |φ_n(0,x)|² dx → 0.

    Step 4: Since τ can be taken arbitrarily large, and ψ(x) → -∞ only at ∞,
            the sequence {e^{τψ} φ_n(0,·)} → 0 in L². As τ → ∞ with ψ(x) < 0
            for x ≠ 0: e^{τψ(x)} → 0 except at x = 0 → v(0,x) = 0 a.e.

    LEAN STATUS:
      Requires:
        - eLpNorm = 0 → a.e. zero (Mathlib: MeasureTheory.eLpNorm_eq_zero_iff)
        - Smooth compactly supported approximation of v in the L^{3,∞} class
        - Convergence of the Carleman bound in the approximation limit
        - Pseudo-convex weight argument: τ → ∞ forces pointwise zero
      ETA: 2-4 months after NS_ESSCarlemanBound_OPEN is proved.

    #print axioms NS_CarlemanToZeroInit_OPEN
    → (does not appear — named open def, NOT axiom) -/
def NS_CarlemanToZeroInit_OPEN : Prop :=
  NS_ESSCarlemanBound_OPEN →
  ∀ (v : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (T : ℝ), T > 0 →
    (∃ M : ℝ, ∀ t ≥ (0 : ℝ), ∀ α > (0 : ℝ),
      MeasureTheory.Measure.haar
        {x | MeasureTheory.nnnorm (v t x) > ENNReal.ofReal α} ≤
        (ENNReal.ofReal (M / α)) ^ 3) →
    MeasureTheory.eLpNorm (v T) 2 MeasureTheory.Measure.haar = 0 →
    ∀ᵐ x ∂MeasureTheory.Measure.haar, v 0 x = 0

/-! ## §III. NS_ZeroInitToZero_OPEN — zero initial data → zero solution -/

/-- **NS_ZeroInitToZero_OPEN** — NS solution with v₀ = 0 a.e. is identically zero.

    MATHEMATICAL CONTENT:

    If v is a Leray-Hopf weak NS solution with initial data v₀ = 0 a.e., then
      ∀ t ∈ [0, T],  ∀ x,  v(t, x) = 0.

    PROOF METHOD (energy inequality):

    From NS_WeakSolution v v₀ and v₀ = 0 a.e.:

    Step 1: ‖v₀‖_{L²}² = ∫ |v₀(x)|² dx = 0  (since v₀ = 0 a.e.).

    Step 2: Energy inequality for Leray-Hopf:
              ‖v(t)‖_{L²}² ≤ ‖v₀‖_{L²}² = 0  for all t ≥ 0.
            (The energy is non-increasing from the initial data.)

    Step 3: ‖v(t)‖_{L²} = 0 → v(t, x) = 0 for a.e. x (for each t).

    Step 4: For pointwise zero (not just a.e.): need regularity of v.
            Under the L^{3,∞} bound and NS_WeakSolution structure, the solution
            v is locally Hölder continuous (from the Leray-Schauder theory or
            the Serrin regularity criterion), so a.e. zero → pointwise zero.

    NOTE: Step 3 gives the a.e. version immediately from energy.
          Step 4 (pointwise) requires additional regularity.
          If the conclusion is weakened to ∀ᵐ x, v t x = 0, Step 4 is unnecessary.
          The Phase 92 definition uses the pointwise conclusion; we keep it here.

    LEAN STATUS:
      Steps 1-3: energy inequality argument (ETA 1-2 weeks with NS_WeakSolution).
      Step 4: Hölder regularity from L^{3,∞} (ETA 2-4 weeks additional work).

    #print axioms NS_ZeroInitToZero_OPEN
    → (does not appear — named open def, NOT axiom) -/
def NS_ZeroInitToZero_OPEN : Prop :=
  ∀ (v₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (v : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (T : ℝ), T > 0 →
    NS_WeakSolution v v₀ →
    (∀ᵐ x ∂MeasureTheory.Measure.haar, v₀ x = 0) →
    ∀ t ∈ Set.Icc 0 T, ∀ x, v t x = 0

/-! ## §IV. Bridge: NS_ESSBackwardUniq_OPEN from sub-steps (0 sorry) -/

/-- **Phase 94: NS_ESSBackwardUniq_from_subgaps_v2 (0 sorry, classical trio).**

    PROOF CHAIN:

    Given hCarl : NS_ESSCarlemanBound_OPEN, v₀, v, T, hT,
          hWeak : NS_WeakSolution v v₀, hWL3 : L^{3,∞} bound, hVzero : eLpNorm(vT) 2 = 0.

    Step A: v(0) = v₀
            By NS_WeakSolInitCond_OPEN (hInit).

    Step B: v(0, x) = 0 a.e.
            By NS_CarlemanToZeroInit_OPEN (hCarl_to_zero) applied to hCarl.
            This gives: ∀ᵐ x, v 0 x = 0.

    Step C: v₀ = 0 a.e.
            From Step A: v₀ = v 0; from Step B: v 0 = 0 a.e.
            Therefore v₀ = 0 a.e.

    Step D: v ≡ 0 on [0,T]
            By NS_ZeroInitToZero_OPEN (hZero) applied to hWeak and Step C.

    AXIOM FOOTPRINT:
      #print axioms NS_ESSBackwardUniq_from_subgaps_v2
      → {propext, Classical.choice, Quot.sound}

    SORRY COUNT: 0 -/
theorem NS_ESSBackwardUniq_from_subgaps_v2
    (hInit        : NS_WeakSolInitCond_OPEN)
    (hCarl_to_zero : NS_CarlemanToZeroInit_OPEN)
    (hZero        : NS_ZeroInitToZero_OPEN) :
    NS_ESSBackwardUniq_OPEN := by
  intro hCarl v₀ v T hT hWeak hWL3 hVzero t ht x
  -- Step A: v(0) = v₀
  have hv0_eq : v 0 = v₀ := hInit v₀ v hWeak
  -- Step B: v(0, x) = 0 a.e.
  have hv0_ae : ∀ᵐ y ∂MeasureTheory.Measure.haar, v 0 y = 0 :=
    hCarl_to_zero hCarl v T hT hWL3 hVzero
  -- Step C: v₀ = 0 a.e.
  have hv0_zero : ∀ᵐ y ∂MeasureTheory.Measure.haar, v₀ y = 0 := by
    filter_upwards [hv0_ae] with y hy
    rw [← hv0_eq]
    exact hy
  -- Step D: v ≡ 0 on [0,T] by NS_ZeroInitToZero_OPEN
  exact hZero v₀ v T hT hWeak hv0_zero t ht x

/-! ## §V. Phase 94 ledger -/

/-
================================================================
PHASE 94 LEDGER (July 2, 2026)
Opera Numerorum — David Fox (ORCID: 0009-0008-1290-6105)
================================================================

PHASE 94 DECOMPOSES Phase 92's NS_ESSBackwardUniq_OPEN into:

  NS_WeakSolInitCond_OPEN       ETA 1 week
    NS_WeakSolution v v₀ → v 0 = v₀.
    Initial condition extraction (structural, near-term).

  NS_CarlemanToZeroInit_OPEN    ETA 2-4 months (after Carleman)
    NS_ESSCarlemanBound_OPEN → v(T)=0 → v(0)=0 a.e.
    Uses approximation + Carleman limit argument.

  NS_ZeroInitToZero_OPEN        ETA 2-4 weeks
    NS_WeakSolution + v₀=0 a.e. → v≡0 on [0,T].
    Energy inequality + regularity argument.

BRIDGE (0 sorry, classical trio):
  NS_ESSBackwardUniq_from_subgaps_v2
    — 3 sub-steps (Init + Carleman + Energy) → NS_ESSBackwardUniq_OPEN

NEAR-TERM CLOSEABLE (after NS_WeakSolution formalization):
  NS_WeakSolInitCond_OPEN   (ETA 1 week)
  NS_ZeroInitToZero_OPEN    (ETA 2-4 weeks)

SORRY COUNT: 0
AXIOM KEYWORD: 0

REMAINING OPEN DEFS (Phase 91+92+93+94, 7 total):
  1. NS_ESSRescaleNS_OPEN           — PDE rescaling, ETA 2-4 weeks
  2. NS_HaarPreimage_OPEN           — Haar dilation, ETA 1-2 days
  3. NS_BlowupConcentration_OPEN    — Aubin-Lions, ETA 2-3 months
  4. NS_ESSCarlemanBound_OPEN       — Carleman, ETA 6-12 months
  5. NS_WeakSolInitCond_OPEN        — Init cond, ETA 1 week (NEAR TERM)
  6. NS_CarlemanToZeroInit_OPEN     — Carleman → zero at 0, ETA 2-4 mo
  7. NS_ZeroInitToZero_OPEN         — Energy ineq, ETA 2-4 weeks (NEAR TERM)
================================================================
-/

theorem phase94_ledger : True := trivial

end Phase94BackwardUniqSubgaps
end NS
end Towers
end TheoremaAureum
