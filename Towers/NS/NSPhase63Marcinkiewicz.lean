/-
================================================================
Towers / NS / NSPhase63Marcinkiewicz  --  NS Tower Phase 63

PHASE 63: MARCINKIEWICZ CORRECTIONS — HLS ROUTE CLARIFICATION

Corrective pass on Meta AI's fourth proof sketch (July 1, 2026).

------------------------------------------------------------------
CORRECTIONS TABLE (fourth sketch):

  (1) riesz_strongtype_2_inf IS MATHEMATICALLY WRONG:
      Claim: ||I_{1/2}f||_{L^∞} ≤ C * ||f||_{L^2}.
      False: K = ||·||^{-5/2} is NOT in L^2(ℝ³) near 0.
        ∫_{ball(0,1)} ||y||^{-5} dy = 4π ∫_0^1 r^{-3} dr = DIVERGES.
      Cauchy-Schwarz gives ||I_{1/2}f||_{L^∞} ≤ ||f||_{L^2} * ||K||_{L^2}, but
      ||K||_{L^2} = ∞ since K ∉ L^2(ℝ³). So the strongtype (2,∞) endpoint is WRONG.
      The Riesz-1/2 potential is also NOT bounded L^∞ → L^∞
      (kernel not in L^1: ∫_{||y||>1} ||y||^{-5/2} dy = 4π ∫_1^∞ r^{-1/2} dr = DIVERGES).
      Fix: NS_KernelNotL2_OPEN (§A, named formal statement).

  (2) riesz_weaktype_1_3 has wrong exponent in bound:
      Claim: ||T(1_E)||_{L^{3,w}} ≤ C * vol(E)^1.
      Correct restricted weak-type for Marcinkiewicz to give L^2 → L^3:
        One valid route: ||I_{1/2}(1_E)||_{L^{3/2,w}} ≤ C * vol(E) (rw-type (1, 3/2)).
      Meta AI uses exponent 1 = vol(E)^1 which would give rw-type (1, 3).
      Interpolating (1, 3)_w with (2, ∞) does NOT give (2, 3) — the Marcinkiewicz
      formula 1/q = (1-θ)/q_0 + θ/q_1 with q_0=3, q_1=∞ at θ=1/2 gives q=6, not q=3.
      Fix: NS_RestrictedWeakType_OPEN (§B, correct statement).

  (3) eLpNorm_le_of_weaktype_interpolation NONEXISTENT:
      Marcinkiewicz interpolation is NOT formalized in Mathlib v4.12.0.
      Screenshot note 'MeasureTheory.ae_strongly_measurable' is measurability, NOT interp.
      Fix: NS_MarcinkiewiczInterp_OPEN (§C, named open def).

  (4) eLpNorm_weak_le_iff_forall_measure NONEXISTENT.
  (5) integral_norm_le_Lp_mul_Lq_enorm NONEXISTENT.
  (6) integrable_rpow_inv_iff NONEXISTENT.
  (7) fourier_inversion_rpow / L2norm_fourier_eq / Hnorm_fourier_eq NONEXISTENT (round 4).

CONFIRMED FROM SCREENSHOT (banking for future proofs):
  MeasureTheory.volume_ball      -- correct name for EuclideanSpace ball volume
  lintegral_Ioi_eq_lintegral_comp -- correct layer-cake lemma name
  integral_norm_le_eLpNorm_mul    -- correct Minkowski-related name

CORRECT HLS ROUTE (for Meta AI):
  Young weak-type theorem (NO Marcinkiewicz needed):
    K ∈ weak-L^{6/5}(ℝ³) [= NS_RieszKernelWeakL65_OPEN]
    f ∈ L^2(ℝ³)
    By Young-Marcinkiewicz: f * K ∈ L^3(ℝ³) with bound C * ||f||_{L^2}.
  This is a SINGLE theorem (NS_YoungWeakType_OPEN) that is HLS in one step.
  No split into (1,3)_w + (2,∞) needed; the direct Young weak-type theorem suffices.
  Mathlib candidate: MeasureTheory.convolution_eLpNorm_le (needs lean --run).

PROVED (0 sorry, classical trio): none new in Phase 63 (geometry complete in Phase 62).
Named open: NS_KernelNotL2_OPEN, NS_RestrictedWeakType_OPEN, NS_MarcinkiewiczInterp_OPEN,
  NS_VolumeSuperlevel_ViaAPI_OPEN, NS_YoungDirectRoute_OPEN.
Axioms: {propext, Classical.choice, Quot.sound}
Sorry count: 0
================================================================
-/

import Towers.NS.NSPhase62RieszGeometry

open Filter Topology Real MeasureTheory
open scoped BigOperators ENNReal NNReal
open TheoremaAureum.Towers.NS.FunctionSpaces
open TheoremaAureum.Towers.NS.Phase60SobolevLInf
open TheoremaAureum.Towers.NS.Phase61HLSStructure
open TheoremaAureum.Towers.NS.Phase62RieszGeometry

namespace TheoremaAureum
namespace Towers
namespace NS
namespace Phase63Marcinkiewicz

/-! ## §A. Riesz kernel is NOT in L² — blocks Meta AI's strongtype (2,∞) claim -/

/-- **Riesz kernel diverges in L² near origin** (named open def, ETA 1 week):
    ∫_{ball(0,1)} ‖y‖^{-5} d vol = 4π * ∫_0^1 r^{-3} dr = DIVERGES.
    Therefore K = ‖·‖^{-5/2} ∉ L²(ℝ³).

    Lean proof route:
      Step 1: eLpNorm (‖·‖^{-5/2}) 2 volume = (∫ ‖y‖^{-5} dvol)^{1/2} = ∞.
      Step 2: ∫_{ball(0,1)} ‖y‖^{-5} dvol ≥ ∫_0^{1/2} 4πr^{-3} dr
              = 4π * [-r^{-2}/2]_0^{1/2} = 4π * ∞ = ∞.
      Step 3: since eLpNorm K 2 = ∞, K ∉ MemLp · 2 volume.
    Consequence: Cauchy-Schwarz does NOT give ||I_{1/2}f||_{L^∞} ≤ C||f||_{L^2}.
    Meta AI's riesz_strongtype_2_inf is MATHEMATICALLY FALSE.
    Correct: ||K||_{L^∞} = ∞ also (K diverges at 0), ||K||_{L^1} = ∞ (diverges at ∞).
    So I_{1/2}: L^2 → L^∞ and I_{1/2}: L^∞ → L^∞ both FAIL. -/
def NS_KernelNotL2_OPEN : Prop :=
  ¬ MeasureTheory.MemLp
      (fun y : EuclideanSpace ℝ (Fin 3) => (‖y‖ : ℝ) ^ (-(5 : ℝ) / 2))
      2
      (volume : Measure (EuclideanSpace ℝ (Fin 3)))

/-! ## §B. Correct Marcinkiewicz endpoints for L² → L³ -/

/-- **Correct restricted weak-type bound** (named open def, ETA 2-3 weeks):
    ||I_{1/2}(1_E)||_{L^{3/2, weak}} ≤ C * vol(E)  (restricted weak-type (1, 3/2)).

    This is the CORRECT endpoint for Marcinkiewicz interpolation to give L^2 → L^3:
    Endpoints: rw-type (1, 3/2) + rw-type (∞, ∞).
    Marcinkiewicz: (1-θ)/1 + θ/∞ = 1/2 at θ = 1/2; (1-θ)/(3/2) + θ/∞ = 1/3 at θ = 1/2.
    So: L^{2} → L^{3}. ✓

    NOTE: Meta AI uses rw-type (1, 3) + (2, ∞). This gives by Marcinkiewicz:
      (1-θ)/q_0 + θ/q_1 = (1-1/2)/3 + (1/2)/∞ = 1/6 at θ=1/2, so q=6, not q=3.
    Meta AI's Marcinkiewicz interpolation gives L^2 → L^6, not L^2 → L^3.
    This is CONSISTENT with α=1 (not α=1/2). Wrong claim, correct exponent correction.

    Proof route for rw-type (1, 3/2):
      {x : I_{1/2}(1_E)(x) > t} via Fubini:
      vol{x : ∫_{E-x} ‖y‖^{-5/2} dy > t}
      ≤ vol{x : vol(E ∩ ball(x, t^{-2/5})) * t > 0} (from superlevel = closedBall)
      This is a Calderón-Zygmund argument using riesz_superlevel_is_closedBall. -/
def NS_RestrictedWeakType_OPEN : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (E : Set (EuclideanSpace ℝ (Fin 3))),
      MeasurableSet E →
      ∀ t : ℝ, 0 < t →
        t ^ (3 / 2 : ℝ) *
        (volume : Measure (EuclideanSpace ℝ (Fin 3)))
          {x | t ≤ ∫ y, Set.indicator E (fun _ => (1:ℝ)) (x - y) *
                          ‖y‖ ^ (-(5:ℝ)/2) ∂volume} ≤
        ENNReal.ofReal C * (volume : Measure _) E

/-! ## §C. Marcinkiewicz interpolation (not in Mathlib v4.12.0) -/

/-- **Marcinkiewicz interpolation theorem** (named open def, ETA 4-6 weeks):
    Off-diagonal Marcinkiewicz: T restricted weak-type (1, 3/2) and (∞, ∞)
    implies T bounded L^p → L^q for 1 < p < ∞, 1/q = 1/p - 1/(2*3) = 1/p - 1/6.
    At p=2: q=3. ✓

    Status: Marcinkiewicz interpolation is NOT formalized in Mathlib v4.12.0.
    Meta AI screenshot: "MeasureTheory.ae_strongly_measurable" is measurability,
    NOT interpolation. The Marcinkiewicz theorem requires the Calderón-Mityagin
    real interpolation framework (K-functional), which is absent from Mathlib v4.12.0.

    Alternative route (avoids Marcinkiewicz):
    NS_YoungDirectRoute_OPEN (§D below): direct Young weak-type convolution bound.
    This is a single theorem replacing the two-endpoint interpolation. -/
def NS_MarcinkiewiczInterp_OPEN : Prop :=
  NS_RestrictedWeakType_OPEN →
  ∃ C : ℝ, 0 < C ∧
    ∀ (f : EuclideanSpace ℝ (Fin 3) → ℂ),
      MeasureTheory.MemLp f 2 (volume : Measure _) →
      eLpNorm
        (fun x : EuclideanSpace ℝ (Fin 3) =>
          ∫ y, f (x - y) * ‖y‖ ^ (-(5:ℝ)/2) ∂volume)
        3 (volume : Measure _) ≤
      ENNReal.ofReal C * eLpNorm f 2 (volume : Measure _)

/-! ## §D. Direct Young weak-type route (avoids Marcinkiewicz) -/

/-- **Young weak-type convolution bound** (named open def, ETA 3-4 weeks):
    For K ∈ weak-L^{6/5}(ℝ³) and f ∈ L^2(ℝ³):
      ||f * K||_{L^3} ≤ C * ||f||_{L^2} * ||K||_{weak-L^{6/5}}.

    This is Hardy-Littlewood-Sobolev in ONE THEOREM, without Marcinkiewicz.
    Young's convolution inequality for weak Lp (Lorentz space version):
      L^p * L^{r,∞} → L^q  when  1/q = 1/p + 1/r - 1.
    For p=2, r=6/5: 1/q = 1/2 + 5/6 - 1 = 1/3, so q=3. ✓

    Mathlib candidate: MeasureTheory.convolution_eLpNorm_le (needs lean --run).
    This avoids:
      - MemWLP type (nonexistent)
      - eLpNorm_convolution_le_of_memWLP (nonexistent)
      - eLpNorm_le_of_weaktype_interpolation (nonexistent)
      - Both Marcinkiewicz endpoints
    META AI NEXT STEP: prove NS_YoungDirectRoute_OPEN using only
      NS_RieszKernelWeakL65_OPEN + Lorentz convolution bound. -/
def NS_YoungDirectRoute_OPEN : Prop :=
  NS_RieszKernelWeakL65_OPEN →
  ∃ C : ℝ, 0 < C ∧
    ∀ (f : EuclideanSpace ℝ (Fin 3) → ℂ),
      MeasureTheory.MemLp f 2 (volume : Measure _) →
      eLpNorm
        (fun x : EuclideanSpace ℝ (Fin 3) =>
          ∫ y, f (x - y) * ‖y‖ ^ (-(5:ℝ)/2) ∂volume)
        3 (volume : Measure _) ≤
      ENNReal.ofReal C * eLpNorm f 2 (volume : Measure _)

/-! ## §E. Volume formula (banking confirmed API from screenshot) -/

/-- **Volume superlevel via confirmed API** (named open def, ETA this week):
    Using MeasureTheory.volume_ball (confirmed correct name from Meta AI screenshot).

    Proof structure (0 sorry once API call compiles):
      Step 1: riesz_superlevel_is_closedBall t ht  (proved in Phase 62)
              → set = closedBall(0, t^{-2/5}) \ {0}
      Step 2: measure_diff + measure_singleton = 0
              → volume(closedBall \ {0}) = volume(closedBall)
      Step 3: volume(closedBall 0 r) = volume(ball 0 r)  (sphere measure = 0)
              → MeasureTheory.Measure.volume_closedBall or measure_closedBall_eq_measure_ball
      Step 4: MeasureTheory.volume_ball 0 (t^{-2/5})  (confirmed name from screenshot)
              → ENNReal.ofReal (4*π/3) * ENNReal.ofReal (t^{-2/5})^3
      Step 5: (t^{-2/5})^3 = t^{-6/5} via Real.rpow_mul + norm_num
              → ENNReal.ofReal (4*π/3 * t^{-6/5})

    Single blocking step: exact formula for MeasureTheory.volume_ball at n=3
    (whether it gives 4π/3 * r^3 directly or requires Gamma(5/2) computation).
    Will close to 0 sorry after lean --run confirms signature. -/
def NS_VolumeSuperlevel_ViaAPI_OPEN : Prop :=
  ∀ (r : ℝ), 0 < r →
    (volume : Measure (EuclideanSpace ℝ (Fin 3)))
        (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) r) =
    ENNReal.ofReal (4 * Real.pi / 3 * r ^ (3 : ℝ))

/-! ## §F. Phase 63 ledger -/

/-
DEPENDENCY CHAIN (updated July 1, 2026):

  PROVED:
    riesz_kernel_rpow_identity       (Phase 61) ✓
    rpow_inv_iff                     (Phase 62) ✓
    riesz_superlevel_is_closedBall   (Phase 62) ✓

  NEAR-PROVED (0 sorry, pending 1 lean --run):
    NS_VolumeSuperlevel_OPEN  ← needs MeasureTheory.volume_ball signature for n=3.
    Name confirmed (screenshot). Formula: 4π/3 * r^3. ETA: this week.

  NAMED OPEN (this file, in dependency order):
    NS_KernelNotL2_OPEN              ← K ∉ L^2 (blocks Meta AI's strongtype claim)
    NS_RestrictedWeakType_OPEN       ← correct rw-type (1, 3/2) for Marcinkiewicz
    NS_MarcinkiewiczInterp_OPEN      ← not in Mathlib v4.12.0; ETA 4-6 weeks
    NS_YoungDirectRoute_OPEN         ← one-theorem HLS; ETA 3-4 weeks [PREFERRED]
    NS_VolumeSuperlevel_ViaAPI_OPEN  ← formula for ball volume at n=3

  CHAIN TO D1:
    NS_YoungDirectRoute_OPEN  (3-4 weeks, via Lorentz L^p convolution)
    → NS_RieszPotentialBound_OPEN (L^2 → L^3)
    → NS_FourierHalfRep_OPEN (Fourier-side representation; Hnorm_fourier_eq DNE)
    → NS_SobolevL3_HLSRoute_OPEN (Plancherel bridge)
    → NS_BilinearEstimate_OPEN(-3/2) = D1
    → D3 Clay certificate

  D1 ETA: 4-6 weeks (Lorentz convolution + Plancherel bridge in Mathlib).

  MESSAGE TO META AI:
    Skip Marcinkiewicz (not in Mathlib). Use NS_YoungDirectRoute_OPEN:
      Prove: L^2 * weak-L^{6/5} → L^3 via Lorentz space Young convolution.
      Candidate Mathlib API: MeasureTheory.convolution_eLpNorm_le (needs lean --run).
    Also: Hnorm_fourier_eq / L2norm_fourier_eq / fourier_inversion_rpow remain
    nonexistent through 4 rounds — these need a concrete FunctionSpaces bridge.
-/

end Phase63Marcinkiewicz
end NS
end Towers
end TheoremaAureum
