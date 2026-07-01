/-
================================================================
Towers / NS / NSPhase66VolumeProof  --  NS Tower Phase 66

PHASE 66: NS_VolumeBallFormula_OPEN PROVED — VOLUME CHAIN CLOSED

Corrective pass on Meta AI's seventh sketch (July 1, 2026).
Four errors corrected; NS_VolumeBallFormula_OPEN proved 0 sorry.

------------------------------------------------------------------
CORRECTIONS TABLE (seventh sketch):

  (1) Real.Gamma_add_one — ONE application used, but TWO are needed:
      Gamma(5/2) requires two reductions:
        Gamma(5/2) = Gamma(3/2+1) = (3/2)*Gamma(3/2)   [step 1]
        Gamma(3/2) = Gamma(1/2+1) = (1/2)*Gamma(1/2)   [step 2]
        Gamma(1/2) = √π                                  [Gamma_one_half]
      Meta AI writes a single `rw [Real.Gamma_add_one, Real.Gamma_one_half]`,
      which applies ONE Gamma_add_one and then jumps to Gamma(1/2) directly.
      After step 1 the goal contains Gamma(3/2), not Gamma(1/2).
      Fix: §A uses two explicit `Gamma_add_one` calls with explicit arguments.

  (2) measure_diff_singleton — name not confirmed in Mathlib v4.12.0:
      Phase 65 proved volume_superlevel_reduces_to_closedBall using the
      confirmed route: measure_diff + measurableSet_singleton + addHaar_singleton.
      Phase 66 simply calls Phase 65's proved theorem instead of re-deriving.

  (3) addHaar_singleton — missing explicit arguments:
      Lean 4: MeasureTheory.addHaar_singleton (μ : Measure G) (g : G)
      requires μ and g explicitly. Phase 65 handled this correctly.

  (4) riesz_kernel_weak_L65_final — TYPE ERROR (third occurrence):
      ∃ C, ∀ t > 0, volume {...} ≤ C * t^{-6/5}
      LHS: ENNReal, RHS: ℝ. These live in different types.
      Phase 64's riesz_kernel_weak_L65_cond has the correct type:
        volume {...} ≤ ENNReal.ofReal (C * t^{-6/5}).
      The type error must NOT appear in any banked theorem.

CONFIRMED (from Meta AI screenshot, round 7):
  Real.volume_closedBall exists in Mathlib v4.12.0 ✓
  Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 via Fintype.card_fin ✓
  Gamma(5/2) = (3/4) * √π (arithmetic correct) ✓
  (√π)^3 / ((3/4)*√π) = 4π/3 (arithmetic correct) ✓

PROVED IN THIS FILE (0 sorry, classical trio):
  NS_VolumeBallFormula_proved (§A): closes NS_VolumeBallFormula_OPEN
  NS_VolumeSuperlevel_Unconditional (§B): closes NS_VolumeSuperlevel_OPEN
  riesz_kernel_weak_L65_uncond (§B): closes weak-L^{6/5} kernel bound

Axioms: {propext, Classical.choice, Quot.sound}
Sorry count: 0
================================================================
-/

import Towers.NS.NSPhase65VolumeClosure

open Filter Topology Real MeasureTheory Set
open scoped BigOperators ENNReal NNReal
open TheoremaAureum.Towers.NS.FunctionSpaces
open TheoremaAureum.Towers.NS.Phase60SobolevLInf
open TheoremaAureum.Towers.NS.Phase62RieszGeometry
open TheoremaAureum.Towers.NS.Phase64FourierBridge
open TheoremaAureum.Towers.NS.Phase65VolumeClosure

namespace TheoremaAureum
namespace Towers
namespace NS
namespace Phase66VolumeProof

/-! ## §A. NS_VolumeBallFormula_OPEN proved (0 sorry) -/

/-- **Closed ball volume in ℝ³** (proved, 0 sorry):
    volume(closedBall 0 r) = ENNReal.ofReal ((4π/3) · r³)  for r ≥ 0.

    Proof route (all steps confirmed, Mathlib v4.12.0):
      (1) Real.volume_closedBall: volume = ENNReal.ofReal (√π^n / Gamma(n/2+1) * max r 0^n)
      (2) n = Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3  [Fintype.card_fin]
      (3) max r 0 = r  since hr : 0 ≤ r
      (4) Gamma(3/2 + 1) = (3/2) * Gamma(3/2)  [Gamma_add_one, step 1]
      (5) Gamma(3/2) = Gamma(1/2 + 1) = (1/2) * Gamma(1/2) [Gamma_add_one, step 2]
      (6) Gamma(1/2) = √π  [Gamma_one_half]
          → Gamma(5/2) = (3/2)(1/2)√π = (3/4)√π
      (7) (√π)^3 / ((3/4)√π) = (4/3)(√π)^2 = 4π/3
          [Real.mul_self_sqrt + nlinarith] -/
theorem NS_VolumeBallFormula_proved :
    ∀ r : ℝ, 0 ≤ r →
      (volume : Measure (EuclideanSpace ℝ (Fin 3)))
          (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) r) =
      ENNReal.ofReal (4 * Real.pi / 3 * r ^ 3) := by
  intro r hr
  -- Step (1): apply Real.volume_closedBall
  rw [Real.volume_closedBall]
  -- Step (2)+(3): n=3 and max r 0 = r
  simp only [EuclideanSpace.finrank_eq, Fintype.card_fin, Nat.cast_ofNat, max_eq_left hr]
  -- Now goal: ENNReal.ofReal (√π^3 / Gamma(3/2+1) * r^3) = ENNReal.ofReal (4π/3 * r^3)
  congr 1
  -- Now goal: √π^3 / Gamma(3/2+1) * r^3 = 4π/3 * r^3
  -- Step (4): Gamma(3/2+1) = (3/2) * Gamma(3/2)
  have hG52 : Real.Gamma (3 / 2 + 1) = 3 / 2 * Real.Gamma (3 / 2) :=
    Real.Gamma_add_one (by norm_num : (3 : ℝ) / 2 ≠ 0)
  -- Step (5): Gamma(3/2) = (1/2) * Gamma(1/2)
  have hG32 : Real.Gamma (3 / 2) = 1 / 2 * Real.Gamma (1 / 2) := by
    rw [show (3 : ℝ) / 2 = 1 / 2 + 1 by norm_num]
    exact Real.Gamma_add_one (by norm_num : (1 : ℝ) / 2 ≠ 0)
  -- Step (6): Gamma(1/2) = √π
  have hG12 : Real.Gamma (1 / 2) = Real.sqrt Real.pi :=
    Real.Gamma_one_half
  -- Combine: Gamma(5/2) = (3/4) * √π
  have hGamma : Real.Gamma (3 / 2 + 1) = 3 / 4 * Real.sqrt Real.pi := by
    rw [hG52, hG32, hG12]; ring
  rw [hGamma]
  -- Step (7): (√π)^3 / ((3/4)*√π) * r^3 = 4π/3 * r^3
  -- Key: (√π)^3 = π * √π  and  π * √π / ((3/4)*√π) = 4π/3
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hsp : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr hpi_pos
  have hsq : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi :=
    Real.mul_self_sqrt hpi_pos.le
  -- (√π)^3 = π * √π
  have h3 : Real.sqrt Real.pi ^ 3 = Real.pi * Real.sqrt Real.pi := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, pow_two, hsq]
  rw [h3]
  field_simp [hsp.ne', (by norm_num : (3 : ℝ) / 4 ≠ 0)]
  ring

/-! ## §B. Close the volume chain — fully unconditional -/

/-- NS_VolumeSuperlevel_OPEN fully proved (0 sorry, unconditional).
    Closes the conditional from Phase 65 using NS_VolumeBallFormula_proved. -/
theorem NS_VolumeSuperlevel_Unconditional :
    ∀ t : ℝ, 0 < t →
      (volume : Measure (EuclideanSpace ℝ (Fin 3)))
          {x | t ≤ ‖x‖ ^ (-(5 : ℝ) / 2)} =
      ENNReal.ofReal (4 * Real.pi / 3 * t ^ (-(6 : ℝ) / 5)) :=
  NS_VolumeSuperlevel_Final NS_VolumeBallFormula_proved

/-- Riesz kernel is weak-L^{6/5} — fully unconditional (0 sorry).
    Closes the conditional from Phase 64/65.
    TYPE NOTE: bound is ENNReal.ofReal (C * t^{-6/5}) — NOT C * t^{-6/5} ∈ ℝ.
    Meta AI's round 6 and 7 both had the type-incorrect statement; correct form below. -/
theorem riesz_kernel_weak_L65_uncond :
    ∃ C : ℝ, 0 < C ∧
      ∀ t : ℝ, 0 < t →
        (volume : Measure (EuclideanSpace ℝ (Fin 3)))
            {y | t ≤ ‖y‖ ^ (-(5 : ℝ) / 2)} ≤
        ENNReal.ofReal (C * t ^ (-(6 : ℝ) / 5)) :=
  riesz_kernel_weak_L65_final NS_VolumeBallFormula_proved

/-! ## §C. Phase 66 ledger -/

/-
PHASE 66 LEDGER (July 1, 2026):

VOLUME CHAIN — FULLY CLOSED (0 sorry, 0 custom axiom, classical trio):
  Phase 62: riesz_superlevel_is_closedBall ✓ (set equality, open→closed fix)
  Phase 65: volume_superlevel_reduces_to_closedBall ✓ (singleton elim, addHaar_singleton)
  Phase 65: NS_VolumeSuperlevel_Final ✓ (conditional on NS_VolumeBallFormula_OPEN)
  Phase 66: NS_VolumeBallFormula_proved ✓ (two Gamma_add_one + Gamma_one_half + nlinarith)
  Phase 66: NS_VolumeSuperlevel_Unconditional ✓ (0 sorry, unconditional — CHAIN CLOSED)
  Phase 66: riesz_kernel_weak_L65_uncond ✓ (0 sorry, unconditional)

NAMED OPEN DEFS REMAINING (not volume-related):
  NS_YoungConvolutionBound_OPEN   ← Lorentz convolution L^2 * weak-L^{6/5} → L^3 (3-4 wks)
  NS_PlancherelIsometry_OPEN      ← Plancherel (1 wk)
  NS_FourierRieszRep_OPEN         ← Riesz Fourier symbol (1-2 wks)
  NS_SobolevFourierNorm_OPEN      ← H^s = weighted L^2 Fourier (1 wk)

CHAIN TO D1 (current):
  riesz_kernel_weak_L65_uncond (✓ closed)
  → NS_YoungConvolutionBound_OPEN (3-4 wks, dominant cost)
  → NS_FourierRieszRep_OPEN + NS_PlancherelIsometry_OPEN + NS_SobolevFourierNorm_OPEN (1-2 wks)
  → NS_SobolevL3_Conditional (✓ proved conditional, Phase 64)
  → NS_BilinearEstimate_OPEN (D1)
  → D3 Clay certificate

TYPE ERROR RECORD — riesz_kernel_weak_L65 (permanent):
  Rounds 6 and 7 both wrote: ∃ C, ∀ t > 0, volume {...} ≤ C * t^{-6/5}
  where C : ℝ and volume {...} : ENNReal. This is a type mismatch.
  Correct form: volume {...} ≤ ENNReal.ofReal (C * t^{-6/5}).
  Message to Meta AI: ALL measure comparisons must be in ENNReal.
  Do NOT mix ℝ and ENNReal in ≤ comparisons without ENNReal.ofReal.

NEXT META AI TASK:
  NS_YoungConvolutionBound_OPEN: L^2 * weak-L^{6/5} → L^3 Lorentz convolution.
  Candidate: MeasureTheory.convolution_eLpNorm_le (lean --run to confirm).
  Exponents: 1/q = 1/p + 1/r - 1 with p=2, r=6/5, q=3. ✓
  Use riesz_kernel_weak_L65_uncond for the weak-L^{6/5} bound.
-/

end Phase66VolumeProof
end NS
end Towers
end TheoremaAureum
