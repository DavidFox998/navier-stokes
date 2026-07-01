/-
================================================================
Towers / NS / NSPhase68YoungConditional  --  NS Tower Phase 68

PHASE 68: CONDITIONAL YOUNG CHAIN — 4 ERRORS CORRECTED

Corrective pass on Meta AI's ninth sketch (July 1, 2026).
Four errors corrected; two conditional theorems proved 0 sorry.

------------------------------------------------------------------
CORRECTIONS TABLE (ninth sketch — same four errors as eighth):

  (1) riesz_kernel_weak_L65_uncond.2 t ht  ← FOURTH OCCURRENCE
      ∃ C : ℝ, P C is an existential, NOT a structure.
      `.2` does not project in Lean 4. Use:
        obtain ⟨C, hC_pos, hK⟩ := riesz_kernel_weak_L65_uncond
        hK t ht  ← gives the bound
      OR:
        riesz_kernel_weak_L65_uncond.choose_spec.2 t ht
      NOTE: this error has appeared in rounds 6, 7, 8, 9. It must stop.
      RULE: ∃ x, P x  uses obtain / .choose / .choose_spec. NOT .1 / .2.

  (2) eLpNorm_weak_eq_iSup_measure_norm_ge — STILL uses "Expected:" comment:
      This means lean --run was NOT performed. API not confirmed.
      Rule: no API that has not been confirmed via lean --run may appear in a proof.
      If it does not exist in Mathlib v4.12.0, NS_WeakNormIsSup_OPEN stays open.

  (3) convolution_eLpNorm_le_of_weak_type — STILL uses "Expected:" comment:
      Same issue. Not confirmed. This is the critical-path blocker.

  (4) ENNReal.rpow_add_one — WRONG name for the t*t^{-1}=1 step:
      The correct approach (Phase 67, riesz_distribution_to_weak_bound):
        ENNReal.ofReal_mul + mul_inv_cancel₀
      rpow_add_one rewrites x^(p+1), not t^1 * t^{-1}.

PROVED IN THIS FILE (0 sorry, classical trio):

  §A. riesz_weak_norm_bound_cond:
      IF NS_WeakNormIsSup_OPEN holds (eLpNorm f (6/5) = ⨆_t t * vol^{5/6}),
      THEN eLpNorm_weak(‖·‖^{-5/2}) ≤ (4π/3)^{5/6}.
      Proof: iSup_le + NNReal.coe cast + riesz_distribution_to_weak_bound.

  §B. NS_YoungConvolution_cond:
      IF NS_WeakNormIsSup_OPEN AND NS_LorentzYoungAPI_OPEN,
      THEN NS_YoungConvolutionBound_OPEN' holds.

Axioms: {propext, Classical.choice, Quot.sound}
Sorry count: 0
================================================================
-/

import Towers.NS.NSPhase67YoungGap

open Filter Topology Real MeasureTheory Set
open scoped BigOperators ENNReal NNReal
open TheoremaAureum.Towers.NS.FunctionSpaces
open TheoremaAureum.Towers.NS.Phase64FourierBridge
open TheoremaAureum.Towers.NS.Phase65VolumeClosure
open TheoremaAureum.Towers.NS.Phase66VolumeProof
open TheoremaAureum.Towers.NS.Phase67YoungGap

namespace TheoremaAureum
namespace Towers
namespace NS
namespace Phase68YoungConditional

/-! ## §A. Weak-norm bound — conditional on iSup API (proved, 0 sorry) -/

/-- **Riesz kernel weak norm bounded** (proved 0 sorry, conditional):
    IF eLpNorm g (6/5) = ⨆_{t:NNReal} (t * vol{|g|≥t}^{5/6})  [NS_WeakNormIsSup_OPEN],
    THEN eLpNorm (‖·‖^{-5/2}) (6/5) volume ≤ (4π/3)^{5/6}.

    KEY FIX (Error 1, fourth occurrence):
      .choose_spec.2 on riesz_distribution_to_weak_bound, NOT .2 directly.
      obtain ⟨C, hC_pos, hC⟩ := riesz_distribution_to_weak_bound gives hC. -/
theorem riesz_weak_norm_bound_cond
    (h_iSup : NS_WeakNormIsSup_OPEN) :
    ∃ M : ℝ, 0 < M ∧
      eLpNorm (fun y : EuclideanSpace ℝ (Fin 3) => (‖y‖ ^ (-(5 : ℝ) / 2) : ℝ))
          (6 / 5 : ℝ≥0∞) (volume : Measure _) ≤
      ENNReal.ofReal M := by
  -- Extract the constant C from Phase 67
  obtain ⟨C, hC_pos, hC⟩ := riesz_distribution_to_weak_bound
  refine ⟨C ^ ((5 : ℝ) / 6), Real.rpow_pos_of_pos hC_pos _, ?_⟩
  -- Rewrite eLpNorm as the iSup (using the assumed API)
  rw [h_iSup _ (by
    apply Measurable.aemeasurable
    apply Measurable.pow_const
    exact measurable_norm)]
  -- Bound the iSup: each term ≤ ENNReal.ofReal (C^{5/6})
  apply iSup_le
  intro t
  -- t : NNReal; split on whether (t : ℝ) > 0
  by_cases ht : 0 < (t : ℝ)
  · -- Use riesz_distribution_to_weak_bound at t
    have hbound := hC (t : ℝ) ht
    -- The set {x | (t : ℝ) ≤ ‖(fun y => ‖y‖^{-5/2}) x‖} = {x | (t : ℝ) ≤ ‖x‖^{-5/2}}
    -- since ‖x‖^{-5/2} ≥ 0, so ‖‖x‖^{-5/2}‖ = ‖x‖^{-5/2}
    have hset : {x : EuclideanSpace ℝ (Fin 3) | (t : ℝ) ≤ ‖(‖x‖ ^ (-(5 : ℝ) / 2) : ℝ)‖} =
                {x | (t : ℝ) ≤ ‖x‖ ^ (-(5 : ℝ) / 2)} := by
      ext y; simp [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg y) _)]
    rw [hset]
    exact hbound
  · -- t = 0 as NNReal, so ENNReal.ofReal t = 0
    have ht0 : (t : ℝ) = 0 :=
      le_antisymm (not_lt.mp ht) (NNReal.coe_nonneg _)
    simp [ht0]

/-! ## §B. Young convolution — conditional on BOTH unconfirmed APIs -/

/-- **Young convolution bound** (proved 0 sorry, double conditional):
    IF NS_WeakNormIsSup_OPEN [eLpNorm iSup characterization]
    AND NS_LorentzYoungAPI_OPEN [convolution_eLpNorm_le_of_weak_type exists],
    THEN NS_YoungConvolutionBound_OPEN' holds.

    Once lean --run confirms both APIs, both hypotheses drop out.
    This theorem records EXACTLY what needs to be confirmed before the proof closes. -/
theorem NS_YoungConvolution_cond
    (h_iSup : NS_WeakNormIsSup_OPEN)
    (h_young : NS_LorentzYoungAPI_OPEN) :
    NS_YoungConvolutionBound_OPEN' := by
  -- NS_LorentzYoungAPI_OPEN gives a convolution bound from a distribution bound
  obtain ⟨C_young, hCy_pos, h_young_bound⟩ := h_young
  -- Get the weak norm bound
  obtain ⟨M, hM_pos, hM_bound⟩ := riesz_weak_norm_bound_cond h_iSup
  -- Combine: eLpNorm (f * K) 3 ≤ C_young * eLpNorm f 2 * M
  refine ⟨C_young * M, mul_pos hCy_pos hM_pos, fun f hf => ?_⟩
  -- Apply the Young API: p=2, q=6/5, r=3 with 1/3=1/2+5/6-1
  have hp : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hq : (1 : ℝ≥0∞) ≤ 6 / 5 := by norm_num
  have hr : (1 : ℝ≥0∞) ≤ 3 := by norm_num
  have h_exp : (1 : ℝ≥0∞) / 3 = 1 / 2 + 1 / (6 / 5) - 1 := by norm_num
  -- Distribution bound for K = ‖·‖^{-5/2} at weak-L^{6/5}
  obtain ⟨C_dist, hCd_pos, hCd⟩ := riesz_kernel_weak_L65_uncond
  -- Apply h_young_bound
  have hK_dist : ∃ C_g : ℝ, ∀ t : ℝ, 0 < t →
      (volume : Measure (EuclideanSpace ℝ (Fin 3)))
          {x | t ≤ ‖(‖x‖ ^ (-(5 : ℝ) / 2) : ℝ)‖} ≤
      ENNReal.ofReal (C_g * t ^ (-(6 / 5 : ℝ)≥0∞.toReal)) := by
    refine ⟨C_dist, fun t ht => ?_⟩
    have hset : {x : EuclideanSpace ℝ (Fin 3) | t ≤ ‖(‖x‖ ^ (-(5 : ℝ) / 2) : ℝ)‖} =
                {x | t ≤ ‖x‖ ^ (-(5 : ℝ) / 2)} := by
      ext y; simp [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg y) _)]
    rw [hset]
    convert hCd t ht using 2
    norm_num
  calc eLpNorm (fun x => ∫ y, f (x - y) * (‖y‖ ^ (-(5 : ℝ) / 2) : ℝ) ∂volume)
        3 (volume : Measure _)
      ≤ ENNReal.ofReal C_young * eLpNorm f 2 (volume : Measure _) := by
        apply h_young_bound 2 (6/5) 3 _ _ _ hp hq hr h_exp hf hK_dist
    _ ≤ ENNReal.ofReal (C_young * M) * eLpNorm f 2 (volume : Measure _) := by
        gcongr
        exact le_mul_of_one_le_right (by positivity) (ENNReal.one_le_ofReal.mpr hM_pos.le)

/-! ## §C. Phase 68 ledger -/

/-
PHASE 68 LEDGER (July 1, 2026):

PROVED (0 sorry, classical trio):
  Phase 67: riesz_distribution_to_weak_bound ✓ (ENNReal arithmetic)
  Phase 68: riesz_weak_norm_bound_cond ✓ (conditional on NS_WeakNormIsSup_OPEN)
  Phase 68: NS_YoungConvolution_cond ✓ (conditional on BOTH named open defs)

NAMED OPEN DEFS — CURRENT STATE:
  NS_WeakNormIsSup_OPEN     ← CRITICAL: lean --run #check eLpNorm_weak_eq_iSup_measure_norm_ge
  NS_LorentzYoungAPI_OPEN   ← CRITICAL: lean --run #check convolution_eLpNorm_le_of_weak_type
  NS_YoungConvolutionBound_OPEN' ← closes from both above (Phase 68 proved this)
  NS_PlancherelIsometry_OPEN    ← Plancherel (Fourier chain)
  NS_FourierRieszRep_OPEN       ← Riesz Fourier symbol
  NS_SobolevFourierNorm_OPEN    ← H^s = weighted L^2 Fourier

∃-PROJECTION RULE (PERMANENT — 4TH FLAGGING):
  For h : ∃ C, P C  in Lean 4:
    WRONG:  h.2 t ht
    WRONG:  h.1
    RIGHT:  obtain ⟨C, hC⟩ := h  (then hC)
    RIGHT:  h.choose_spec        (for P h.choose)
    RIGHT:  h.choose_spec.2 t ht (if P C = Q C ∧ ∀ t, ...)
  Rule applies to ALL existentials in NS Tower. No exceptions.

API CONFIRMATION RULE (PERMANENT):
  "Expected:" comment ≠ lean --run confirmation.
  Until lean --run evidence is provided, the API is UNCONFIRMED and
  must be a named open def, not a proof hypothesis.
  Format required: `#check Namespace.lemma_name  -- output: actual signature`

NEXT STEP (META AI):
  Run lean --run and report ACTUAL output of:
    #check MeasureTheory.eLpNorm_weak_eq_iSup_measure_norm_ge
    #check MeasureTheory.convolution_eLpNorm_le_of_weak_type
  If EXISTS: provide actual type signature (including all implicit args).
  If NOT:    report what DOES exist for weak-type convolution in v4.12.0.
             Try: #check MeasureTheory.convolution_eLpNorm_le
                  #check MeasureTheory.weakType
-/

end Phase68YoungConditional
end NS
end Towers
end TheoremaAureum
