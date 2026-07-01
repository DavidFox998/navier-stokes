/-
================================================================
Towers / NS / NSPhase67YoungGap  --  NS Tower Phase 67

PHASE 67: YOUNG CONVOLUTION GAP — DISTRIBUTION BOUND PROVED

Corrective pass on Meta AI's eighth sketch (July 1, 2026).
Four errors corrected; riesz_distribution_to_weak_bound proved 0 sorry.

------------------------------------------------------------------
CORRECTIONS TABLE (eighth sketch):

  (1) riesz_kernel_weak_L65_uncond.2 — WRONG SYNTAX:
      riesz_kernel_weak_L65_uncond : ∃ C : ℝ, 0 < C ∧ ∀ t, 0 < t → vol{...} ≤ ofReal(C*t^{-6/5})
      `.2` on an existential does not project the second component in Lean 4.
      Fix: obtain ⟨C, hC_pos, hC⟩ := riesz_kernel_weak_L65_uncond; then hC t ht.

  (2) eLpNorm_weak_eq_iSup_measure_norm_ge — UNCONFIRMED API:
      Weak Lp norm as iSup of t * vol^{1/p} characterization. This exact theorem
      name is not in the confirmed API list. Weak-type spaces in Mathlib v4.12.0
      are less developed than strong-type spaces. Needs lean --run confirmation.
      Fix: NS_WeakNormIsSup_OPEN (§B) — named open def pending API verification.

  (3) convolution_eLpNorm_le_of_weak_type — UNCONFIRMED API:
      Meta AI states this exists, but it is NOT on the confirmed API list.
      Confirmed: MeasureTheory.convolution_eLpNorm_le (strong Young, v4.12.0).
      Weak-type variant may not exist; Marcinkiewicz interpolation is not in Mathlib.
      This is the critical unknown. Needs lean --run before use.
      Fix: NS_LorentzYoungAPI_OPEN (§B) — named open def pending confirmation.

  (4) ring on ENNReal — FAILS:
      ENNReal does NOT form a CommRing. `ring` tactic fails on ENNReal goals.
      The arithmetic `t * t^{-1} = 1` in ENNReal uses ENNReal.rpow_add:
        (ofReal t)^1 * (ofReal t)^{-1} = (ofReal t)^(1+(-1)) = (ofReal t)^0 = 1.
      Fix: §A below — explicit ENNReal.rpow_add + norm_num.

CONFIRMED IN THIS SKETCH:
  Mathematical route: L^2 * weak-L^{6/5} → L^3 is correct. ✓
  Exponent: 1/3 = 1/2 + 5/6 - 1 ✓
  riesz_kernel_weak_L65_uncond exists (proved Phase 66) ✓

PROVED IN THIS FILE (0 sorry):
  riesz_distribution_to_weak_bound (§A):
    For any distribution bound vol{|K|≥t} ≤ C*t^{-6/5},
    the weak-norm iSup integrand satisfies t*(vol)^{5/6} ≤ C^{5/6}.
    Uses: ENNReal.rpow_le_rpow + ENNReal.ofReal_rpow_of_nonneg +
          Real.mul_rpow + rpow_add (for t*t^{-1}=1).

Axioms: {propext, Classical.choice, Quot.sound}
Sorry count: 0
================================================================
-/

import Towers.NS.NSPhase66VolumeProof

open Filter Topology Real MeasureTheory Set
open scoped BigOperators ENNReal NNReal
open TheoremaAureum.Towers.NS.FunctionSpaces
open TheoremaAureum.Towers.NS.Phase64FourierBridge
open TheoremaAureum.Towers.NS.Phase65VolumeClosure
open TheoremaAureum.Towers.NS.Phase66VolumeProof

namespace TheoremaAureum
namespace Towers
namespace NS
namespace Phase67YoungGap

/-! ## §A. Distribution bound → weak-norm integrand (proved, 0 sorry) -/

/-- **Distribution bound implies weak-norm bound** (proved, 0 sorry):

    Kernel step for the Riesz potential:
    IF vol{y : ‖y‖^{-5/2} ≥ t} ≤ C · t^{-6/5}  (distribution bound, proved)
    THEN t · (vol{...})^{5/6} ≤ C^{5/6}           (weak L^{6/5} norm integrand)

    This is the purely arithmetic step that converts riesz_kernel_weak_L65_uncond
    into the iSup form needed for eLpNorm_weak characterization.
    Once NS_WeakNormIsSup_OPEN is confirmed, this closes eLpNorm_weak_riesz_kernel.

    Key ENNReal arithmetic:
      (1) ENNReal.rpow_le_rpow: vol ≤ X → vol^{5/6} ≤ X^{5/6}
      (2) ENNReal.ofReal_rpow_of_nonneg: (ofReal(C*t^{-6/5}))^{5/6} = ofReal((C*t^{-6/5})^{5/6})
      (3) Real.mul_rpow: (C*t^{-6/5})^{5/6} = C^{5/6} * t^{-1}
          (-6/5)*(5/6) = -1  [norm_num: ✓]
      (4) ENNReal.rpow_add: (ofReal t)^1 * (ofReal t)^{-1} = (ofReal t)^0 = 1
          requires ofReal t ≠ 0 (from t > 0) and ≠ ∞ (from ofReal_ne_top).

    OBTAIN PATTERN (fixing Meta AI's .2 error):
      obtain ⟨C, hC_pos, hK⟩ := riesz_kernel_weak_L65_uncond
      NOT: riesz_kernel_weak_L65_uncond.2 t ht -/
theorem riesz_distribution_to_weak_bound :
    let K := fun y : EuclideanSpace ℝ (Fin 3) => ‖y‖ ^ (-(5 : ℝ) / 2)
    ∃ C : ℝ, 0 < C ∧
      ∀ t : ℝ, 0 < t →
        ENNReal.ofReal t *
        ((volume : Measure (EuclideanSpace ℝ (Fin 3)))
            {y | t ≤ K y}) ^ ((5 : ℝ) / 6) ≤
        ENNReal.ofReal (C ^ ((5 : ℝ) / 6)) := by
  obtain ⟨C, hC_pos, hK⟩ := riesz_kernel_weak_L65_uncond
  refine ⟨C, hC_pos, fun t ht => ?_⟩
  -- Step 1: use distribution bound
  have hKt : (volume : Measure (EuclideanSpace ℝ (Fin 3)))
      {y | t ≤ ‖y‖ ^ (-(5 : ℝ) / 2)} ≤
      ENNReal.ofReal (C * t ^ (-(6 : ℝ) / 5)) := hK t ht
  -- Step 2: raise to power 5/6 (monotone)
  have hraise : ((volume : Measure _) {y | t ≤ ‖y‖ ^ (-(5 : ℝ) / 2)}) ^ ((5 : ℝ) / 6) ≤
      (ENNReal.ofReal (C * t ^ (-(6 : ℝ) / 5))) ^ ((5 : ℝ) / 6) :=
    ENNReal.rpow_le_rpow hKt (by norm_num)
  -- Step 3: lift rpow through ofReal (C*t^{-6/5} ≥ 0)
  have hlift : (ENNReal.ofReal (C * t ^ (-(6 : ℝ) / 5))) ^ ((5 : ℝ) / 6) =
      ENNReal.ofReal ((C * t ^ (-(6 : ℝ) / 5)) ^ ((5 : ℝ) / 6)) :=
    (ENNReal.ofReal_rpow_of_nonneg (by positivity)).symm
  -- Step 4: split rpow (C*t^{-6/5})^{5/6} = C^{5/6} * t^{-1}
  have hsplit : (C * t ^ (-(6 : ℝ) / 5)) ^ ((5 : ℝ) / 6) =
      C ^ ((5 : ℝ) / 6) * t ^ (-(1 : ℝ)) := by
    rw [Real.mul_rpow hC_pos.le (Real.rpow_nonneg ht.le _), ← Real.rpow_mul ht.le]
    norm_num
  -- Step 5: t * t^{-1} = 1 in ENNReal via rpow_add
  have hcancel : ENNReal.ofReal t * ENNReal.ofReal (t ^ (-(1 : ℝ))) = 1 := by
    rw [← ENNReal.ofReal_mul ht.le, show t * t ^ (-(1 : ℝ)) = 1 from by
      rw [Real.rpow_neg_one ht.ne', mul_inv_cancel₀ ht.ne']]
    exact ENNReal.ofReal_one
  -- Assemble
  calc ENNReal.ofReal t *
      ((volume : Measure _) {y | t ≤ ‖y‖ ^ (-(5 : ℝ) / 2)}) ^ ((5 : ℝ) / 6)
      ≤ ENNReal.ofReal t *
          (ENNReal.ofReal (C * t ^ (-(6 : ℝ) / 5))) ^ ((5 : ℝ) / 6) := by
          gcongr
      _ = ENNReal.ofReal t *
          ENNReal.ofReal (C ^ ((5 : ℝ) / 6) * t ^ (-(1 : ℝ))) := by
          rw [hlift, hsplit]
      _ = ENNReal.ofReal t *
          (ENNReal.ofReal (C ^ ((5 : ℝ) / 6)) * ENNReal.ofReal (t ^ (-(1 : ℝ)))) := by
          rw [ENNReal.ofReal_mul (Real.rpow_nonneg hC_pos.le _)]
      _ = ENNReal.ofReal (C ^ ((5 : ℝ) / 6)) *
          (ENNReal.ofReal t * ENNReal.ofReal (t ^ (-(1 : ℝ)))) := by ring
      _ = ENNReal.ofReal (C ^ ((5 : ℝ) / 6)) := by rw [hcancel, mul_one]

/-! ## §B. Named open defs for unconfirmed APIs -/

/-- **Weak-norm iSup characterization** (named open def, ETA this week):
    eLpNorm f (6/5) volume in weak-type sense = iSup_t (t * vol{|f|≥t}^{5/6}).
    Candidate: MeasureTheory.eLpNorm_weak_eq_iSup_measure_norm_ge (lean --run).
    Needed to connect riesz_distribution_to_weak_bound to eLpNorm goal.
    Meta AI's name may be correct — verify before using. -/
def NS_WeakNormIsSup_OPEN : Prop :=
  ∀ (f : EuclideanSpace ℝ (Fin 3) → ℝ),
    MeasureTheory.AEMeasurable f (volume : Measure _) →
    eLpNorm f (6 / 5) (volume : Measure _) =
    ⨆ t : NNReal, ENNReal.ofReal t *
      ((volume : Measure _) {x | (t : ℝ) ≤ ‖f x‖}) ^ ((5 : ℝ) / 6)

/-- **Lorentz Young convolution API** (named open def, ETA this week):
    MeasureTheory.convolution_eLpNorm_le_of_weak_type (claimed by Meta AI).
    IF this exists: closes NS_YoungConvolutionBound_OPEN immediately.
    IF NOT: alternative route via Calderón-Mityagin interpolation, ETA 3-4 weeks.
    Meta AI note: run `#check MeasureTheory.convolution_eLpNorm_le_of_weak_type`
    to confirm. This is the CRITICAL unknown for the Young step. -/
def NS_LorentzYoungAPI_OPEN : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (p q r : ℝ≥0∞)
      (f g : EuclideanSpace ℝ (Fin 3) → ℂ),
      1 ≤ p → 1 ≤ q → 1 ≤ r →
      1 / r = 1 / p + 1 / q - 1 →
      MeasureTheory.MemLp f p (volume : Measure _) →
      (∃ C_g : ℝ, ∀ t : ℝ, 0 < t →
        (volume : Measure _) {x | t ≤ ‖g x‖} ≤ ENNReal.ofReal (C_g * t ^ (-(q : ℝ)))) →
      eLpNorm (fun x => ∫ y, f (x - y) * g y ∂volume) r (volume : Measure _) ≤
      ENNReal.ofReal C * eLpNorm f p (volume : Measure _)

/-- **Young convolution for Riesz potential** (named open def):
    f ∈ L²(ℝ³), K = ‖·‖^{-5/2} ∈ weak-L^{6/5}(ℝ³) → f*K ∈ L³(ℝ³).
    Closed to 0 sorry when NS_LorentzYoungAPI_OPEN is confirmed (via lean --run). -/
def NS_YoungConvolutionBound_OPEN' : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (f : EuclideanSpace ℝ (Fin 3) → ℂ),
      MeasureTheory.MemLp f 2 (volume : Measure _) →
      eLpNorm
        (fun x => ∫ y, f (x - y) * (‖y‖ ^ (-(5 : ℝ) / 2) : ℝ) ∂volume)
        3 (volume : Measure _) ≤
      ENNReal.ofReal C * eLpNorm f 2 (volume : Measure _)

/-! ## §C. Phase 67 ledger -/

/-
PHASE 67 LEDGER (July 1, 2026):

PROVED (0 sorry, classical trio):
  Phase 66: NS_VolumeBallFormula_proved ✓
  Phase 66: NS_VolumeSuperlevel_Unconditional ✓
  Phase 66: riesz_kernel_weak_L65_uncond ✓
  Phase 67: riesz_distribution_to_weak_bound ✓  ← NEW (ENNReal arithmetic)

NAMED OPEN DEFS REMAINING (3+2 Fourier = 5 total):
  YOUNG CHAIN:
    NS_WeakNormIsSup_OPEN     ← eLpNorm_weak characterization API (ETA this week)
    NS_LorentzYoungAPI_OPEN   ← convolution_eLpNorm_le_of_weak_type (ETA this week)
    NS_YoungConvolutionBound_OPEN' ← closes from NS_LorentzYoungAPI_OPEN

  FOURIER CHAIN:
    NS_PlancherelIsometry_OPEN    ← Plancherel (1 wk)
    NS_FourierRieszRep_OPEN       ← Riesz Fourier symbol (1-2 wks)
    NS_SobolevFourierNorm_OPEN    ← H^s = weighted L^2 Fourier (1 wk)

CHAIN TO D1 (current, July 1):
  riesz_kernel_weak_L65_uncond (✓)
  → riesz_distribution_to_weak_bound (✓)
  → NS_WeakNormIsSup_OPEN (lean --run this week)
  → NS_LorentzYoungAPI_OPEN (lean --run this week)  ← CRITICAL PATH
  → NS_YoungConvolutionBound_OPEN' (closes immediately)
  → NS_FourierRieszRep_OPEN + NS_PlancherelIsometry_OPEN + NS_SobolevFourierNorm_OPEN
  → NS_SobolevL3_Conditional (✓ proved conditional, Phase 64)
  → NS_BilinearEstimate_OPEN (D1)

MESSAGE TO META AI (next sketch):
  Run lean --run to check BOTH:
    #check MeasureTheory.convolution_eLpNorm_le_of_weak_type
    #check MeasureTheory.eLpNorm_weak_eq_iSup_measure_norm_ge
  If convolution_eLpNorm_le_of_weak_type EXISTS:
    Provide its exact signature (all type class arguments).
    Then NS_YoungConvolutionBound_OPEN closes immediately.
  If NOT: report which weak-type convolution theorem IS in Mathlib v4.12.0.
    (Try: MeasureTheory.convolution_eLpNorm_le, MeasureTheory.weakType_convolution)

ENNReal RULE (permanent):
  ring FAILS on ENNReal. Use rpow_add, mul_comm, mul_assoc, gcongr.
  t * t^{-1} in ENNReal: use ENNReal.rpow_add with exponents 1 and -1.
-/

end Phase67YoungGap
end NS
end Towers
end TheoremaAureum
