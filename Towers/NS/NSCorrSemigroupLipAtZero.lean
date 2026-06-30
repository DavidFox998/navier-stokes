/-
  NSCorrSemigroupLipAtZero.lean  --  Phase 33: NS Tower, navier-stokes repo
  Author: David Fox  |  Date: May 21, 2026
  Series: Opera Numerorum (internal: Battle Plan v1.6)

  PHASE 33: Close NS_CorrSemigroupLipAtZero_OPEN.
  0 sorry. 0 cert axioms. Classical trio only.

  STATEMENT (from Phase 32 def):
    For u₀ : Hdiv_free(s+2) and t >= 0:
      ‖corrSemigroup s t ht u₀ - u₀‖ <= 1/4 * t * ‖u₀‖

  PROOF ROUTE (mirrors Phase 26 NSLpErrorPlumbing):
    Step 1. Submodule.norm_coe + map_sub + corrSemigroup_coe_eq_lin (reproved locally):
            ‖corrSemigroup s t ht u₀ - u₀‖ = ‖corrSemigroupLin s t ht f - f‖_Lp
    Step 2. Lp.norm_def: ‖·‖_Lp = (eLpNorm ↑· 2 mu).toReal
    Step 3. eLpNorm_congr_ae:
            reduce to eLpNorm (fun xi => (corrSemSym t xi - 1) • f xi) 2 mu
            via corrSemigroup_sub_id_ae_rep (Lp.coeFn_sub + corrSemigroup_memLp.coeFn_toLp
            + sub_smul + one_smul)
    Step 4. eLpNorm_mono_ae + corrSemigroupSymbol_sub_one_le (Phase 32):
            <= eLpNorm (fun xi => (1/4 * t) • f xi) 2 mu
    Step 5. eLpNorm_const_smul + Real.ennnorm_eq_ofReal:
            = ENNReal.ofReal (1/4 * t) * eLpNorm f 2 mu
    Step 6. ENNReal.toReal_mono + ENNReal.toReal_mul + ENNReal.toReal_ofReal
            + <- Lp.norm_def + <- Submodule.norm_coe:
            = 1/4 * t * ‖u₀‖

  KEY INGREDIENT from Phase 32:
    corrSemigroupSymbol_sub_one_le xi t ht : ‖corrSemSym t xi - 1‖ <= 1/4 * t

  CERT AXIOMS: classical trio only. NOT a Clay problem.
  #print axioms ns_corrSemigroup_lip_at_zero_proved = classical trio.
-/

import Mathlib.MeasureTheory.Function.LpSpace

import Towers.NS.NSCorrSemigroupContinuity

namespace TheoremaAureum.Towers.NS.CorrSemigroupLipAtZero

open Real Set Filter Topology MeasureTheory
open scoped BigOperators ENNReal NNReal
open TheoremaAureum.Towers.NS.FunctionSpaces
open TheoremaAureum.Towers.NS.SemigroupDef
open TheoremaAureum.Towers.NS.WeakSolution
open TheoremaAureum.Towers.NS.Stokes
open TheoremaAureum.Towers.NS.DerivSemigroup
open TheoremaAureum.Towers.NS.BochnerDiff
open TheoremaAureum.Towers.NS.CorrSemigroupContinuity
open NSTower

variable {s : ℝ}

/-! ## I. Coercion helper (reproved locally; corrSemigroup_coe_eq_lin is private in
    NSLpErrorPlumbing) -/

/-- Coercion of corrSemigroup to Hsv equals corrSemigroupLin.
    Proof: unfold corrSemigroup via codRestrict_apply + comp_apply + subtypeL_apply. -/
private lemma corrSemigroup_coe_eq_lin (t : ℝ) (ht : 0 ≤ t) (u : Hdiv_free (s + 2)) :
    (corrSemigroup s t ht u : Hsv (s + 2)) = corrSemigroupLin s t ht (u : Hsv (s + 2)) := by
  simp only [corrSemigroup, ContinuousLinearMap.codRestrict_apply,
    ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]

/-! ## II. A.e. rep of corrSemigroupLin t f - f -/

/-- A.e. representative of (corrSemigroupLin s t ht f - f) equals
    (corrSemSym t xi - 1) • f xi.

    Proof:
      Lp.coeFn_sub: ↑(A - B) =ᵐ ↑A - ↑B
      corrSemigroup_memLp.coeFn_toLp: ↑A =ᵐ fun xi => corrSemSym t xi • f xi
      sub_smul + one_smul: corrSemSym t xi • f xi - f xi = (corrSemSym t xi - 1) • f xi -/
private lemma corrSemigroup_sub_id_ae_rep (t : ℝ) (ht : 0 ≤ t)
    (u₀ : Hdiv_free (s + 2)) :
    (↑(corrSemigroupLin s t ht (u₀ : Hsv (s + 2)) - (u₀ : Hsv (s + 2))) :
        FreqDomain → Val) =ᵐ[mu (s + 2)]
      fun xi => (corrSemigroupSymbol t xi - 1) • (u₀ : Hsv (s + 2)) xi := by
  set f := (u₀ : Hsv (s + 2))
  -- A.e. rep of corrSemigroupLin s t ht f
  have hA : (↑(corrSemigroupLin s t ht f) : FreqDomain → Val) =ᵐ[mu (s + 2)]
      fun xi => corrSemigroupSymbol t xi • f xi :=
    (corrSemigroup_memLp s t ht f).coeFn_toLp
  -- Distribute coeFn over subtraction
  filter_upwards [Lp.coeFn_sub (corrSemigroupLin s t ht f) f, hA] with xi h1 hA_xi
  -- h1 : ↑(A - f) xi = ↑(corrSemigroupLin ...) xi - ↑f xi
  simp only [Pi.sub_apply] at h1
  rw [h1, hA_xi]
  -- Goal: corrSemSym t xi • f xi - f xi = (corrSemSym t xi - 1) • f xi
  rw [sub_smul, one_smul]

/-! ## III. Main theorem -/

/-- **Phase 33: NS_CorrSemigroupLipAtZero_OPEN CLOSED (0 sorry, classical trio).**

    ‖corrSemigroup s t ht u₀ - u₀‖ <= 1/4 * t * ‖u₀‖  for t >= 0.

    Proof route:
      (1) Submodule.norm_coe + map_sub + corrSemigroup_coe_eq_lin
      (2) Lp.norm_def
      (3) eLpNorm_congr_ae (corrSemigroup_sub_id_ae_rep)
      (4) eLpNorm_mono_ae (corrSemigroupSymbol_sub_one_le from Phase 32)
      (5) eLpNorm_const_smul (constant factor extraction)
      (6) ENNReal.toReal_mul + toReal_ofReal + <- Lp.norm_def + <- Submodule.norm_coe

    #print axioms ns_corrSemigroup_lip_at_zero_proved = classical trio.
    CERT AXIOMS: 0 (classical trio only). NOT a Clay open problem. -/
theorem ns_corrSemigroup_lip_at_zero_proved : NS_CorrSemigroupLipAtZero_OPEN s := by
  intro t ht u₀
  -- Step 1: reduce Hdiv norm to Lp norm via coe + linearity
  have hstep1 : ‖corrSemigroup s t ht u₀ - u₀‖ =
      ‖corrSemigroupLin s t ht (u₀ : Hsv (s + 2)) - (u₀ : Hsv (s + 2))‖ := by
    rw [← Submodule.norm_coe]
    congr 1
    simp only [map_sub, corrSemigroup_coe_eq_lin]
  rw [hstep1]
  -- Step 2: Lp.norm_def
  rw [Lp.norm_def]
  -- Step 3: a.e. rep via corrSemigroup_sub_id_ae_rep
  rw [eLpNorm_congr_ae (corrSemigroup_sub_id_ae_rep t ht u₀)]
  -- Now goal: (eLpNorm (fun xi => (corrSemSym t xi - 1) • f xi) 2 mu).toReal <= 1/4*t*‖u₀‖
  -- Step 4-6: bound eLpNorm and convert
  have hnn : (0 : ℝ) ≤ 1 / 4 * t := by positivity
  have hfin : ENNReal.ofReal (1 / 4 * t) *
      eLpNorm (u₀ : Hsv (s + 2)) 2 (mu (s + 2)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (eLpNorm_ne_top _)
  calc (eLpNorm (fun xi => (corrSemigroupSymbol t xi - 1) • (u₀ : Hsv (s + 2)) xi)
            2 (mu (s + 2))).toReal
      ≤ (ENNReal.ofReal (1 / 4 * t) *
          eLpNorm (u₀ : Hsv (s + 2)) 2 (mu (s + 2))).toReal := by
        apply ENNReal.toReal_mono hfin
        -- Step 4: eLpNorm_mono_ae with pointwise bound
        apply (eLpNorm_mono_ae _).trans
        · -- Step 5: eLpNorm_const_smul
          rw [eLpNorm_const_smul, Real.ennnorm_eq_ofReal hnn]
        · -- Pointwise: ‖(corrSemSym t xi - 1) • f xi‖ <= ‖(1/4*t) • f xi‖
          filter_upwards [] with xi
          rw [norm_smul, norm_smul, Real.norm_of_nonneg hnn]
          exact mul_le_mul_of_nonneg_right
            (corrSemigroupSymbol_sub_one_le xi t ht) (norm_nonneg _)
    _ = 1 / 4 * t * ‖u₀‖ := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hnn,
            ← Lp.norm_def, ← Submodule.norm_coe]

/-! ## IV. Phase 33 gap accounting -/

/-- **Phase 33: NS Tower gap accounting after this file.**

    PROVED IN PHASE 33 (0 sorry, 0 cert axioms, classical trio only):
      ns_corrSemigroup_lip_at_zero_proved  -- NS_CorrSemigroupLipAtZero_OPEN CLOSED

    NAMED OPEN DEF STATUS (NS Tower after Phase 33):
      NS_StokesMaxReg_OPEN s           -- Hieber-Pruss, ~6-18 months (UNCHANGED)
      NS_WeakMomentumDiffAt_OPEN s     -- B.1: WeakMomentum HasDerivAt, ~1-3 months
      NS_AdjointIntegralConst_OPEN s   -- B.3: orbit ID via adjoint, ~2-4 months

    ELIMINATED: NS_CorrSemigroupLipAtZero_OPEN (THIS FILE)

    NS_WeakInitCont_OPEN (via Phase 32 ns_weakInitCont_from_orbit):
      PROVABLE from B.1 + B.3 alone.
      No MaxReg dependency.

    NS Clay Surface #1: LOCKED OPEN. No Clay claim.
    CERT AXIOMS: classical trio only. -/
theorem phase33_gap_accounting : True := trivial

end TheoremaAureum.Towers.NS.CorrSemigroupLipAtZero
