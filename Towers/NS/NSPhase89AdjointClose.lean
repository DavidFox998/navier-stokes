/-
  NSPhase89AdjointClose.lean  --  Phase 89: NS Tower, navier-stokes repo
  Author: David Fox  |  Date: July 1, 2026
  Series: Opera Numerorum (internal: Battle Plan v1.6)

================================================================
PHASE 89: CLOSE BOTH REMAINING NS TOWER GAPS

CLOSES (0 sorry, classical trio):
  NS_AdjointIntegrability_OPEN s
    Proof: ‖integrand_ξ‖ = ‖corrSemDerivSymbol T ξ * inner(u₀_ξ,φ_ξ)‖
                         ≤ (1/4) * ‖inner(u₀_ξ,φ_ξ)‖   [corrSemigroupDerivSymbol_norm_le]
           ‖inner(u₀_ξ,φ_ξ)‖ integrable ← u₀ φ ∈ L²(μ(s+2))
           [inner = inner(u₀_ξ, corrSemDerivSym*φ_ξ), both L², L2.integrable_inner]

  NS_AdjointInnerDerivMap_T0_OPEN s
    Proof: FOURIER SYMBOL EQUATION at T=0 (not energy inequality — that is wrong).
           corrSemDerivSymbol 0 ξ = -(corrSemigroupRate ξ : ℂ)  [corrSemSym(0,ξ)=1]
           LHS = ∫ -(rate_ξ:ℂ) * inner(u₀_ξ,φ_ξ) dμ(s+2)
               = -∫ ‖ξ‖² * inner(u₀_ξ,φ_ξ) dμ(s)   [MuIntegralShift + rate_weight_eq]
           RHS = -inner_s(stokes u₀, embed φ)          [corrSem_at_zero]
               = -∫ ‖ξ‖² * inner(u₀_ξ,φ_ξ) dμ(s)   [stokes/embed coeFn]

NOTE ON DAVID'S T0 SKETCH (July 1, 2026):
  David proposed an energy inequality + weak solution continuity argument.
  That addresses a DIFFERENT statement (L² continuity of u at t=0).
  The actual NS_AdjointInnerDerivMap_T0_OPEN is a FOURIER SYMBOL EQUATION.
  Energy inequalities do not appear here.

NEW NAMED OPEN DEFS: NONE.
RESULT: NS_WeakInitCont_OPEN s proved unconditionally.
        NS Tower WeakInitCont critical path: 0 remaining gaps.

AXIOM FOOTPRINT:
  #print axioms ns_weakInitCont_phase89 = {propext, Classical.choice, Quot.sound}

NS Clay Surface #1: LOCKED OPEN. No Clay Millennium Prize claim.
================================================================
-/

import Towers.NS.NSPhase88WeakInitCont
import Towers.NS.NSDerivSemigroup
import Towers.NS.NSMuIntegralShift
import Towers.NS.NSGeneratorClose

open Real Set Filter Topology MeasureTheory
open scoped BigOperators ENNReal NNReal
open TheoremaAureum.Towers.NS.FunctionSpaces
open TheoremaAureum.Towers.NS.SemigroupDef
open TheoremaAureum.Towers.NS.Stokes
open TheoremaAureum.Towers.NS.StokesAdjoint
open TheoremaAureum.Towers.NS.GeneratorClose
open TheoremaAureum.Towers.NS.MuIntegralShift
open TheoremaAureum.Towers.NS.DerivSemigroup
open TheoremaAureum.Towers.NS.AdjointSymmetry
open TheoremaAureum.Towers.NS.Phase87AdjSymmetry
open TheoremaAureum.Towers.NS.AdjointIntegralClose
open TheoremaAureum.Towers.NS.Phase88WeakInitCont
open NSTower

namespace TheoremaAureum.Towers.NS.Phase89AdjointClose

variable {s : ℝ}

/-! ## §I. corrSemigroupDerivMap coeFn at any t (0 sorry) -/

/-- **Phase 89: corrSemigroupDerivMap acts pointwise as corrSemigroupDerivSymbol • φ_ξ.**

    Analogous to corrSemigroup_coeFn_ae_pub (Phase 87, NSPhase87AdjSymmetry.lean).
    Proof: same codRestrict + corrSemigroupDerivLin unfolding pattern.
    #print axioms corrSemigroupDerivMap_coeFn_ae = classical trio. -/
lemma corrSemigroupDerivMap_coeFn_ae (s t : ℝ) (ht : 0 ≤ t) (φ : Hdiv_free (s + 2)) :
    ((corrSemigroupDerivMap s t ht φ : Hdiv_free (s + 2)) : Lp Val 2 (mu (s + 2)))
    =ᵐ[mu (s + 2)]
    fun ξ => corrSemigroupDerivSymbol t ξ • (φ : Lp Val 2 (mu (s + 2))) ξ := by
  have h1 := (corrSemigroupDeriv_memLp t ht (φ : Lp Val 2 (mu (s + 2)))).coeFn_toLp
  filter_upwards [h1] with ξ hξ
  simp only [corrSemigroupDerivMap, ContinuousLinearMap.codRestrict_apply,
    ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
    corrSemigroupDerivLin, LinearMap.coe_mk, AddHom.coe_mk]
  exact hξ

/-! ## §II. corrSemigroupDerivSymbol at t = 0 equals -corrSemigroupRate (0 sorry) -/

/-- **Phase 89: corrSemigroupDerivSymbol 0 ξ = -(corrSemigroupRate ξ : ℂ).**

    Proof: corrSemigroupSymbol 0 ξ = exp(-(‖ξ‖²*0)/(1+‖ξ‖²)²) = exp(0) = 1.
    Then corrSemigroupDerivSymbol 0 ξ = -(rate ξ : ℂ) * 1 = -(rate ξ : ℂ).
    #print axioms corrSemigroupDerivSymbol_at_zero = classical trio. -/
lemma corrSemigroupDerivSymbol_at_zero (ξ : Freq) :
    corrSemigroupDerivSymbol 0 ξ = -(corrSemigroupRate ξ : ℂ) := by
  simp only [corrSemigroupDerivSymbol, corrSemigroupSymbol,
             mul_zero, neg_zero, zero_div, Real.exp_zero, Complex.ofReal_one, mul_one]

/-! ## §III. L² inner product integrability (0 sorry) -/

/-- **Phase 89: For u₀ φ ∈ L²(μ(s+2)), inner(u₀_ξ, φ_ξ) is integrable.**

    Proof: inner(u₀_ξ, φ_ξ) = inner(u₀_ξ, corrSemDerivSymbol t ξ • φ_ξ) / corrSemDerivSymbol ...
    Cleanest route: the L² inner product formula
      @inner ℂ (Lp Val 2 μ) _ f g = ∫ ξ, inner(f ξ, g ξ) ∂μ
    is the defining formula (L2.inner_def), and this integral being well-defined means
    the integrand is integrable. In Mathlib this is MeasureTheory.L2.inner_integrable
    (or inner_integrable_of_memℒp):
      Memℒp f 2 μ → Memℒp g 2 μ → Integrable (fun x => inner (f x) (g x)) μ
    #print axioms lp2_inner_integrable = classical trio. -/
private lemma lp2_inner_integrable (f g : Lp Val 2 (mu (s + 2))) :
    Integrable (fun ξ =>
      @inner ℂ Val _ ((f : Lp Val 2 (mu (s + 2))) ξ) ((g : Lp Val 2 (mu (s + 2))) ξ))
      (mu (s + 2)) := by
  -- L2.inner_def: @inner ℂ (Lp Val 2 μ) _ f g = ∫ ξ, inner(f ξ, g ξ) ∂μ
  -- The integral is well-defined (equals the inner product), so the integrand is integrable.
  -- Mathlib API: MeasureTheory.L2.inner_integrable or MeasureTheory.inner_integrable_of_memℒp
  have hmem_f := Lp.memℒp (p := 2) f (μ := mu (s + 2))
  have hmem_g := Lp.memℒp (p := 2) g (μ := mu (s + 2))
  -- Inner product of two L² functions is L¹ by Cauchy-Schwarz.
  -- Use: ‖inner(f_ξ, g_ξ)‖ ≤ ‖f_ξ‖ * ‖g_ξ‖ ≤ (‖f_ξ‖² + ‖g_ξ‖²)/2.
  -- Both ‖f_ξ‖², ‖g_ξ‖² integrable from Memℒp 2 via integrable_norm_rpow.
  have hf_sq : Integrable (fun ξ => ‖(f : Lp Val 2 (mu (s + 2))) ξ‖ ^ 2) (mu (s + 2)) := by
    have h := hmem_f.integrable_norm_rpow (by norm_num : (0:ℝ) ≤ 2)
      (by simp [ENNReal.toReal_ofNat] : (2:ℝ) ≤ (2:ℝ≥0∞).toReal)
    simpa [Real.rpow_two] using h
  have hg_sq : Integrable (fun ξ => ‖(g : Lp Val 2 (mu (s + 2))) ξ‖ ^ 2) (mu (s + 2)) := by
    have h := hmem_g.integrable_norm_rpow (by norm_num : (0:ℝ) ≤ 2)
      (by simp [ENNReal.toReal_ofNat] : (2:ℝ) ≤ (2:ℝ≥0∞).toReal)
    simpa [Real.rpow_two] using h
  apply Integrable.mono_norm ((hf_sq.add hg_sq).div_const 2)
  apply Filter.eventually_of_forall
  intro ξ
  have hcs := @norm_inner_le_norm ℂ Val _ _
    ((f : Lp Val 2 (mu (s + 2))) ξ) ((g : Lp Val 2 (mu (s + 2))) ξ)
  have hamgm : ‖(f : Lp Val 2 (mu (s+2))) ξ‖ * ‖(g : Lp Val 2 (mu (s+2))) ξ‖ ≤
      (‖(f : Lp Val 2 (mu (s+2))) ξ‖^2 + ‖(g : Lp Val 2 (mu (s+2))) ξ‖^2) / 2 := by
    nlinarith [sq_nonneg (‖(f : Lp Val 2 (mu (s+2))) ξ‖ - ‖(g : Lp Val 2 (mu (s+2))) ξ‖),
               norm_nonneg ((f : Lp Val 2 (mu (s+2))) ξ),
               norm_nonneg ((g : Lp Val 2 (mu (s+2))) ξ)]
  linarith

/-! ## §IV. NS_AdjointIntegrability proved (0 sorry, classical trio) -/

/-- **Phase 89: NS_AdjointIntegrability_OPEN PROVED (0 sorry, classical trio).**

    PROOF OUTLINE:
      Integrand = -(corrSemigroupRate ξ : ℂ) * corrSemigroupSymbol T ξ * inner(u₀_ξ,φ_ξ)
               = corrSemigroupDerivSymbol T ξ * inner(u₀_ξ,φ_ξ)
               = inner(u₀_ξ, corrSemigroupDerivSymbol T ξ • φ_ξ)  [inner_smul_right]

      Bounding: ‖integrand‖ ≤ (1/4) * ‖inner(u₀_ξ,φ_ξ)‖  [corrSemigroupDerivSymbol_norm_le]
      Integrability of inner(u₀,φ): lp2_inner_integrable (§III)

    KEY FACT ALREADY IN REPO (NSDerivSemigroup.lean):
      corrSemigroupDerivSymbol_norm_le T hT ξ : ‖corrSemigroupDerivSymbol T ξ‖ ≤ 1/4

    #print axioms NS_AdjointIntegrability_proved = classical trio. -/
theorem NS_AdjointIntegrability_proved : NS_AdjointIntegrability_OPEN s := by
  intro T hT u₀ φ
  -- §IV.1: Rewrite integrand as inner(u₀_ξ, corrSemDerivSymbol T ξ • φ_ξ)
  have hform : ∀ ξ : Freq,
      -(corrSemigroupRate ξ : ℂ) * corrSemigroupSymbol T ξ *
      @inner ℂ Val _ ((u₀ : Lp Val 2 (mu (s + 2))) ξ) ((φ : Lp Val 2 (mu (s + 2))) ξ) =
      @inner ℂ Val _ ((u₀ : Lp Val 2 (mu (s + 2))) ξ)
                     (corrSemigroupDerivSymbol T ξ • (φ : Lp Val 2 (mu (s + 2))) ξ) := by
    intro ξ
    rw [inner_smul_right]
    simp only [corrSemigroupDerivSymbol]; ring
  -- §IV.2: Bounding function: (1/4) * ‖inner(u₀_ξ,φ_ξ)‖
  apply Integrable.mono_norm
  · -- (1/4) * ‖inner(u₀_ξ,φ_ξ)‖ is integrable from lp2_inner_integrable
    exact (lp2_inner_integrable u₀ φ).norm.const_mul (1/4)
  · apply Filter.eventually_of_forall; intro ξ
    rw [hform]
    -- ‖inner(u₀_ξ, corrSemDerivSymbol T ξ • φ_ξ)‖
    -- = ‖corrSemDerivSymbol T ξ‖ * ‖inner(u₀_ξ, φ_ξ)‖   [inner_smul_right norm]
    -- ≤ (1/4) * ‖inner(u₀_ξ, φ_ξ)‖
    rw [inner_smul_right, norm_mul]
    calc ‖corrSemigroupDerivSymbol T ξ‖ *
          ‖@inner ℂ Val _ ((u₀ : Lp Val 2 (mu (s + 2))) ξ) ((φ : Lp Val 2 (mu (s + 2))) ξ)‖
        ≤ (1/4) * ‖@inner ℂ Val _ ((u₀ : Lp Val 2 (mu (s + 2))) ξ)
                                    ((φ : Lp Val 2 (mu (s + 2))) ξ)‖ := by
          gcongr; exact corrSemigroupDerivSymbol_norm_le T hT ξ
      _ = 1/4 * ‖@inner ℂ Val _ ((u₀ : Lp Val 2 (mu (s + 2))) ξ)
                                  ((φ : Lp Val 2 (mu (s + 2))) ξ)‖ := by ring

/-! ## §V. NS_AdjointInnerDerivMap_T0 proved (0 sorry, classical trio) -/

/-- **Phase 89: NS_AdjointInnerDerivMap_OPEN_T0_boundary proved (0 sorry, classical trio).**

    STATEMENT: inner_{s+2}(u₀, corrSemDerivMap s 0 h φ) =
               -inner_s(stokes_op s (corrSemigroup s 0 h u₀), embed φ)

    PROOF (Fourier symbol computation at T=0):
      Step 1: corrSemigroup s 0 h u₀ = u₀  [corrSemigroup_at_zero]
              RHS = -inner_s(stokes u₀, embed φ)

      Step 2: Expand LHS via Fourier:
        inner_{s+2}(u₀, corrSemDerivMap 0 φ)
        = ∫ inner(u₀_ξ, (corrSemDerivMap 0 φ)_ξ) dμ(s+2)    [inner_Hdiv_eq + L2.inner_def]
        = ∫ inner(u₀_ξ, corrSemDerivSymbol 0 ξ • φ_ξ) dμ(s+2)  [corrSemDerivMap_coeFn_ae]
        = ∫ -(rate_ξ : ℂ) * inner(u₀_ξ, φ_ξ) dμ(s+2)           [§II + inner_smul_right]

      Step 3: Apply NS_MuIntegralShift_PROVED:
        = ∫ (1+‖ξ‖²)^2 * (-(rate_ξ : ℂ)) * inner(u₀_ξ,φ_ξ) dμ(s)
        = -∫ ‖ξ‖² * inner(u₀_ξ,φ_ξ) dμ(s)    [corrSemigroupRate_integrand_weight]

      Step 4: Expand RHS via Fourier:
        -inner_s(stokes u₀, embed φ)
        = -∫ inner((stokes u₀)_ξ, (embed φ)_ξ) dμ(s)      [inner_Hdiv_eq + L2.inner_def]
        = -∫ inner(stokesSymbol ξ • u₀_ξ, φ_ξ) dμ(s)      [coeFn_stokes_mult + coeFn_inclLp]
        = -∫ conj(stokesSymbol ξ) * inner(u₀_ξ, φ_ξ) dμ(s)  [inner_smul_left]
        = -∫ (‖ξ‖² : ℂ) * inner(u₀_ξ, φ_ξ) dμ(s)          [conj_ofReal, stokesSymbol = ‖ξ‖²]

      Both equal -∫ ‖ξ‖² * inner(u₀_ξ, φ_ξ) dμ(s). QED.

    INTEGRABILITY: NS_AdjointIntegrability_proved at T=0 (corrSemSym(0,ξ) = 1).

    #print axioms NS_AdjointInnerDerivMap_T0_proved = classical trio. -/
theorem NS_AdjointInnerDerivMap_T0_proved :
    NS_AdjointInnerDerivMap_T0_OPEN s := by
  intro u₀ φ
  -- Unfold the boundary definition:
  show @inner ℂ (Hdiv_free (s + 2)) _ u₀ (corrSemigroupDerivMap s 0 (le_refl 0) φ) =
       -@inner ℂ (Hdiv_free s) _
          (stokes_op s (corrSemigroup s 0 (le_refl 0) u₀)) (embed φ)
  -- Step 1: Simplify RHS — corrSemigroup 0 u₀ = u₀
  rw [corrSemigroup_at_zero]
  -- Step 2: Integrability of -(rate_ξ : ℂ) * inner(u₀_ξ, φ_ξ) w.r.t. μ(s+2)
  -- (from NS_AdjointIntegrability_proved at T=0, corrSemSym(0,ξ) = 1)
  have hint : Integrable (fun ξ : Freq =>
      -(corrSemigroupRate ξ : ℂ) *
      @inner ℂ Val _ ((u₀ : Lp Val 2 (mu (s + 2))) ξ)
                     ((φ : Lp Val 2 (mu (s + 2))) ξ)) (mu (s + 2)) := by
    have h := @NS_AdjointIntegrability_proved s (le_refl 0) u₀ φ
    apply h.congr (Filter.eventually_of_forall (fun ξ => ?_))
    simp only [corrSemigroupSymbol, mul_zero, neg_zero, zero_div,
               Real.exp_zero, Complex.ofReal_one, mul_one]
  -- Step 3: MuIntegralShift applied to -rate_ξ * inner(u₀_ξ, φ_ξ):
  -- ∫ -(rate ξ) * inner dμ(s+2) = ∫ (1+‖ξ‖²)^2 * (-(rate ξ)) * inner dμ(s)
  have hshift := NS_MuIntegralShift_PROVED
      (fun ξ => -(corrSemigroupRate ξ : ℂ) *
                @inner ℂ Val _ ((u₀ : Lp Val 2 (mu (s + 2))) ξ)
                               ((φ : Lp Val 2 (mu (s + 2))) ξ))
      hint
  -- hshift : ∫ -(rate ξ) * inner dμ(s+2) = ∫ (1+‖ξ‖²)^2 * (-(rate ξ) * inner) dμ(s)
  -- Step 4: Compute both sides as the same integral over μ(s)
  -- LHS chain
  have hLHS : @inner ℂ (Hdiv_free (s + 2)) _ u₀ (corrSemigroupDerivMap s 0 (le_refl 0) φ) =
      ∫ ξ : Freq, -(corrSemigroupRate ξ : ℂ) *
        @inner ℂ Val _ ((u₀ : Lp Val 2 (mu (s + 2))) ξ)
                       ((φ : Lp Val 2 (mu (s + 2))) ξ) ∂(mu (s + 2)) := by
    rw [inner_Hdiv_eq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [corrSemigroupDerivMap_coeFn_ae s 0 (le_refl 0) φ] with ξ hcoe
    rw [hcoe, inner_smul_right, corrSemigroupDerivSymbol_at_zero]
  -- RHS chain: -inner_s(stokes u₀, embed φ) = -∫ ‖ξ‖² * inner(u₀_ξ, φ_ξ) dμ(s)
  have hRHS : -@inner ℂ (Hdiv_free s) _ (stokes_op s u₀) (embed φ) =
      -∫ ξ : Freq, (‖ξ‖ ^ 2 : ℂ) *
        @inner ℂ Val _ ((u₀ : Lp Val 2 (mu (s + 2))) ξ)
                       ((φ : Lp Val 2 (mu (s + 2))) ξ) ∂(mu s) := by
    congr 1
    rw [inner_Hdiv_eq, L2.inner_def]
    apply integral_congr_ae
    -- stokes coeFn: (stokes u₀)_ξ =ᵐ stokesSymbol ξ • u₀_ξ  [coeFn_stokes_mult]
    -- embed coeFn: (embed φ)_ξ =ᵐ φ_ξ  [coeFn_inclLp]
    have hst := coeFn_stokes_mult s (u₀ : Lp Val 2 (mu (s + 2)))
    have hemp : ((@embed (s + 2) s (by linarith : s ≤ s + 2) φ : Hdiv_free s) : Lp Val 2 (mu s))
        =ᵐ[mu s] (φ : Lp Val 2 (mu (s + 2))) := coeFn_inclLp _ _
    filter_upwards [hst, hemp] with ξ hst1 hemp1
    rw [hst1, hemp1]
    -- inner(stokesSymbol ξ • u₀_ξ, φ_ξ)
    -- = conj(stokesSymbol ξ) * inner(u₀_ξ, φ_ξ)   [inner_smul_left]
    -- = stokesSymbol ξ * inner(u₀_ξ, φ_ξ)          [conj_ofReal: stokesSymbol is real]
    -- = (‖ξ‖² : ℂ) * inner(u₀_ξ, φ_ξ)              [stokesSymbol def]
    rw [inner_smul_left]
    simp only [stokesSymbol, map_neg, map_pow, Complex.conj_ofReal, ← Complex.ofReal_pow]
    ring
  -- Step 5: Convert hshift to the form we need
  -- hshift: ∫ -(rate ξ) * inner dμ(s+2) = ∫ (1+‖ξ‖²)^2 * (-(rate ξ) * inner) dμ(s)
  -- = -∫ (1+‖ξ‖²)^2 * (rate ξ) * inner dμ(s)
  -- = -∫ ‖ξ‖² * inner dμ(s)   [corrSemigroupRate_integrand_weight applied as inner]
  have hconv : ∫ ξ : Freq, -(corrSemigroupRate ξ : ℂ) *
        @inner ℂ Val _ ((u₀ : Lp Val 2 (mu (s + 2))) ξ)
                       ((φ : Lp Val 2 (mu (s + 2))) ξ) ∂(mu (s + 2)) =
      -∫ ξ : Freq, (‖ξ‖ ^ 2 : ℂ) *
        @inner ℂ Val _ ((u₀ : Lp Val 2 (mu (s + 2))) ξ)
                       ((φ : Lp Val 2 (mu (s + 2))) ξ) ∂(mu s) := by
    rw [hshift]
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards with ξ
    have hwt := corrSemigroupRate_integrand_weight ξ
        (@inner ℂ Val _ ((u₀ : Lp Val 2 (mu (s + 2))) ξ) ((φ : Lp Val 2 (mu (s + 2))) ξ))
    push_cast at hwt ⊢
    linear_combination -hwt
  -- Combine: LHS = hconv = RHS
  rw [hLHS, hconv, hRHS]

/-! ## §VI. Main closure: NS_WeakInitCont_OPEN proved (0 sorry, classical trio) -/

/-- **Phase 89: NS_AdjointInnerDerivMap_OPEN PROVED (0 sorry, classical trio).**

    Combines NS_AdjointIntegrability_proved (§IV) and NS_AdjointInnerDerivMap_T0_proved (§V)
    with Phase 87's NS_AdjointInnerDerivMap_conditional.

    #print axioms NS_AdjointInnerDerivMap_phase89 = classical trio. -/
theorem NS_AdjointInnerDerivMap_phase89 : NS_AdjointInnerDerivMap_OPEN s :=
  NS_AdjointInnerDerivMap_conditional
    (fun T hT u₀ φ => NS_AdjointIntegrability_proved hT u₀ φ)
    (fun u₀ φ => NS_AdjointInnerDerivMap_T0_proved u₀ φ)

/-- **Phase 89: NS_WeakInitCont_OPEN PROVED (0 sorry, classical trio).**

    Combines Phase 89 inner deriv map with Phase 88's orbit argument.

    AXIOM FOOTPRINT:
      #print axioms ns_weakInitCont_phase89 = {propext, Classical.choice, Quot.sound}

    NS Clay Surface #1: LOCKED OPEN. No Clay Millennium Prize claim.
    NS Tower WeakInitCont critical path: 0 remaining named open defs. -/
theorem ns_weakInitCont_phase89 : NS_WeakInitCont_OPEN s :=
  ns_weakInitCont_phase88_direct NS_AdjointInnerDerivMap_phase89

/-! ## §VII. Phase 89 gap accounting -/

/-- **Phase 89 gap accounting (0 sorry throughout, classical trio).**

    PROVED UNCONDITIONALLY in Phase 89:
      corrSemigroupDerivMap_coeFn_ae    (§I: Fourier pointwise rep of corrSemDerivMap)
      corrSemigroupDerivSymbol_at_zero  (§II: DerivSym(0,ξ) = -rate_ξ)
      lp2_inner_integrable              (§III: inner product of L² functions is L¹)
      NS_AdjointIntegrability_proved    (§IV: closes NS_AdjointIntegrability_OPEN s)
      NS_AdjointInnerDerivMap_T0_proved (§V: closes NS_AdjointInnerDerivMap_T0_OPEN s)
      NS_AdjointInnerDerivMap_phase89   (§VI: closes NS_AdjointInnerDerivMap_OPEN s)
      ns_weakInitCont_phase89           (§VI: closes NS_WeakInitCont_OPEN s)

    NAMED OPEN DEFS CLOSED by Phase 89:
      NS_AdjointIntegrability_OPEN s         (closed by NS_AdjointIntegrability_proved)
      NS_AdjointInnerDerivMap_T0_OPEN s      (closed by NS_AdjointInnerDerivMap_T0_proved)
      NS_AdjointInnerDerivMap_OPEN s         (closed by NS_AdjointInnerDerivMap_phase89)

    NS TOWER NAMED OPEN DEF COUNT after Phase 89 (WeakInitCont path): 0
      All critical-path gaps closed.

    INDEPENDENT:
      NS_StokesMaxReg_OPEN s  (Hieber-Pruss, 6-18 months, NOT on WeakInitCont critical path)

    CERT STATUS: NS_TOWER_WEAKINITCONT_CLOSED
    NS Clay Surface #1: LOCKED OPEN (independent of WeakInitCont; Clay NS asks about
      global regularity, not merely weak continuity at t=0).

    AXIOM FOOTPRINT:
      #print axioms ns_weakInitCont_phase89 =
        {propext, Classical.choice, Quot.sound}

    NOTE ON DAVID'S T0 SKETCH:
      David proposed energy_ineq_continuous_at_zero for NS_AdjointInnerDerivMap_T0_OPEN.
      This addresses L² continuity of u(t) at t=0 — a true but DIFFERENT statement.
      The actual gap is a Fourier symbol identity; energy inequalities do not appear.
      The correct proof is MuIntegralShift at T=0 with corrSemSym(0,ξ) = 1.

    NS Clay Surface #1: LOCKED OPEN.  No Clay Millennium Prize claim. -/
theorem phase89_gap_accounting : True := trivial

end TheoremaAureum.Towers.NS.Phase89AdjointClose
