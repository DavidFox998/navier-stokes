/-
================================================================
Towers / NS / NSParametricDiff  --  Phase 22: NS Tower

Closes NS_ParametricDiff_OPEN (DCT through L^2(mu) integral)
and NS_CorrSemigroupGenerator_OPEN (Gap A fully closed).

PROVED (classical trio, 0 sorry, 0 cert axioms):

  (1) NS_ParametricDiff_PROVED : NS_ParametricDiff_OPEN s
        Proof: hasDerivAt_integral_of_dominated_loc_of_deriv_le
          with epsilon = t/2 > 0.  Interval Ioo (t/2) (3t/2) lies in (0,infty)
          so corrSemigroupSymbol_norm_le applies uniformly.
          Dominator: (1/4)*||inner||; integrable by L2.inner_integrable + const_mul.

  (2) NS_AdjointInner_v2_PROVED : NS_AdjointInner_v2_OPEN s
        Proof: NS_AdjointInner_v2_from_mushift with the integrability proved below.

  (3) NS_CorrSemigroupGenerator_PROVED : NS_CorrSemigroupGenerator_OPEN s
        Proof: ns_generator_from_fourier_and_dct combining Phases 20-22.

KEY HELPER LEMMAS (all 0 sorry, classical trio):
  symbol_inner_aesm           -- AESM of corrSymbol * inner
  symbol_inner_integrable     -- Integrable at t >= 0 via symbol norm <= 1
  adjoint_integrand_integrable -- Integrable of -rate*symbol*inner via rate <= 1/4
  corrSemigroupRate_continuous -- Continuity of xi |-> corrSemigroupRate xi

EPSILON CHOICE: epsilon = t/2 ensures the dominator interval Ioo (t/2) (3t/2)
stays strictly positive, so corrSemigroupSymbol_norm_le (x hx_pos.le xi) applies.

GAP REDUCTION after Phase 22:
  Gap A: FULLY CLOSED.  All three named props proved.
  Gap B: NS_CorrSemigroupStrongDiff_OPEN unchanged (Bochner ODE regularity).
  Cert count: 2 (Gate1 + Gate2).
  NS Clay Surface #1: LOCKED OPEN.  No Clay claim.

Author: David Fox | Date: May 21, 2026
Series: Opera Numerorum (internal: Battle Plan v1.6)
================================================================
-/

import Towers.NS.NSMuIntegralShift
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Function.L2Space

open Real Set Filter Topology MeasureTheory
open scoped BigOperators ENNReal NNReal
open TheoremaAureum.Towers.NS.FunctionSpaces
open TheoremaAureum.Towers.NS.SemigroupDef
open TheoremaAureum.Towers.NS.CorrSemigroupSmooth
open TheoremaAureum.Towers.NS.GeneratorClose
open TheoremaAureum.Towers.NS.FourierInner
open TheoremaAureum.Towers.NS.MuIntegralShift
open NSTower

namespace TheoremaAureum
namespace Towers
namespace NS
namespace ParametricDiff

variable {s : ℝ}

/-! ## I. Continuity of corrSemigroupRate -/

/-- corrSemigroupRate is continuous: xi |-> ||xi||^2 / (1 + ||xi||^2)^2.
    Proof: continuous numerator and positive continuous denominator.
    Classical trio, 0 sorry, 0 cert axioms. -/
private lemma corrSemigroupRate_continuous : Continuous (corrSemigroupRate : Freq -> ℝ) := by
  unfold corrSemigroupRate
  apply Continuous.div
  · exact continuous_norm.pow 2
  · exact (continuous_const.add (continuous_norm.pow 2)).pow 2
  · intro xi; positivity

/-! ## II. AEStronglyMeasurable of the Fourier integrand -/

/-- AEStronglyMeasurable of (fun xi => corrSemigroupSymbol tau xi * inner u0_xi phi_xi).
    Proof: product of continuous symbol (AESM) with inner of Lp representatives (AESM).
    Classical trio, 0 sorry, 0 cert axioms. -/
private lemma symbol_inner_aesm (τ : ℝ) (u0 φ : Hdiv_free (s + 2)) :
    AEStronglyMeasurable (fun ξ : Freq =>
        corrSemigroupSymbol τ ξ *
        @inner ℂ Val _ (fourierCoeff u0 ξ) (fourierCoeff φ ξ))
      (mu (s + 2)) := by
  apply AEStronglyMeasurable.mul
  · exact (continuous_corrSemigroupSymbol τ).aestronglyMeasurable
  · apply AEStronglyMeasurable.inner
    · exact Lp.aestronglyMeasurable (u0 : Lp Val 2 (mu (s + 2)))
    · exact Lp.aestronglyMeasurable (φ : Lp Val 2 (mu (s + 2)))

/-! ## III. Integrability of the Fourier integrand at t >= 0 -/

/-- Inner product of L2 functions is integrable.
    Proof: L2.inner_integrable from Mathlib.MeasureTheory.Function.L2Space.
    Classical trio, 0 sorry, 0 cert axioms. -/
private lemma fourierCoeff_inner_integrable (u0 φ : Hdiv_free (s + 2)) :
    Integrable (fun ξ : Freq =>
        @inner ℂ Val _ (fourierCoeff u0 ξ) (fourierCoeff φ ξ))
      (mu (s + 2)) :=
  MeasureTheory.L2.inner_integrable
    (u0 : Lp Val 2 (mu (s + 2))) (φ : Lp Val 2 (mu (s + 2)))

/-- Integrable (fun xi => corrSemigroupSymbol t xi * inner ...) for t >= 0.
    Proof: bound by ||inner|| using symbol norm <= 1; use fourierCoeff_inner_integrable.
    Classical trio, 0 sorry, 0 cert axioms. -/
private lemma symbol_inner_integrable (t : ℝ) (ht : 0 ≤ t) (u0 φ : Hdiv_free (s + 2)) :
    Integrable (fun ξ : Freq =>
        corrSemigroupSymbol t ξ *
        @inner ℂ Val _ (fourierCoeff u0 ξ) (fourierCoeff φ ξ))
      (mu (s + 2)) := by
  apply (fourierCoeff_inner_integrable u0 φ).mono (symbol_inner_aesm t u0 φ)
  apply Filter.eventually_of_forall; intro ξ
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (corrSemigroupSymbol_norm_le t ht ξ)

/-! ## IV. Integrability of the adjoint/derivative integrand -/

/-- Integrable (fun xi => -(rate xi : C) * symbol t xi * inner ...) for t > 0.
    Proof: norm <= (1/4) * ||inner|| by rate <= 1/4 and symbol norm <= 1;
    bound integrable: (1/4) * L2.inner_integrable.
    Classical trio, 0 sorry, 0 cert axioms. -/
private lemma adjoint_integrand_integrable (t : ℝ) (ht : 0 < t)
    (u0 φ : Hdiv_free (s + 2)) :
    Integrable (fun ξ : Freq =>
        -(corrSemigroupRate ξ : ℂ) * corrSemigroupSymbol t ξ *
        @inner ℂ Val _ (fourierCoeff u0 ξ) (fourierCoeff φ ξ))
      (mu (s + 2)) := by
  have h_aesm : AEStronglyMeasurable (fun ξ : Freq =>
        -(corrSemigroupRate ξ : ℂ) * corrSemigroupSymbol t ξ *
        @inner ℂ Val _ (fourierCoeff u0 ξ) (fourierCoeff φ ξ)) (mu (s + 2)) := by
    apply AEStronglyMeasurable.mul
    · apply AEStronglyMeasurable.mul
      · exact (Complex.continuous_ofReal.comp corrSemigroupRate_continuous).neg
          .aestronglyMeasurable
      · exact (continuous_corrSemigroupSymbol t).aestronglyMeasurable
    · apply AEStronglyMeasurable.inner
      · exact Lp.aestronglyMeasurable (u0 : Lp Val 2 (mu (s + 2)))
      · exact Lp.aestronglyMeasurable (φ : Lp Val 2 (mu (s + 2)))
  -- Bound: ||f_adj xi|| <= (1/4) * ||inner xi||
  have h_bound_int : Integrable (fun ξ : Freq =>
        (1 / 4 : ℝ) * ‖@inner ℂ Val _ (fourierCoeff u0 ξ) (fourierCoeff φ ξ)‖)
      (mu (s + 2)) :=
    (fourierCoeff_inner_integrable u0 φ).norm.const_mul (1 / 4)
  apply h_bound_int.mono h_aesm
  apply Filter.eventually_of_forall; intro ξ
  have hrate_nn : 0 ≤ corrSemigroupRate ξ := div_nonneg (by positivity) (by positivity)
  -- ||-(rate xi : C) * symbol t xi * inner|| <= (1/4) * ||inner||
  calc ‖-(corrSemigroupRate ξ : ℂ) * corrSemigroupSymbol t ξ *
        @inner ℂ Val _ (fourierCoeff u0 ξ) (fourierCoeff φ ξ)‖
      = corrSemigroupRate ξ * ‖corrSemigroupSymbol t ξ‖ *
        ‖@inner ℂ Val _ (fourierCoeff u0 ξ) (fourierCoeff φ ξ)‖ := by
          rw [norm_mul, norm_mul, map_neg, norm_neg, Complex.norm_real,
              Real.norm_of_nonneg hrate_nn]
    _ ≤ corrSemigroupRate ξ * 1 *
        ‖@inner ℂ Val _ (fourierCoeff u0 ξ) (fourierCoeff φ ξ)‖ := by
          gcongr; exact corrSemigroupSymbol_norm_le t ht.le ξ
    _ ≤ (1 / 4) *
        ‖@inner ℂ Val _ (fourierCoeff u0 ξ) (fourierCoeff φ ξ)‖ := by
          gcongr; linarith [corr_symbol_le_quarter ξ]
    _ = (1 / 4 : ℝ) * ‖@inner ℂ Val _ (fourierCoeff u0 ξ) (fourierCoeff φ ξ)‖ := by
          norm_cast

/-! ## V. Main DCT theorem: NS_ParametricDiff_PROVED -/

/-- **Phase 22: NS_ParametricDiff_PROVED (0 sorry, classical trio).**

    Proves NS_ParametricDiff_OPEN s via Bochner parametric differentiation.

    Epsilon = t/2 (strictly positive since ht : 0 < t).
    The dominator interval Ioo (t - t/2) (t + t/2) = Ioo (t/2) (3t/2) lies in (0,infty).
    Hence corrSemigroupSymbol_norm_le applies at every x in the interval.

    Six DCT conditions (hasDerivAt_integral_of_dominated_loc_of_deriv_le):
      hF_meas   : symbol_inner_aesm, eventually_of_forall
      hF_int    : symbol_inner_integrable at t with ht.le
      hF'_meas  : product of continuous (rate, symbol) and inner-AESM
      h_bound   : ||deriv (fun tau => symbol tau xi * c xi) x||
                  = corrSemigroupRate xi * ||symbol x xi|| * ||c xi||
                  <= 1/4 * ||c xi|| (rate<=1/4, symbol norm<=1 for x>0)
      bound_int : (1/4)*||inner|| integrable by const_mul + fourierCoeff_inner_integrable
      h_diff    : corrSemigroupSymbol_hasDerivAt.mul_const, congr_deriv by ring

    #print axioms NS_ParametricDiff_PROVED = classical trio. -/
theorem NS_ParametricDiff_PROVED : NS_ParametricDiff_OPEN s := by
  intro _hfourier t ht u0 φ
  -- abbreviate the inner product coefficient
  set c : Freq → ℂ :=
    fun ξ => @inner ℂ Val _ (fourierCoeff u0 ξ) (fourierCoeff φ ξ)
  -- Apply parametric differentiation under the Bochner integral
  apply hasDerivAt_integral_of_dominated_loc_of_deriv_le (ε := t / 2) (by linarith)
  · -- hF_meas: ∀ᶠ tau in nhds t, AEStronglyMeasurable (fun xi => symbol tau xi * c xi) mu
    exact Filter.eventually_of_forall (fun τ => symbol_inner_aesm τ u0 φ)
  · -- hF_int: Integrable (fun xi => symbol t xi * c xi) mu(s+2)
    exact symbol_inner_integrable t ht.le u0 φ
  · -- hF'_meas: AEStronglyMeasurable (fun xi => -(rate xi : C) * symbol t xi * c xi) mu
    apply AEStronglyMeasurable.mul
    · apply AEStronglyMeasurable.mul
      · exact (Complex.continuous_ofReal.comp corrSemigroupRate_continuous).neg
          .aestronglyMeasurable
      · exact (continuous_corrSemigroupSymbol t).aestronglyMeasurable
    · apply AEStronglyMeasurable.inner
      · exact Lp.aestronglyMeasurable (u0 : Lp Val 2 (mu (s + 2)))
      · exact Lp.aestronglyMeasurable (φ : Lp Val 2 (mu (s + 2)))
  · -- h_bound: for ae xi, all x in Ioo (t/2) (3t/2),
    --   ||deriv (fun tau => symbol tau xi * c xi) x|| <= (1/4) * ||c xi||
    apply Filter.eventually_of_forall; intro ξ x hx
    -- x > t/2 > 0
    have hx_pos : 0 < x := lt_trans (by linarith) hx.1
    -- HasDerivAt of the integrand at x
    have hd : HasDerivAt (fun τ => corrSemigroupSymbol τ ξ * c ξ)
                         (corrSemigroupSymbol x ξ * -(corrSemigroupRate ξ : ℂ) * c ξ) x :=
      ((corrSemigroupSymbol_hasDerivAt ξ x).mul_const (c ξ)).congr_deriv (by ring)
    rw [hd.deriv]
    have hrate_nn : 0 ≤ corrSemigroupRate ξ := div_nonneg (by positivity) (by positivity)
    calc ‖corrSemigroupSymbol x ξ * -(corrSemigroupRate ξ : ℂ) * c ξ‖
        = corrSemigroupRate ξ * ‖corrSemigroupSymbol x ξ‖ * ‖c ξ‖ := by
            rw [norm_mul, norm_mul, map_neg, norm_neg, Complex.norm_real,
                Real.norm_of_nonneg hrate_nn, mul_comm (‖corrSemigroupSymbol x ξ‖)]
      _ ≤ (1 / 4) * 1 * ‖c ξ‖ := by
            gcongr
            · exact corr_symbol_le_quarter ξ
            · exact corrSemigroupSymbol_norm_le x hx_pos.le ξ
      _ = 1 / 4 * ‖c ξ‖ := by ring
  · -- bound_integrable: (1/4) * ||c xi|| is integrable
    exact (fourierCoeff_inner_integrable u0 φ).norm.const_mul (1 / 4)
  · -- h_diff: HasDerivAt (fun tau => symbol tau xi * c xi) (F' xi) t at ae xi
    apply Filter.eventually_of_forall; intro ξ
    exact ((corrSemigroupSymbol_hasDerivAt ξ t).mul_const (c ξ)).congr_deriv (by ring)

/-! ## VI. NS_AdjointInner_v2_PROVED -/

/-- **Phase 22: NS_AdjointInner_v2_PROVED (0 sorry, classical trio).**

    Closes NS_AdjointInner_v2_OPEN by supplying adjoint_integrand_integrable
    to NS_AdjointInner_v2_from_mushift (Phase 21 conditional closure).

    The integrability is unconditional: proved from corr_symbol_le_quarter
    and L2.inner_integrable without any sorry.

    #print axioms NS_AdjointInner_v2_PROVED = classical trio. -/
theorem NS_AdjointInner_v2_PROVED : NS_AdjointInner_v2_OPEN s :=
  NS_AdjointInner_v2_from_mushift
    (fun t ht u0 φ => adjoint_integrand_integrable t ht u0 φ)

/-! ## VII. Gap A master closure: NS_CorrSemigroupGenerator_PROVED -/

/-- **Phase 22: NS_CorrSemigroupGenerator_PROVED (0 sorry, classical trio).**

    Closes Gap A (NS_CorrSemigroupGenerator_OPEN) unconditionally.

    Chain:
      NS_CorrSemigroupFourierEq_PROVED  (Phase 20)
      NS_ParametricDiff_PROVED          (Phase 22, this file)
      NS_AdjointInner_v2_PROVED         (Phase 22, this file)
    via ns_generator_from_fourier_and_dct (Phase 19 conditional combinator).

    After this: only Gap B remains (NS_CorrSemigroupStrongDiff_OPEN,
    Bochner ODE / Amann parabolic regularity, ~6-12 months Mathlib).

    #print axioms NS_CorrSemigroupGenerator_PROVED = classical trio. -/
theorem NS_CorrSemigroupGenerator_PROVED : NS_CorrSemigroupGenerator_OPEN s :=
  ns_generator_from_fourier_and_dct
    NS_CorrSemigroupFourierEq_PROVED
    NS_ParametricDiff_PROVED
    NS_AdjointInner_v2_PROVED

/-! ## VIII. Phase 22 gap accounting -/

/-- **Phase 22 gap accounting (0 sorry throughout).**

    PROVED in Phase 22 (classical trio, 0 cert axioms):
      NS_ParametricDiff_PROVED          -- closes NS_ParametricDiff_OPEN
      NS_AdjointInner_v2_PROVED         -- closes NS_AdjointInner_v2_OPEN
      NS_CorrSemigroupGenerator_PROVED  -- closes Gap A (NS_CorrSemigroupGenerator_OPEN)

    Phase 20-22 summary (classical trio, 0 cert axioms, 0 sorry):
      Phase 20: NS_CorrSemigroupFourierEq_PROVED
      Phase 21: NS_MuIntegralShift_PROVED + NS_AdjointInner_v2_from_mushift
      Phase 22: NS_ParametricDiff_PROVED + NS_AdjointInner_v2_PROVED
                + NS_CorrSemigroupGenerator_PROVED (GAP A CLOSED)

    REMAINING named gap (Gap B only):
      NS_CorrSemigroupStrongDiff_OPEN
        HasDerivAt in the Hdiv_free(s+2) Banach norm (not just scalar inner product)
        Requires Amann-type parabolic semigroup theory in Mathlib.
        ETA: 6-12 months.

    NS Clay Surface #1: LOCKED OPEN.  No Clay claim. -/
theorem phase22_gap_accounting : True := trivial

end ParametricDiff
end NS
end Towers
end TheoremaAureum
