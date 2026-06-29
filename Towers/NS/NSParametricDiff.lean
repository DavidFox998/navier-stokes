/-
================================================================
Towers / NS / NSParametricDiff  --  Phase 22: NS Tower

Closes Gap A completely.

PROVED (classical trio, 0 sorry, 0 cert axioms):
  corrSemigroupSymbol_continuous_xi  -- Continuous (fun xi => symbol t xi) for fixed t
  corrSemigroupSymbol_norm_le_one    -- ||symbol t xi|| <= 1 for t >= 0
  inner_fourierCoeff_integrable      -- L^2 Holder: inner(u0 xi, phi xi) in L^1
  adjoint_integrand_integrable       -- -(rate:C)*symbol*inner is L^1
  NS_ParametricDiff_PROVED           -- DCT: HasDerivAt under mu(s+2) integral
  NS_AdjointInner_v2_PROVED          -- from Phase 21 conditional + integrability
  NS_CorrSemigroupGenerator_PROVED   -- GAP A CLOSED

MATHEMATICAL CONTENT:
  Parametric differentiation via:
    hasDerivAt_integral_of_dominated_loc_of_deriv_le  (Mathlib)
  F  tau xi := corrSemigroupSymbol tau xi * inner(u0 xi, phi xi)
  F'     xi := -(rate xi : C) * symbol t xi * inner(u0 xi, phi xi)
  bound  xi := (1/4) * ||inner(u0 xi, phi xi)||

  Dominator (for hF'_bound):
    |F' xi| = rate xi * ||symbol t xi|| * ||c xi||
              <= (1/4) * 1 * ||c xi||       [rate <= 1/4, |symbol| <= 1]
  Integrability of bound (hbound):
    L2.integrable_inner: inner product of two L^2 functions is L^1
  Pointwise HasDerivAt (hF_deriv):
    (corrSemigroupSymbol_hasDerivAt xi t).mul_const c  (Phase 19)

  Gap A chain (Phase 22 closure):
    NS_CorrSemigroupFourierEq_PROVED  (Phase 20)
    NS_ParametricDiff_PROVED          (Phase 22)
    NS_AdjointInner_v2_PROVED         (Phase 22)
    => ns_generator_from_fourier_and_dct  (Phase 19)
    => NS_CorrSemigroupGenerator_PROVED

Author: David Fox | Date: May 21, 2026
Series: Opera Numerorum (internal: Battle Plan v1.6)
================================================================
-/

import Towers.NS.NSMuIntegralShift
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Function.L2Space

open Real Set Filter Topology MeasureTheory
open scoped BigOperators ENNReal
open TheoremaAureum.Towers.NS.FunctionSpaces
open TheoremaAureum.Towers.NS.Stokes
open TheoremaAureum.Towers.NS.StokesAdjoint
open TheoremaAureum.Towers.NS.SemigroupDef
open TheoremaAureum.Towers.NS.GeneratorClose
open TheoremaAureum.Towers.NS.OrbitClosure
open TheoremaAureum.Towers.NS.FourierInner
open TheoremaAureum.Towers.NS.MuIntegralShift
open NSTower

namespace TheoremaAureum
namespace Towers
namespace NS
namespace ParametricDiff

variable {s : ℝ}

/-! ## I. Continuity of corrSemigroupSymbol in the frequency variable -/

/-- corrSemigroupSymbol t is continuous in xi for each fixed t.

    Proof: corrSemigroupSymbol t xi = Complex.exp(-(corrSemigroupRate xi * t) : R)
    as a composition of continuous functions:
      xi |-> ||xi||^2 / (1+||xi||^2)^2    (rational of norm, denom > 0)
      r  |-> -(r * t)                       (linear, continuous)
      x  |-> Real.exp x                     (continuous)
      r  |-> (r : C)                        (Complex.ofReal, continuous)

    Used to establish AEStronglyMeasurability of F t for the DCT theorem. -/
theorem corrSemigroupSymbol_continuous_xi (t : ℝ) :
    Continuous (fun ξ : FreqDomain => corrSemigroupSymbol t ξ) := by
  simp only [corrSemigroupSymbol, corrSemigroupRate]
  apply Continuous.comp Complex.continuous_ofReal
  apply Real.continuous_exp.comp
  apply Continuous.neg
  apply Continuous.mul_const
  exact (continuous_norm.pow 2).div
    ((continuous_const.add (continuous_norm.pow 2)).pow 2)
    (fun ξ => pow_ne_zero 2 (ne_of_gt (by positivity)))

/-! ## II. Norm bound on corrSemigroupSymbol -/

/-- ||corrSemigroupSymbol t xi|| <= 1 for all t >= 0 and xi.

    Proof: corrSemigroupSymbol t xi = (exp(-(rate xi * t)) : C),
    rate xi >= 0 and t >= 0 give rate xi * t >= 0,
    so -(rate xi * t) <= 0, hence exp(-rate xi * t) <= exp 0 = 1.

    Key bound for both hF_int and hF'_bound in the DCT theorem. -/
theorem corrSemigroupSymbol_norm_le_one {t : ℝ} (ht : 0 ≤ t) (ξ : FreqDomain) :
    ‖corrSemigroupSymbol t ξ‖ ≤ 1 := by
  simp only [corrSemigroupSymbol, corrSemigroupRate, Complex.norm_exp, Complex.ofReal_re]
  exact Real.exp_le_one_of_nonpos (neg_nonpos.mpr
    (mul_nonneg (div_nonneg (by positivity) (by positivity)) ht))

/-! ## III. Integrability of the inner product of two L^2 functions -/

/-- The pointwise inner product of two L^2(mu) functions is L^1-integrable.

    Proof: Holder inequality for L^2 pairs:
      ||inner(u0 xi, phi xi)|| <= ||u0 xi|| * ||phi xi||  (Cauchy-Schwarz pointwise)
      Int ||u0 xi|| * ||phi xi|| dmu <= ||u0||_{L^2} * ||phi||_{L^2} < inf  (Holder)
    Accessed via L2.integrable_inner from Mathlib.MeasureTheory.Function.L2Space.

    This is the key integrability fact underlying both ParametricDiff (hbound,
    hF_int) and AdjointInner_v2 (adjoint_integrand_integrable below). -/
theorem inner_fourierCoeff_integrable (u0 φ : Hdiv_free (s + 2)) :
    Integrable (fun ξ : FreqDomain =>
      @inner ℂ Val _ (fourierCoeff u0 ξ) (fourierCoeff φ ξ)) (mu (s + 2)) :=
  L2.integrable_inner
    (u0 : Lp Val 2 (mu (s + 2)))
    (φ : Lp Val 2 (mu (s + 2)))

/-! ## IV. Integrability of the adjoint integrand -/

/-- The adjoint integrand -(rate xi : C) * symbol t xi * inner(u0 xi, phi xi)
    is L^1-integrable w.r.t. mu(s+2).

    Proof: pointwise bound by (1/4) * ||inner(u0 xi, phi xi)||:
      |-(rate xi : C) * symbol t xi * c xi|
        = rate xi * ||symbol t xi|| * ||c xi||
        <= (1/4) * 1 * ||c xi||    [corr_symbol_le_quarter, corrSemigroupSymbol_norm_le_one]
    Then Integrable.mono from inner_fourierCoeff_integrable.

    This supplies the `hint` hypothesis to NS_AdjointInner_v2_from_mushift (Phase 21). -/
theorem adjoint_integrand_integrable
    (t : ℝ) (ht : 0 < t) (u0 φ : Hdiv_free (s + 2)) :
    Integrable (fun ξ : Freq =>
      -(corrSemigroupRate ξ : ℂ) * corrSemigroupSymbol t ξ *
      @inner ℂ Val _ (fourierCoeff u0 ξ) (fourierCoeff φ ξ)) (mu (s + 2)) := by
  have h_c_int : Integrable
      (fun ξ : Freq => @inner ℂ Val _ (fourierCoeff u0 ξ) (fourierCoeff φ ξ))
      (mu (s + 2)) :=
    inner_fourierCoeff_integrable u0 φ
  have h_rate_cont : Continuous (fun ξ : FreqDomain => (corrSemigroupRate ξ : ℂ)) := by
    apply Continuous.comp Complex.continuous_ofReal
    simp only [corrSemigroupRate]
    exact (continuous_norm.pow 2).div
      ((continuous_const.add (continuous_norm.pow 2)).pow 2)
      (fun ξ => pow_ne_zero 2 (ne_of_gt (by positivity)))
  apply h_c_int.mono
  · exact (h_rate_cont.neg.mul (corrSemigroupSymbol_continuous_xi t)
      ).aestronglyMeasurable.mul h_c_int.1
  · filter_upwards with ξ
    have h1 : corrSemigroupRate ξ ≤ 1 / 4 := corr_symbol_le_quarter ξ
    have h2 : ‖corrSemigroupSymbol t ξ‖ ≤ 1 := corrSemigroupSymbol_norm_le_one ht.le ξ
    have h3 : 0 ≤ corrSemigroupRate ξ := by simp only [corrSemigroupRate]; positivity
    have h5 : 0 ≤ ‖@inner ℂ Val _ (fourierCoeff u0 ξ) (fourierCoeff φ ξ)‖ := norm_nonneg _
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, abs_of_nonneg h3]
    calc corrSemigroupRate ξ * ‖corrSemigroupSymbol t ξ‖ *
          ‖@inner ℂ Val _ (fourierCoeff u0 ξ) (fourierCoeff φ ξ)‖
        ≤ (1 / 4) * 1 * ‖@inner ℂ Val _ (fourierCoeff u0 ξ) (fourierCoeff φ ξ)‖ := by
          apply mul_le_mul_of_nonneg_right _ h5
          exact mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)
      _ ≤ ‖@inner ℂ Val _ (fourierCoeff u0 ξ) (fourierCoeff φ ξ)‖ := by
          nlinarith

/-! ## V. NS_ParametricDiff: DCT differentiation under the integral -/

/-- **Phase 22: NS_ParametricDiff_PROVED (0 sorry, classical trio).**

    Closes NS_ParametricDiff_OPEN from NSGeneratorClose.lean.

    Given NS_CorrSemigroupFourierEq_OPEN s (hypothesis; not used in this proof,
    present only because NS_ParametricDiff_OPEN carries it as a Prop → Prop),
    proves HasDerivAt of the mu(s+2)-Fourier inner product integral.

    PROOF: hasDerivAt_integral_of_dominated_loc_of_deriv_le with delta=1:
      F  tau xi  := corrSemigroupSymbol tau xi * c xi
      F'     xi  := -(rate xi : C) * corrSemigroupSymbol t xi * c xi
      bound  xi  := (1/4) * ||c xi||
    where c xi = inner(fourierCoeff u0 xi, fourierCoeff phi xi).

    Conditions:
      hF_meas   -- continuous * AEMeas = AEMeas
      hF_int    -- ||symbol t xi|| <= 1 -> Integrable c -> Integrable (F t)
      hF'_meas  -- product of continuous functions, AEMeas
      hbound    -- Integrable c.norm * (1/4)
      hF'_bound -- rate <= 1/4 and |symbol| <= 1 give ||F' xi|| <= (1/4)||c xi||
      hF_deriv  -- (corrSemigroupSymbol_hasDerivAt xi t).mul_const c

    #print axioms NS_ParametricDiff_PROVED = classical trio. -/
theorem NS_ParametricDiff_PROVED : NS_ParametricDiff_OPEN s := by
  intro _hfourier t ht u0 φ
  set c : FreqDomain → ℂ :=
    fun ξ => @inner ℂ Val _ (fourierCoeff u0 ξ) (fourierCoeff φ ξ)
  have h_c_int : Integrable c (mu (s + 2)) := inner_fourierCoeff_integrable u0 φ
  have h_rate_cont : Continuous (fun ξ : FreqDomain => (corrSemigroupRate ξ : ℂ)) := by
    apply Continuous.comp Complex.continuous_ofReal
    simp only [corrSemigroupRate]
    exact (continuous_norm.pow 2).div
      ((continuous_const.add (continuous_norm.pow 2)).pow 2)
      (fun ξ => pow_ne_zero 2 (ne_of_gt (by positivity)))
  apply hasDerivAt_integral_of_dominated_loc_of_deriv_le (δ := 1) one_pos
  · -- hF_meas
    intro τ _hτ
    exact (corrSemigroupSymbol_continuous_xi τ).aestronglyMeasurable.mul h_c_int.1
  · -- hF_int: Integrable (fun xi => symbol t xi * c xi) at t
    apply h_c_int.mono
      ((corrSemigroupSymbol_continuous_xi t).aestronglyMeasurable.mul h_c_int.1)
    filter_upwards with ξ
    calc ‖corrSemigroupSymbol t ξ * c ξ‖
        = ‖corrSemigroupSymbol t ξ‖ * ‖c ξ‖ := norm_mul _ _
      _ ≤ 1 * ‖c ξ‖ :=
          mul_le_mul_of_nonneg_right (corrSemigroupSymbol_norm_le_one ht.le ξ) (norm_nonneg _)
      _ = ‖c ξ‖ := one_mul _
  · -- hF'_meas: AEStronglyMeasurable of F' (the derivative integrand)
    exact (h_rate_cont.neg.mul (corrSemigroupSymbol_continuous_xi t)
      ).aestronglyMeasurable.mul h_c_int.1
  · -- hbound: (1/4) * ||c xi|| is integrable
    exact h_c_int.norm.const_mul (1 / 4)
  · -- hF'_bound: ||F' xi|| <= (1/4) * ||c xi|| for all tau in ball t 1
    intro τ _hτ
    filter_upwards with ξ
    have h1 : corrSemigroupRate ξ ≤ 1 / 4 := corr_symbol_le_quarter ξ
    have h2 : ‖corrSemigroupSymbol t ξ‖ ≤ 1 := corrSemigroupSymbol_norm_le_one ht.le ξ
    have h3 : 0 ≤ corrSemigroupRate ξ := by simp only [corrSemigroupRate]; positivity
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, abs_of_nonneg h3]
    calc corrSemigroupRate ξ * ‖corrSemigroupSymbol t ξ‖ * ‖c ξ‖
        ≤ (1 / 4) * 1 * ‖c ξ‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          exact mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)
      _ = 1 / 4 * ‖c ξ‖ := by ring
  · -- hF_deriv: pointwise HasDerivAt via corrSemigroupSymbol_hasDerivAt * mul_const
    filter_upwards with ξ
    have hd := (corrSemigroupSymbol_hasDerivAt ξ t).mul_const (c ξ)
    exact hd.congr_deriv (by ring)

/-! ## VI. Closing NS_AdjointInner_v2_OPEN -/

/-- **NS_AdjointInner_v2_PROVED (Phase 22, 0 sorry, classical trio).**

    Supplies adjoint_integrand_integrable to NS_AdjointInner_v2_from_mushift
    (Phase 21, conditional), closing NS_AdjointInner_v2_OPEN unconditionally.

    The integrability is proved by Holder for L^2 pairs + symbol bound <= 1/4. -/
theorem NS_AdjointInner_v2_PROVED : NS_AdjointInner_v2_OPEN s :=
  NS_AdjointInner_v2_from_mushift adjoint_integrand_integrable

/-! ## VII. Closing NS_CorrSemigroupGenerator_OPEN (Gap A) -/

/-- **Phase 22: NS_CorrSemigroupGenerator_PROVED (0 sorry, classical trio).**

    CLOSES NS_CorrSemigroupGenerator_OPEN = Gap A of the NS Tower.

    Full closure chain:
      NS_CorrSemigroupFourierEq_PROVED (Phase 20) : FourierEq holds
      NS_ParametricDiff_PROVED         (Phase 22) : HasDerivAt of Fourier integral
      NS_AdjointInner_v2_PROVED        (Phase 22) : adjoint inner identity holds
      ns_generator_from_fourier_and_dct (Phase 19) : logical combinator
      => NS_CorrSemigroupGenerator_PROVED

    #print axioms NS_CorrSemigroupGenerator_PROVED = classical trio. -/
theorem NS_CorrSemigroupGenerator_PROVED : NS_CorrSemigroupGenerator_OPEN s :=
  ns_generator_from_fourier_and_dct
    NS_CorrSemigroupFourierEq_PROVED
    NS_ParametricDiff_PROVED
    NS_AdjointInner_v2_PROVED

/-! ## VIII. Phase 22 gap accounting -/

/-- **Phase 22 gap accounting (0 sorry throughout).**

    PROVED in Phase 22 (classical trio, 0 cert axioms):
      corrSemigroupSymbol_continuous_xi  -- xi-continuity of the Fourier symbol
      corrSemigroupSymbol_norm_le_one    -- ||symbol t xi|| <= 1 for t >= 0
      inner_fourierCoeff_integrable      -- L^2 Holder: inner product is L^1
      adjoint_integrand_integrable       -- -(rate:C)*symbol*inner is L^1
      NS_ParametricDiff_PROVED           -- DCT HasDerivAt under mu(s+2)
      NS_AdjointInner_v2_PROVED          -- closes NS_AdjointInner_v2_OPEN
      NS_CorrSemigroupGenerator_PROVED   -- GAP A CLOSED

    GAP STATUS AFTER PHASE 22:
      Gap A: NS_CorrSemigroupGenerator_OPEN  -- CLOSED (Phase 22)
      Gap B: NS_CorrSemigroupStrongDiff_OPEN -- OPEN (Bochner ODE regularity; HARD)
             ETA: 6-12 months Mathlib development (absent from v4.12.0)

    CONDITIONAL CHAIN (all 0 sorry, Gap B is now the only remaining Lean gap):
      Gap B + huniq => NS_SemigroupClosed_OPEN     [Phase 16]
      SemigroupClosed => NS_LocalRegularity_OPEN   [ns_semigroup_implies_localreg]

    Cert count: 2 (Gate1 + Gate2, unchanged).
    NS Clay Surface #1: LOCKED OPEN. No Clay claim. -/
theorem phase22_gap_accounting : True := trivial

end ParametricDiff
end NS
end Towers
end TheoremaAureum
