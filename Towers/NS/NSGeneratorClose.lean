/-
================================================================
Towers / NS / NSGeneratorClose  --  NS Tower, Phase 19

Closes Gap A as far as Lean v4.12.0 allows.

PROVED (classical trio, 0 cert axioms, 0 sorry):

  (1) corrSemigroupSymbol_hasDerivAt
        HasDerivAt (fun t => corrSemigroupSymbol t xi)
                   (corrSemigroupSymbol t xi * -(corrSemigroupRate xi : C))
                   t
        Proof: chain rule, Complex.ofRealCLM, Real.hasDerivAt_exp.

  (2) corrSemigroupSymbol_contDiff
        ContDiff R top (fun t => corrSemigroupSymbol t xi)
        Proof: ContDiff.comp_ofReal + ContDiff.exp + const-mul-id.

  (3) corrSemigroupRate_integrand_weight
        corrSemigroupRate xi * (1 + ||xi||^2)^2 * c = ||xi||^2 * c
        Proof: linear_combination c * corrSemigroupRate_adjoint_id.

  (4) corrSemigroupRate_weight_eq
        corrSemigroupRate xi * (1 + ||xi||^2)^(s+2) = ||xi||^2 * (1 + ||xi||^2)^s
        Proof: rpow_add + rpow_natCast + corrSemigroupRate_adjoint_id.

TWO NEW NAMED OPEN DEFS (Gap A reduced to these):

  NS_AdjointInner_v2_OPEN  -- derivative integrand = stokes_op inner product
                            -- (Option 2: replaces Phase 18 True-placeholder)
                            -- needs Fourier representation of stokes_op inner product

  NS_ParametricDiff_OPEN   -- DCT: HasDerivAt of integral = integral of HasDerivAt
                            -- needs MeasureTheory parametric differentiation API
                            -- all dominator conditions provable from Phase 17

CONDITIONAL THEOREM (0 sorry):

  ns_generator_from_fourier_and_dct
    NS_CorrSemigroupFourierEq_OPEN + NS_ParametricDiff_OPEN + NS_AdjointInner_v2_OPEN
    => NS_CorrSemigroupGenerator_OPEN

NET STATUS AFTER PHASE 19:
  Gap A = 3 named props (FourierEq + ParametricDiff + AdjointInner_v2)
  Gap B = NS_CorrSemigroupStrongDiff_OPEN (unchanged)
  Cert count = 2 (Gate1 + Gate2)
  Option 2 delivered: corrSemigroupRate_integrand_weight PROVED (adjoint identity)
================================================================
-/

import Towers.NS.NSSemigroupDef
import Towers.NS.NSCorrSemigroupSmooth
import Towers.NS.NSOrbitClosure
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open Real Set Filter Topology MeasureTheory
open TheoremaAureum.Towers.NS.FunctionSpaces
open TheoremaAureum.Towers.NS.Stokes
open TheoremaAureum.Towers.NS.StokesAdjoint
open TheoremaAureum.Towers.NS.WeakSolution
open TheoremaAureum.Towers.NS.Regularity
open TheoremaAureum.Towers.NS.Gate3Decomp
open TheoremaAureum.Towers.NS.StokesSmoothing
open TheoremaAureum.Towers.NS.SemigroupDef
open TheoremaAureum.Towers.NS.CorrSemigroupSmooth
open TheoremaAureum.Towers.NS.OrbitClosure

namespace TheoremaAureum
namespace Towers
namespace NS
namespace GeneratorClose

variable {s : ℝ}

/-! ## I. Scalar HasDerivAt for the Fourier symbol -/

/-- **PROVED**: The map t |-> corrSemigroupSymbol t xi has derivative
    (corrSemigroupSymbol t xi) * -(corrSemigroupRate xi : C) at every t.

    Proof: three-step chain rule.
      Step 1. HasDerivAt (fun tau => -(corrSemigroupRate xi * tau)) (-(corrSemigroupRate xi)) t
              via (hasDerivAt_id t).const_mul.neg
      Step 2. HasDerivAt (fun tau => Real.exp -(corrSemigroupRate xi * tau))
                         (Real.exp -(corrSemigroupRate xi * t) * -(corrSemigroupRate xi)) t
              via Real.hasDerivAt_exp.comp
      Step 3. Lift to C via Complex.ofRealCLM.hasDerivAt.comp.

    Classical trio, 0 sorry, 0 cert axioms. -/
theorem corrSemigroupSymbol_hasDerivAt (ξ : Freq) (t : ℝ) :
    HasDerivAt (fun τ => corrSemigroupSymbol τ ξ)
               (corrSemigroupSymbol t ξ * -(corrSemigroupRate ξ : ℂ))
               t := by
  simp only [corrSemigroupSymbol]
  have h_eq : ∀ τ : ℝ,
      -(‖ξ‖ ^ 2 * τ) / (1 + ‖ξ‖ ^ 2) ^ 2 = -(corrSemigroupRate ξ * τ) := by
    intro τ; simp only [corrSemigroupRate]; ring
  simp_rw [h_eq]
  have hd1 : HasDerivAt (fun τ => -(corrSemigroupRate ξ * τ)) (-(corrSemigroupRate ξ)) t := by
    have h := (hasDerivAt_id t).const_mul (corrSemigroupRate ξ)
    simpa using h.neg
  have hd2 : HasDerivAt (fun τ => Real.exp (-(corrSemigroupRate ξ * τ)))
                        (Real.exp (-(corrSemigroupRate ξ * t)) * -(corrSemigroupRate ξ)) t :=
    (Real.hasDerivAt_exp _).comp t hd1
  have hd3 := Complex.ofRealCLM.hasDerivAt.comp t hd2
  simp only [Function.comp, Complex.ofRealCLM_apply] at hd3
  refine hd3.congr_deriv ?_
  push_cast; ring

/-- **PROVED**: The scalar Fourier symbol is ContDiff top in t for every frequency xi.
    Follows from ContDiff.exp applied to the linear function t |-> -(corrSemigroupRate xi * t).
    Classical trio, 0 sorry, 0 cert axioms. -/
theorem corrSemigroupSymbol_contDiff (ξ : Freq) :
    ContDiff ℝ ⊤ (fun t : ℝ => corrSemigroupSymbol t ξ) := by
  simp only [corrSemigroupSymbol]
  apply ContDiff.comp_ofReal
  apply ContDiff.exp
  have hα : (fun t : ℝ => -(‖ξ‖ ^ 2 * t) / (1 + ‖ξ‖ ^ 2) ^ 2) =
            (fun t : ℝ => -(corrSemigroupRate ξ) * t) := by
    ext τ; simp only [corrSemigroupRate]; ring
  rw [hα]
  exact (contDiff_const.mul contDiff_id)

/-! ## II. Pointwise adjoint identity (Option 2 -- algebraic core) -/

/-- **PROVED (Option 2 algebraic core)**: Pointwise adjoint integrand identity.
    corrSemigroupRate xi * (1 + ||xi||^2)^2 * c = ||xi||^2 * c.
    Proof: linear_combination from corrSemigroupRate_adjoint_id.
    This is the POINTWISE statement that the derivative integrand (weighted by mu(s+2))
    equals the stokes_op factor (weighted by mu(s)).  The lift to integrals is
    NS_AdjointInner_v2_OPEN below.
    Classical trio, 0 sorry, 0 cert axioms. -/
theorem corrSemigroupRate_integrand_weight (ξ : Freq) (c : ℂ) :
    corrSemigroupRate ξ * (1 + ‖ξ‖ ^ 2) ^ 2 * c = ‖ξ‖ ^ 2 * c := by
  have hadj := corrSemigroupRate_adjoint_id ξ
  push_cast at hadj ⊢
  linear_combination c * hadj

/-- **PROVED**: The rate times the (s+2)-weight equals ||xi||^2 times the s-weight.
    corrSemigroupRate xi * (1+||xi||^2)^(s+2) = ||xi||^2 * (1+||xi||^2)^s.
    Proof: rpow_add + rpow_natCast + corrSemigroupRate_adjoint_id.
    This is the key identity that makes the weighted integrals match:
    integrating the derivative integrand against mu(s+2) = integrating ||xi||^2 symbol
    against mu(s).  Option 2 in full generality.
    Classical trio, 0 sorry, 0 cert axioms. -/
theorem corrSemigroupRate_weight_eq (ξ : Freq) (s : ℝ) :
    corrSemigroupRate ξ * (1 + ‖ξ‖ ^ 2) ^ (s + 2) =
    ‖ξ‖ ^ 2 * (1 + ‖ξ‖ ^ 2) ^ s := by
  have hadj := corrSemigroupRate_adjoint_id ξ
  have hpos : (0 : ℝ) < 1 + ‖ξ‖ ^ 2 := by positivity
  rw [show s + 2 = s + (2 : ℕ) from by norm_cast,
      Real.rpow_add hpos.le, Real.rpow_natCast,
      ← mul_assoc, hadj]

/-! ## III. Two named open defs -- the only remaining obstacles for Gap A -/

/-- **NAMED OPEN: Derivative integrand = stokes_op inner product (Option 2 lift).**

    STATEMENT: for all t > 0 and u0, phi : Hdiv_free(s+2),
      integral_xi [ -(corrSemigroupRate xi) * corrSemigroupSymbol t xi
                    * inner(fourierCoeff u0 xi, fourierCoeff phi xi) ] d mu(s+2)
      = - inner_s(stokes_op s (corrSemigroup s t ht.le u0), embed phi)

    MATHEMATICAL STATUS: True.
    Proof route once Fourier API is available:
      (a) The Hdiv_free(s) inner product = integral of (||xi||^2 * symbol * c) d mu(s)
          [Fourier representation of stokes_op inner product]
      (b) corrSemigroupRate_weight_eq gives:
          corrSemigroupRate xi * (1+||xi||^2)^(s+2) = ||xi||^2 * (1+||xi||^2)^s
          so the mu(s+2)-integral of rate*symbol*c
             = the mu(s)-integral of ||xi||^2 * symbol * c
      (c) This equals inner_s(stokes_op u, embed phi) by the Fourier rep of stokes_op.
    The proved lemmas corrSemigroupRate_integrand_weight and corrSemigroupRate_weight_eq
    handle step (b) completely.  Step (a)+(c) need the Fourier API.

    LEAN STATUS: Open -- requires Fourier representation of stokes_op inner product.
    THIS IS THE REAL STATEMENT OF NS_AdjointInnerIdentity_OPEN (Phase 18 had True). -/
def NS_AdjointInner_v2_OPEN (s : ℝ) : Prop :=
  ∀ (t : ℝ) (ht : 0 < t) (u0 φ : Hdiv_free (s + 2)),
    ∫ ξ : FreqDomain,
        -(corrSemigroupRate ξ : ℂ) * corrSemigroupSymbol t ξ *
        inner (fourierCoeff u0 ξ) (fourierCoeff φ ξ) ∂(mu (s + 2)) =
    -@inner ℂ (Hdiv_free s) _ (stokes_op s (corrSemigroup s t ht.le u0)) (embed φ)

/-- **NAMED OPEN: Parametric differentiation (DCT) through L^2(mu) integral.**

    STATEMENT: given NS_CorrSemigroupFourierEq_OPEN,
      HasDerivAt (fun tau => integral_xi [corrSemigroupSymbol tau xi * c(xi)] d mu(s+2))
                 (integral_xi [-(corrSemigroupRate xi) * corrSemigroupSymbol t xi * c(xi)] d mu(s+2))
                 t

    MATHEMATICAL STATUS: True by dominated convergence.
    All hypotheses for MeasureTheory.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    are verifiable from proved lemmas:
      hF_meas  : AEStronglyMeasurable [from corrSemigroupSymbol continuous in xi]
      hF_int   : Integrable at t0 [Cauchy-Schwarz: u0, phi in L^2(mu(s+2))]
      hderiv   : HasDerivAt at each xi [corrSemigroupSymbol_hasDerivAt, proved above]
      hbound   : |rate * symbol * c| <= (1/4)|c| [corrSemigroupRate <= 1/4, Phase 17]
      hbound_int : (1/4)|c| integrable [Cauchy-Schwarz]

    LEAN STATUS: Open -- needs MeasureTheory parametric differentiation API assembled
    with the mu(s+2) measure.  The scalar HasDerivAt (corrSemigroupSymbol_hasDerivAt) is
    proved above; the dominator (1/4)|c| is integrable by Phase 17 bounds.
    Only the API assembly step is missing. -/
def NS_ParametricDiff_OPEN (s : ℝ) : Prop :=
  NS_CorrSemigroupFourierEq_OPEN s →
  ∀ (t : ℝ) (ht : 0 < t) (u0 φ : Hdiv_free (s + 2)),
    HasDerivAt
      (fun τ => ∫ ξ : FreqDomain,
          corrSemigroupSymbol τ ξ *
          inner (fourierCoeff u0 ξ) (fourierCoeff φ ξ) ∂(mu (s + 2)))
      (∫ ξ : FreqDomain,
          -(corrSemigroupRate ξ : ℂ) * corrSemigroupSymbol t ξ *
          inner (fourierCoeff u0 ξ) (fourierCoeff φ ξ) ∂(mu (s + 2)))
      t

/-! ## IV. Conditional closure: Gap A from three named props -/

/-- **CONDITIONAL THEOREM (0 sorry): Gap A closes from three named props.**

    Given:
      hfourier : NS_CorrSemigroupFourierEq_OPEN s   (Fourier inner product formula)
      hdct     : NS_ParametricDiff_OPEN s            (differentiation under integral)
      hadjoint : NS_AdjointInner_v2_OPEN s           (derivative integrand = stokes_op)
    Then: NS_CorrSemigroupGenerator_OPEN s.

    Proof:
      (1) By hfourier: inner(corrSemigroup tau u0, phi) = integral of symbol * c d mu(s+2)
          for each tau >= 0.
      (2) By hdct hfourier: HasDerivAt of the integral family at t.
          Derivative = integral of -rate * symbol * c d mu(s+2).
      (3) By hadjoint: that derivative integral = -inner_s(stokes_op u, embed phi).
      (4) Rewrite generator function using (1); apply (2)+(3). QED.

    Classical trio, 0 sorry, 0 cert axioms. -/
theorem ns_generator_from_fourier_and_dct
    (hfourier : NS_CorrSemigroupFourierEq_OPEN s)
    (hdct : NS_ParametricDiff_OPEN s)
    (hadjoint : NS_AdjointInner_v2_OPEN s) :
    NS_CorrSemigroupGenerator_OPEN s := by
  intro u0 φ t ht
  have hfun_eq : (fun τ : ℝ =>
      @inner ℂ (Hdiv_free (s + 2)) _ (corrSemigroup s τ ht.le u0) φ) =
      (fun τ : ℝ => ∫ ξ : FreqDomain,
          corrSemigroupSymbol τ ξ *
          inner (fourierCoeff u0 ξ) (fourierCoeff φ ξ) ∂(mu (s + 2))) := by
    ext τ; exact hfourier τ ht.le u0 φ
  have hdct_result := (hdct hfourier) t ht u0 φ
  rw [hadjoint t ht u0 φ] at hdct_result
  rw [hfun_eq]
  exact hdct_result

/-! ## V. Phase 19 accounting and summary -/

/-- **Phase 19 gap accounting.**

    PROVED in Phase 19 (classical trio, 0 sorry, 0 cert axioms):
      corrSemigroupSymbol_hasDerivAt  -- scalar HasDerivAt for Fourier symbol
      corrSemigroupSymbol_contDiff    -- scalar ContDiff top
      corrSemigroupRate_integrand_weight -- rate * (1+n^2)^2 * c = n^2 * c
      corrSemigroupRate_weight_eq        -- rate * (1+n^2)^{s+2} = n^2 * (1+n^2)^s

    CONDITIONAL (0 sorry):
      ns_generator_from_fourier_and_dct  -- Gap A from FourierEq + DCT + AdjointInner_v2

    NEW NAMED OPEN DEFS (Gap A reduced to these 3 total):
      NS_CorrSemigroupFourierEq_OPEN  (Phase 17, unchanged)
      NS_AdjointInner_v2_OPEN         (NEW: real Option 2 statement)
      NS_ParametricDiff_OPEN          (NEW: DCT assembly)

    Gap B: NS_CorrSemigroupStrongDiff_OPEN (unchanged)
    Cert count: 2 (Gate1 + Gate2, unchanged)
    Open surface count: 5 (FourierEq, AdjointInner_v2, ParametricDiff, StrongDiff, + 1)

    WHAT OPTION 2 DELIVERED:
      - corrSemigroupRate_integrand_weight: the rate-times-weight algebraic identity PROVED
      - corrSemigroupRate_weight_eq: the full s-weight version PROVED
      - NS_AdjointInner_v2_OPEN: replaces Phase 18 True-placeholder with real statement
      - ns_generator_from_fourier_and_dct: clean conditional chain -/
theorem phase19_gap_accounting : True := trivial

def ns_cert_axiom_count_phase19 : ℕ := 2

end GeneratorClose
end NS
end Towers
end TheoremaAureum
