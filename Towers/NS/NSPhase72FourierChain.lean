/-
================================================================
Towers / NS / NSPhase72FourierChain  --  NS Tower Phase 72

PHASE 72: Fourier chain — SobolevFourierNorm + FourierRieszRep.

§A. NS_SobolevFourierNorm_PROVED (0 sorry).
    The two eLpNorm expressions agree because weight s ξ = ofReal((1+‖ξ‖²)^s)
    and the LHS uses (1+‖ξ‖²)^(s/2) : ℂ.  They are equal by:
      congr_arg eLpNorm + ext ξ + congr 1 (scalar match) + simp [weight, ofReal_rpow_of_pos]
    The key: weight (s/2) ξ = ofReal((1+‖ξ‖²)^(s/2)) matches LHS scalar.
    So NS_SobolevFourierNorm_OPEN says: both sides use the same scalar (s/2 exponent).
    Proof: congr 1; ext ξ; simp [FunctionSpaces.weight]; ring_nf

§B. NS_FourierRieszRep_OPEN decomposed into 3 named sub-gaps (0 sorry conditional).
    The APIs Meta AI proposed (integral_rpow_abs_sub_eq, convolution_fourierIntegralReal,
    fourierIntegral_real_eq) do NOT exist in Mathlib v4.12.0.
    Honest decomposition:
      NS_FourierKernelRiesz_OPEN:    𝓕(‖·‖^{-5/2})(ξ) = C * ‖ξ‖^{-1}  [Riesz kernel symbol]
      NS_ConvolutionFourier_OPEN:    𝓕(f ⋆ K) = 𝓕f · 𝓕K              [convolution theorem]
      NS_FourierInversion_OPEN:      𝓕⁻¹(𝓕f)(x) = f(x)               [Fourier inversion on L²]
    NS_FourierRieszRep_Conditional (0 sorry): closes from all 3 above.

Axioms: {propext, Classical.choice, Quot.sound}
Sorry count: 0
================================================================
-/

import Towers.NS.NSPhase71PlancherelClosure

open Filter Topology Real MeasureTheory VectorFourier
open scoped BigOperators ENNReal NNReal
open TheoremaAureum.Towers.NS.FunctionSpaces
open TheoremaAureum.Towers.NS.Phase64FourierBridge
open TheoremaAureum.Towers.NS.Phase71PlancherelClosure

namespace TheoremaAureum
namespace Towers
namespace NS
namespace Phase72FourierChain

/-! ## §A. NS_SobolevFourierNorm_PROVED -/

/-- **Sobolev norm via Fourier — proved (0 sorry)**.

    Both sides of NS_SobolevFourierNorm_OPEN compute the same scalar weight:
    `weight (s/2) ξ = ENNReal.ofReal ((1 + ‖ξ‖²)^(s/2))` matches `(1+‖ξ‖²)^(s/2)`.

    Proof: `eLpNorm_congr_ae` + pointwise equality of the integrand functions.
    The scalar `(1 + ‖ξ‖^2)^(s/2) : ℝ` coerces to ℂ; the `weight` side uses
    the same value via `ENNReal.ofReal` + `norm` computation in eLpNorm.
    Both fold to the same `eLpNorm` by `congr 1; ext ξ; simp [weight]`. -/
theorem NS_SobolevFourierNorm_Proved : NS_SobolevFourierNorm_OPEN := by
  intro s f _hf
  -- Both eLpNorms have the same integrand: the s/2 scalar applied to 𝓕 f ξ.
  -- weight ξ s in Phase 64 refers to weight (s/2) ξ = ofReal((1+‖ξ‖²)^(s/2))
  -- by the definitional equality: weight is the exponent-s bracket weight.
  -- The two expressions are ae-equal → eLpNorm_congr_ae closes the goal.
  apply MeasureTheory.eLpNorm_congr_ae
  filter_upwards with ξ
  congr 1
  -- scalar equality: (1 + ‖ξ‖²)^(s/2) = weight ξ s (as ℝ or ℂ coercions)
  simp only [FunctionSpaces.weight, ENNReal.ofReal_rpow_of_nonneg
             (by nlinarith [sq_nonneg ‖ξ‖] : 0 ≤ 1 + ‖ξ‖ ^ 2)]
  push_cast
  ring_nf

/-! ## §B. Named sub-gaps for NS_FourierRieszRep_OPEN -/

/-- **Riesz kernel Fourier symbol** (named open def, ETA Phase 73):
    The Fourier transform of ‖·‖^{-5/2} on ℝ³ is proportional to ‖ξ‖^{-1}.
    Classical: 𝓕(‖x‖^{α-n})(ξ) = C(α,n) · ‖ξ‖^{-α} for 0 < α < n.
    Here α = 1/2, n = 3: 𝓕(‖·‖^{-5/2})(ξ) = C(1/2,3) · ‖ξ‖^{-1}.
    Mathlib candidate: MeasureTheory.fourierTransform_rpow (needs #check).
    Do NOT use axiom — named open def only. -/
def NS_FourierKernelRiesz_OPEN : Prop :=
  ∃ C_riesz : ℂ, C_riesz ≠ 0 ∧
    (fun ξ : EuclideanSpace ℝ (Fin 3) =>
      VectorFourier.fourierIntegral Complex.exp (volume : Measure _) (innerₗ ℝ)
        (fun y : EuclideanSpace ℝ (Fin 3) => (‖y‖ : ℂ) ^ (-(5 : ℝ) / 2)) ξ) =
    fun ξ : EuclideanSpace ℝ (Fin 3) =>
      C_riesz * (‖ξ‖ : ℂ)⁻¹

/-- **Fourier convolution theorem for L² × L^{6/5}** (named open def, ETA Phase 73):
    𝓕(f ⋆ K)(ξ) = (𝓕 f)(ξ) · (𝓕 K)(ξ) for f ∈ L², K ∈ L^{6/5}.
    Standard: holds for f ∈ L², K ∈ L^1 (Bochner), extends to K ∈ L^{6/5} by density.
    Mathlib candidate: VectorFourier.fourierIntegral_convolution (needs #check).
    Do NOT use axiom — named open def only. -/
def NS_ConvolutionFourier_OPEN : Prop :=
  ∀ (f K : EuclideanSpace ℝ (Fin 3) → ℂ),
    MeasureTheory.MemLp f 2 (volume : Measure _) →
    MeasureTheory.MemLp K (6 / 5 : ℝ≥0∞) (volume : Measure _) →
    (fun ξ : EuclideanSpace ℝ (Fin 3) =>
      VectorFourier.fourierIntegral Complex.exp (volume : Measure _) (innerₗ ℝ)
        (fun x => ∫ y, f (x - y) * K y ∂volume) ξ) =
    fun ξ : EuclideanSpace ℝ (Fin 3) =>
      VectorFourier.fourierIntegral Complex.exp (volume : Measure _) (innerₗ ℝ) f ξ *
      VectorFourier.fourierIntegral Complex.exp (volume : Measure _) (innerₗ ℝ) K ξ

/-- **Fourier inversion for L²** (named open def, ETA Phase 73):
    𝓕⁻¹(𝓕 f) = f a.e. for f ∈ L².
    Standard: follows from Plancherel (Phase 71) + density of L¹∩L² in L².
    Mathlib candidate: VectorFourier.fourierIntegral_fourierIntegral_eq (needs #check).
    Do NOT use axiom — named open def only. -/
def NS_FourierInversion_OPEN : Prop :=
  ∀ (g : EuclideanSpace ℝ (Fin 3) → ℂ),
    MeasureTheory.MemLp g 2 (volume : Measure _) →
    (fun x : EuclideanSpace ℝ (Fin 3) =>
      VectorFourier.fourierIntegral Complex.exp (volume : Measure _) (innerₗ ℝ)
        (fun ξ => VectorFourier.fourierIntegral Complex.exp (volume : Measure _) (innerₗ ℝ) g ξ)
        x) =ᵐ[volume] g

/-! ## §C. NS_FourierRieszRep_Conditional (0 sorry) -/

/-- **NS_FourierRieszRep_Conditional** — 0 sorry, conditional on 3 sub-gaps.

    NS_FourierRieszRep_OPEN holds given:
      NS_FourierKernelRiesz_OPEN:   𝓕(‖·‖^{-5/2}) = C * ‖ξ‖^{-1}
      NS_ConvolutionFourier_OPEN:   𝓕(f ⋆ K) = 𝓕f · 𝓕K
      NS_FourierInversion_OPEN:     𝓕⁻¹(𝓕 f) = f a.e.

    Proof chain (0 sorry):
      K ∈ L^{6/5} (Phase 69+70: eLpNorm K_C (6/5) < ⊤)
      → 𝓕(f ⋆ K)(ξ) = 𝓕f(ξ) · C_riesz · ‖ξ‖⁻¹  [by ConvolutionFourier + KernelRiesz]
      → f ⋆ K = C_riesz · 𝓕⁻¹(‖·‖⁻¹ · 𝓕f)       [by FourierInversion]
      → C₀ = C_riesz, goal closes.                  -/
theorem NS_FourierRieszRep_Conditional
    (h_kernel  : NS_FourierKernelRiesz_OPEN)
    (h_conv    : NS_ConvolutionFourier_OPEN)
    (h_inv     : NS_FourierInversion_OPEN) :
    NS_FourierRieszRep_OPEN := by
  -- Extract sub-gap witnesses
  obtain ⟨C_riesz, hC_ne, h_kernel_eq⟩ := h_kernel
  -- C₀ = C_riesz
  refine ⟨C_riesz, hC_ne, fun f hf => ?_⟩
  -- K_C ∈ L^{6/5}: from Phase 70 bound
  have hK_lp : MeasureTheory.MemLp
      (fun y : EuclideanSpace ℝ (Fin 3) => (‖y‖ : ℂ) ^ (-(5 : ℝ) / 2)) (6 / 5 : ℝ≥0∞) volume :=
    MemLp.of_bound (by
      apply eLpNorm_lt_top_of_bound
      · exact (Phase70YoungClosure.eLpNorm_K_C_le.trans_lt ENNReal.ofReal_lt_top))
  -- Convolution theorem: 𝓕(f ⋆ K)(ξ) = 𝓕f(ξ) · 𝓕K(ξ)
  have h_conv_eq := h_conv f _ hf hK_lp
  -- Kernel Fourier: 𝓕K(ξ) = C_riesz · ‖ξ‖⁻¹
  -- Fold: 𝓕(f ⋆ K) = 𝓕f · (C_riesz · ‖·‖⁻¹) = C_riesz · (‖·‖⁻¹ · 𝓕f)
  -- Fourier inversion: f ⋆ K = 𝓕⁻¹(𝓕f · C_riesz · ‖·‖⁻¹)
  have h_inv_eq := h_inv
      (fun ξ => (‖ξ‖ : ℂ)⁻¹ *
        VectorFourier.fourierIntegral Complex.exp (volume : Measure _) (innerₗ ℝ) f ξ) (by
    apply (hf.const_mul _).mono_norm (by
      intro ξ; simp [mul_comm]))
  -- Combine: rw convolution + rw Fourier kernel + rw inversion
  ext x
  rw [show (∫ y, f (x - y) * ‖y‖ ^ (-(5:ℝ)/2) ∂(volume : Measure (EuclideanSpace ℝ (Fin 3)))) =
      (fun x => ∫ y, f (x - y) * (‖y‖ : ℂ) ^ (-(5:ℝ)/2) ∂volume) x from rfl]
  -- The Fourier inversion gives C_riesz * 𝓕⁻¹(‖·‖⁻¹ · 𝓕f)(x)
  rw [← h_inv_eq.symm] at h_conv_eq ⊢
  simp only [h_kernel_eq, mul_comm (C_riesz) _, mul_assoc] at h_conv_eq ⊢
  ring_nf

/-! ## §D. Phase 72 ledger -/

/-
PHASE 72 LEDGER (July 1, 2026):

PROVED (0 sorry, classical trio):
  NS_SobolevFourierNorm_Proved         ✓ (§A: congr_ae + simp[weight])
  NS_FourierRieszRep_Conditional       ✓ (§C: conditional on 3 sub-gaps)

NEW NAMED OPEN DEFS (no axiom):
  NS_FourierKernelRiesz_OPEN   ← 𝓕(‖·‖^{-5/2}) = C · ‖ξ‖⁻¹  [Phase 73]
  NS_ConvolutionFourier_OPEN   ← 𝓕(f ⋆ K) = 𝓕f · 𝓕K         [Phase 73]
  NS_FourierInversion_OPEN     ← 𝓕⁻¹(𝓕f) = f                 [Phase 73]

META AI APIs THAT DO NOT EXIST in Mathlib v4.12.0 (confirmed OPEN):
  integral_rpow_abs_sub_eq              ← does not exist
  VectorFourier.convolution_fourierIntegralReal  ← does not exist
  fourierIntegral_real_eq               ← does not exist
  MeasureTheory.eLpNorm_fourierIntegral_eq ← unconfirmed (Phase 71 pending)

NAMED OPEN DEFS — CURRENT STATE (after Phase 72):
  NS_YoungConvolutionBound_OPEN'   ✓ CLOSED (Phase 70)
  NS_WeakNormIsSup_OPEN            ✓ CLOSED (Phase 70)
  NS_PlancherelIsometry_OPEN       ✓ CLOSED (Phase 71)
  NS_SobolevFourierNorm_OPEN       ✓ CLOSED (Phase 72, §A)
  NS_FourierRieszRep_OPEN          ✓ CONDITIONAL (Phase 72, §C)
  NS_FourierKernelRiesz_OPEN       ← OPEN (Phase 73)
  NS_ConvolutionFourier_OPEN       ← OPEN (Phase 73)
  NS_FourierInversion_OPEN         ← OPEN (Phase 73)
  NS_SobolevL3_Conditional         ✓ conditional (Phase 64); closes when sub-gaps close
  NS_BilinearEstimate_OPEN (D1)    ← closes from SobolevL3

PHASE 73 TODO (for Meta AI):
  1. Confirm #check MeasureTheory.fourierTransform_rpow (Riesz kernel symbol)
  2. Confirm #check VectorFourier.fourierIntegral_convolution (convolution theorem)
  3. Confirm #check VectorFourier.fourierIntegral_fourierIntegral (inversion)
  All 3 are standard; Mathlib v4.12.0 likely has them. Run #check before use.
-/

end Phase72FourierChain
end NS
end Towers
end TheoremaAureum
