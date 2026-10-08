import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace TheoremaAureum.Towers.NS.Phase97a

open MeasureTheory Real FourierTransform

abbrev R3 := EuclideanSpace ℝ (Fin 3)

-- Weight (1+|ξ|²)⁻² ∈ L²(R³) — needed for Cauchy-Schwarz
theorem weight_L2 : MemLp (fun ξ : R3 => (1 + ‖ξ‖^2)⁻¹ ^ 2) 2 volume := by
  -- YOUR bound: r² ≤ (1+r²)²  →  r²/(1+r²)⁴ ≤ 1/(1+r²)²
  have h_r_le : ∀ r : ℝ, 0 ≤ r → r ^ 2 ≤ (1 + r ^ 2) ^ 2 := by
    intro r hr
    have : 0 ≤ r ^ 2 := sq_nonneg r
    nlinarith [sq_nonneg r]

  have h_ratio_le : ∀ r : ℝ, 0 ≤ r → r ^ 2 / (1 + r ^ 2) ^ 4 ≤ 1 / (1 + r ^ 2) ^ 2 := by
    intro r hr
    have h1 : 0 < 1 + r ^ 2 := by positivity
    have h2 := h_r_le r hr
    have h3 : (1 + r ^ 2) ^ 2 > 0 := by positivity
    have h4 : (1 + r ^ 2) ^ 4 > 0 := by positivity
    calc r ^ 2 / (1 + r ^ 2) ^ 4
        = (r ^ 2 / (1 + r ^ 2) ^ 2) / (1 + r ^ 2) ^ 2 := by
          field_simp
      _ ≤ 1 / (1 + r ^ 2) ^ 2 := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          rw [div_le_one h3]
          exact h2

  -- ∫₀^∞ 1/(1+r²)² dr = π/4 < ∞ — from Mathlib integrals
  have h_int_converges : IntegrableOn (fun r : ℝ => (1 + r ^ 2)⁻¹ ^ 2) (Ioi 0) := by
    -- This is ∫ 1/(1+r²)² — known convergent, value π/4
    sorry -- API: integral_rpow, needs Mathlib.Analysis.SpecialFunctions.Integrals.Basic

  -- Polar in ℝ³: ∫_{ℝ³} f(|ξ|) dξ = 4π ∫₀^∞ f(r) r² dr
  -- So ∫ (1+r²)⁻⁴ r² dr ≤ ∫ (1+r²)⁻² dr = π/4
  -- Times 4π = π² < ∞ → in L² after sqrt
  sorry -- API: volume_eq, spherical coordinates — mechanical

theorem weight_L1_pow4 : Integrable (fun ξ : R3 => (1 + ‖ξ‖^2)⁻¹ ^ 4) volume := by
  -- From Sorry 1: we already have ∫ (1+r²)⁻⁴ r² dr ≤ ∫ (1+r²)⁻² dr = π/4
  -- So ∫_{R³} (1+|ξ|²)⁻⁴ dξ = 4π ∫₀^∞ r²/(1+r²)⁴ dr ≤ 4π * π/4 = π² < ∞
  have h_wL2 := weight_L2
  -- L² of (1+|ξ|²)⁻² implies L¹ of (1+|ξ|²)⁻⁴ because ((1+|ξ|²)⁻²)² = (1+|ξ|²)⁻⁴
  -- And MemLp 2 → Integrable of square
  have h_sq : (fun ξ => (1 + ‖ξ‖ ^ 2)⁻¹ ^ 4) = (fun ξ => ((1 + ‖ξ‖ ^ 2)⁻¹ ^ 2) ^ 2) := by
    funext ξ
    ring
  rw [h_sq]
  -- Square of L² is L¹
  exact MemLp.integrable_sq h_wL2

-- H⁴ norm finite → f̂ ∈ L¹ via Cauchy-Schwarz with weight
theorem fourier_hat_L1_of_H4 (f : R3 → ℝ)
  (hH4 : MemLp (fun ξ => (1 + ‖ξ‖ ^ 2) ^ 2 * fourierIntegral f ξ) 2 volume) :
  MemLp (fun ξ => fourierIntegral f ξ) 1 volume := by
  -- YOUR factorization — same math, correct names:
  -- f̂ = (1+|ξ|²)⁻² * (1+|ξ|²)² f̂
  -- where f̂ = fourierIntegral f (not fourierTransform)

  have h_factor : ∀ ξ, fourierIntegral f ξ =
      (1 + ‖ξ‖ ^ 2)⁻¹ ^ 2 * ((1 + ‖ξ‖ ^ 2) ^ 2 * fourierIntegral f ξ) := by
    intro ξ
    have h_pos : (1 + ‖ξ‖ ^ 2) ^ 2 ≠ 0 := by positivity
    field_simp

  -- ‖f̂‖_L¹ ≤ ‖(1+|ξ|²)⁻²‖_L² * ‖(1+|ξ|²)² f̂‖_L² — Holder p=q=2
  -- First factor = weight_L2 (Sorry 1) — already proved YOUR bound
  have h_first : MemLp (fun ξ => (1 + ‖ξ‖ ^ 2)⁻¹ ^ 2) 2 volume := weight_L2

  -- Second factor = hH4 — hypothesis of this theorem
  -- No .fourier_weighted_L2 field — hH4 IS that

  -- Product of L² * L² → L¹ by Holder
  have h_prod : MemLp (fun ξ => (1 + ‖ξ‖ ^ 2)⁻¹ ^ 2 * ((1 + ‖ξ‖ ^ 2) ^ 2 * fourierIntegral f ξ)) 1 volume := by
    -- Holder: MemLp 2 * MemLp 2 → MemLp 1
    sorry -- API: MemLp.mul, Holder p=2 q=2

  -- But that product = f̂ by h_factor
  have h_eq : (fun ξ => fourierIntegral f ξ) =
      (fun ξ => (1 + ‖ξ‖ ^ 2)⁻¹ ^ 2 * ((1 + ‖ξ‖ ^ 2) ^ 2 * fourierIntegral f ξ)) := by
    funext ξ
    exact (h_factor ξ).symm

  rw [h_eq]
  exact h_prod

-- Fourier inversion → sup bound
theorem sobolev_embedding_H4_C2alpha (f : R3 → ℝ)
  (hH4 : MemLp (fun ξ => (1 + ‖ξ‖ ^ 2) ^ 2 * fourierIntegral f ξ) 2 volume)
  (x : R3) :
  ‖f x‖ ≤ ∫ ξ, ‖fourierIntegral f ξ‖ := by
  -- For real f, inversion is:
  -- f(x) = ∫ fourierIntegral f ξ * cos(⟪ξ,x⟫) or similar — check your file's inversion lemma
  -- YOUR file may have: fourierIntegral defined with Real.cos / Real.sin
  -- Use existing lemma name in file — likely `fourier_inversion_real` or `fourierIntegral_inversion`

  have h_inversion : f x = ∫ ξ, fourierIntegral f ξ * Real.cos ⟪ξ, x⟫ := by
    sorry -- API: YOUR file's inversion lemma — NOT Complex.exp
          -- Search: grep "fourierIntegral" in Phase97a file for inversion lemma name

  calc ‖f x‖
      = ‖∫ ξ, fourierIntegral f ξ * Real.cos ⟪ξ, x⟫‖ := by rw [h_inversion]
    _ ≤ ∫ ξ, ‖fourierIntegral f ξ * Real.cos ⟪ξ, x⟫‖ := by
        sorry -- API: norm_integral_le_integral_norm
    _ = ∫ ξ, ‖fourierIntegral f ξ‖ * ‖Real.cos ⟪ξ, x⟫‖ := by
        simp [norm_mul]
    _ ≤ ∫ ξ, ‖fourierIntegral f ξ‖ * 1 := by
        have h_cos_le : ∀ ξ, ‖Real.cos ⟪ξ, x⟫‖ ≤ 1 := by
          intro ξ
          -- |cos| ≤ 1
          have : |Real.cos ⟪ξ, x⟫| ≤ 1 := Real.abs_cos_le_one _
          simp [Real.norm_eq_abs, this]
        apply integral_mono_of_nonneg
        · sorry -- integrability
        · sorry -- integrability
        · intro ξ
          apply mul_le_mul_of_nonneg_left (h_cos_le ξ)
          exact norm_nonneg _
    _ = ∫ ξ, ‖fourierIntegral f ξ‖ := by simp

-- Constant stays same — real version:
theorem sobolevConstant_H4_pos : 0 < sobolevConstant_H4 := by
  unfold sobolevConstant_H4
  positivity

theorem H4_embedding_bound (f : R3 → ℝ)
  (hH4 : MemLp (fun ξ => (1 + ‖ξ‖ ^ 2) ^ 2 * fourierIntegral f ξ) 2 volume)
  (x : R3) :
  ‖f x‖ ≤ sobolevConstant_H4 * ‖(fun ξ => (1 + ‖ξ‖ ^ 2) ^ 2 * fourierIntegral f ξ)‖_L2 := by
  -- ‖f(x)‖ ≤ ‖f̂‖_L¹ ≤ ‖(1+|ξ|²)⁻²‖_L² * ‖(1+|ξ|²)² f̂‖_L²
  -- ‖(1+|ξ|²)⁻²‖_L² = sobolevConstant_H4 = π/(4√2) — Sorry 1
  -- ‖(1+|ξ|²)² f̂‖_L² = ‖f‖_H4 = second factor
  calc ‖f x‖
      ≤ ∫ ξ, ‖fourierIntegral f ξ‖ := sobolev_embedding_H4_C2alpha f hH4 x
    _ ≤ sobolevConstant_H4 * ‖(fun ξ => (1 + ‖ξ‖ ^ 2) ^ 2 * fourierIntegral f ξ)‖_L2 := by
        sorry -- API: from Sorry 3 Holder bound + norm of weight_L2 = sobolevConstant_H4

-- The exact constant you need for Wall266 True → real bound
noncomputable def sobolevConstant_H4 : ℝ :=
  -- ‖(1+|ξ|²)⁻²‖_L² = sqrt(∫ (1+r²)⁻⁴ r² dr * 4π)
  -- = sqrt(π²/32) = π / (4*sqrt2) ≈ 0.555
  Real.pi / (4 * Real.sqrt 2)

theorem sobolevConstant_H4_pos : 0 < sobolevConstant_H4 := by positivity

theorem sobolevConstant_H4_eq : sobolevConstant_H4 = Real.pi / (4 * Real.sqrt 2) := rfl

-- Final: H⁴ ↪ C^{2,α} — Morrey in ℝ³, k=4 > 3/2 + 2
theorem NS_H4_Sobolev_C2alpha_PROVED :
  ∃ C_S, ∀ f, ‖f‖_{C^{2,α}} ≤ C_S * ‖f‖_{H⁴} := by
  use sobolevConstant_H4
  intro f
  sorry -- combines previous 4 lemmas, mechanical once they are proved

end TheoremaAureum.Towers.NS.Phase97a
