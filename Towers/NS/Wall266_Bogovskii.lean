/-
Wall266_Bogovskii — compact-support cutoff for the Path B scaffold.

What is proved, with no `sorry` and no new axiom:
* A concrete normalized cutoff on the unit ball, built from Mathlib's
  `ContDiffBump` and `ContDiffBump.normed`. Its integral is 1, it is
  nonnegative, smooth, and supported in the open unit ball.
* For every R > 0, the radius-R rescaling
  `x ↦ R⁻³ • ω(R⁻¹ • x)` has integral 1, is smooth and compactly
  supported inside the ball of radius R, and is Lipschitz. The Lipschitz
  constant is the unit-cutoff constant times `‖R⁻³‖₊ * ‖R⁻¹‖₊`, which is
  the scaling `C / R⁴` coming from the Jacobian factor `R⁻³` and the chain
  rule factor `R⁻¹`.
* `rayIntegral_reparam`: on a finite interval `1 ≤ r ≤ M`, the kernel ray
  `∫ ω(y + r(x-y)) r² dr` equals `∫ ω(y + t⁻¹(x-y)) t⁻⁴ dt` after
  `r = t⁻¹`. This is the change of variables for the nonsingular formula
  `u(x) = ∫₀¹ ∫ z ω(x+(1-t)z) f(x-tz) dz dt`. It does not identify the
  divergence of `Bogovskii` with `f`.

What is recorded as OPEN, with no `sorry` and no new axiom:
* `BogovskiiDiv_OPEN`: the kernel identity `div (Bogovskii ω R f) = f`
  for smooth, compactly supported, mean-zero data in the ball of radius R.
  The proved fact `∫ ω_R = 1` is the normalization that identity uses.
  It does not prove the identity. The missing step is integration by parts
  and Fubini for the distributional derivative of the kernel, including
  the diagonal delta. Mathlib v4.12 has no Bogovskii theorem.
* `BogovskiiCZ_OPEN`: `‖∇(B f)‖₂ ≤ C ‖f‖₂` and the radius-scaled bound
  inside `H1Norm (B f) ≤ C (1 + R) ‖f‖₂`. The cutoff Lipschitz constant
  `C / R⁴` is not a singular-integral bound. Mathlib v4.12 has no
  Calderón–Zygmund theorem to import.
* Neither proposition is asserted. This file does not make the M6
  pressure term work.
-/

import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Function.LpSpace
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.MeasureTheory.Constructions.Prod.Integral
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

namespace TheoremaAureum.Towers.NS.Wall266Bogovskii

open FiniteDimensional MeasureTheory Filter
open scoped BigOperators NNReal Interval Topology

noncomputable section

/-- Euclidean three-space, rather than the supremum-norm function space. -/
abbrev R3 := EuclideanSpace ℝ (Fin 3)

/-- The open Euclidean ball centered at zero. -/
def ballR (R : ℝ) : Set R3 := Metric.ball (0 : R3) R

/-- Required normalized cutoff data. -/
structure BogovskiiCutoff where
  toFun : R3 → ℝ
  smooth : ContDiff ℝ ⊤ toFun
  compact_support : HasCompactSupport toFun
  support_in_unit_ball : Function.support toFun ⊆ ballR 1
  nonnegative : ∀ x, 0 ≤ toFun x
  integral_one : (∫ x, toFun x ∂(volume : Measure R3)) = 1

/-- The dimension-three rescaling of the supplied unit-ball cutoff. -/
def bogovskii_cutoff (omega : BogovskiiCutoff) (R : ℝ) (x : R3) : ℝ :=
  (R ^ 3)⁻¹ * omega.toFun (R⁻¹ • x)

/-- The actual Bogovskii kernel. Integrability of the singular diagonal is
not proved in this file. -/
def BogovskiiKernel (omega : BogovskiiCutoff) (R : ℝ) (x y : R3) : R3 :=
  (∫ r in Set.Ioi (1 : ℝ),
    bogovskii_cutoff omega R (y + r • (x - y)) * r ^ 2) • (x - y)

/-- The integral operator. Scalar multiplication, not pointwise vector
multiplication, gives the vector-valued Bochner integrand. -/
def Bogovskii (omega : BogovskiiCutoff) (R : ℝ) (f : R3 → ℝ) : R3 → R3 :=
  fun x => ∫ y, f y • BogovskiiKernel omega R x y ∂(volume : Measure R3)

/-- Classical derivative of component j in coordinate direction i. -/
def coordinateDerivative (v : R3 → R3) (i j : Fin 3) : R3 → ℝ :=
  fun x => deriv
    (fun t : ℝ => (v (x + t • EuclideanSpace.single i 1)) j) 0

/-- Classical coordinate divergence. -/
def divClassical (v : R3 → R3) (x : R3) : ℝ :=
  ∑ i : Fin 3, coordinateDerivative v i i x

/-- Real L2 quantity. It is a norm only when the extended norm is finite:
ENNReal.toReal sends infinity to zero. -/
def L2Norm (f : R3 → ℝ) : ℝ :=
  (eLpNorm f 2 (volume : Measure R3)).toReal

/-- Finiteness and a.e. strong measurability of the vector field and
all nine classical first derivatives. -/
def H1Regular (v : R3 → R3) : Prop :=
  Memℒp v 2 (volume : Measure R3) ∧
    ∀ i j : Fin 3, Memℒp (coordinateDerivative v i j) 2 (volume : Measure R3)

/-- The inhomogeneous H1 quantity on fields satisfying H1Regular. -/
def H1Norm (v : R3 → R3) : ℝ :=
  Real.sqrt
    ((eLpNorm v 2 (volume : Measure R3)).toReal ^ 2 +
      ∑ i : Fin 3, ∑ j : Fin 3,
        (eLpNorm (coordinateDerivative v i j) 2
          (volume : Measure R3)).toReal ^ 2)

private theorem finrank_R3 : finrank ℝ R3 = 3 := by
  simpa [Fintype.card_fin] using
    (finrank_euclideanSpace_fin : finrank ℝ (EuclideanSpace ℝ (Fin 3)) = Fintype.card (Fin 3))

/-- Mathlib bump equal to 1 on the closed ball of radius 1/2 and supported
on the open unit ball. The same radii pattern as the H1 cutoff, scaled to
the unit ball required by `BogovskiiCutoff`. -/
noncomputable def unitBump : ContDiffBump (0 : R3) where
  rIn := 1 / 2
  rOut := 1
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- Normalized unit-ball cutoff. `ContDiffBump.normed` divides by the
positive volume integral, so the integral is 1 by Mathlib. -/
noncomputable def unitBogovskiiCutoff : BogovskiiCutoff where
  toFun := unitBump.normed (volume : Measure R3)
  smooth := unitBump.contDiff_normed
  compact_support := unitBump.hasCompactSupport_normed
  support_in_unit_ball := by
    rw [unitBump.support_normed_eq (μ := (volume : Measure R3))]
    exact subset_rfl
  nonnegative := unitBump.nonneg_normed
  integral_one := unitBump.integral_normed

/-- A Lipschitz constant for the normalized unit cutoff, from compact support
and smoothness. This is the same existence argument used for the H1 cutoff. -/
noncomputable def unitCutoffLipschitzConstant : ℝ≥0 :=
  Classical.choose (ContDiff.lipschitzWith_of_hasCompactSupport
    unitBogovskiiCutoff.compact_support
    (unitBogovskiiCutoff.smooth : ContDiff ℝ ⊤ unitBogovskiiCutoff.toFun)
    le_top)

theorem unitCutoff_lipschitz :
    LipschitzWith unitCutoffLipschitzConstant unitBogovskiiCutoff.toFun :=
  Classical.choose_spec (ContDiff.lipschitzWith_of_hasCompactSupport
    unitBogovskiiCutoff.compact_support
    (unitBogovskiiCutoff.smooth : ContDiff ℝ ⊤ unitBogovskiiCutoff.toFun)
    le_top)

theorem bogovskii_cutoff_smooth (omega : BogovskiiCutoff) (R : ℝ) :
    ContDiff ℝ ⊤ (bogovskii_cutoff omega R) := by
  unfold bogovskii_cutoff
  exact contDiff_const.mul (omega.smooth.comp (contDiff_const_smul (R⁻¹)))

theorem bogovskii_cutoff_support_subset (omega : BogovskiiCutoff) {R : ℝ} (hR : 0 < R) :
    Function.support (bogovskii_cutoff omega R) ⊆ ballR R := by
  intro x hx
  have hω : omega.toFun (R⁻¹ • x) ≠ 0 := by
    intro h0
    apply hx
    simp [bogovskii_cutoff, h0]
  have hmem : R⁻¹ • x ∈ ballR 1 :=
    omega.support_in_unit_ball (Function.mem_support.2 hω)
  have hnorm : ‖R⁻¹ • x‖ < 1 := by
    simpa [ballR, Metric.mem_ball, dist_zero_right] using hmem
  have hinv : 0 < R⁻¹ := inv_pos.2 hR
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hinv] at hnorm
  have hdiv : ‖x‖ / R < 1 := by
    rwa [div_eq_mul_inv, mul_comm]
  have hxlt : ‖x‖ < R := (div_lt_one hR).1 hdiv
  simpa [ballR, Metric.mem_ball, dist_zero_right] using hxlt

theorem bogovskii_cutoff_hasCompactSupport (omega : BogovskiiCutoff) {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (bogovskii_cutoff omega R) := by
  rw [HasCompactSupport, tsupport]
  have hsubset := closure_mono (bogovskii_cutoff_support_subset omega hR)
  rw [ballR, closure_ball (0 : R3) hR.ne'] at hsubset
  exact IsCompact.of_isClosed_subset (isCompact_closedBall (0 : R3) R) isClosed_closure hsubset

/-- The rescaled cutoff keeps integral 1. The factor `R⁻³` cancels the
Jacobian `R³` of `x ↦ R⁻¹ • x` on `R3`. -/
theorem bogovskii_cutoff_integral (omega : BogovskiiCutoff) {R : ℝ} (hR : 0 < R) :
    ∫ x, bogovskii_cutoff omega R x ∂(volume : Measure R3) = 1 := by
  unfold bogovskii_cutoff
  rw [integral_mul_left]
  have hscale :=
    Measure.integral_comp_inv_smul_of_nonneg (volume : Measure R3) omega.toFun hR.le
  rw [hscale, omega.integral_one, finrank_R3, smul_eq_mul, mul_one]
  exact inv_mul_cancel₀ (pow_ne_zero 3 hR.ne')

/-- Chain rule plus the normalization factor. If `ω` is `K`-Lipschitz, then
`x ↦ R⁻³ * ω(R⁻¹ • x)` is Lipschitz with constant `‖R⁻³‖₊ * K * ‖R⁻¹‖₊`. -/
theorem bogovskii_cutoff_lipschitz (omega : BogovskiiCutoff) {R : ℝ} (hR : 0 < R) {K : ℝ≥0}
    (hK : LipschitzWith K omega.toFun) :
    LipschitzWith (‖(R ^ 3)⁻¹‖₊ * (K * ‖R⁻¹‖₊)) (bogovskii_cutoff omega R) := by
  have hinner : LipschitzWith (K * ‖R⁻¹‖₊) (fun x : R3 => omega.toFun (R⁻¹ • x)) :=
    hK.comp (lipschitzWith_smul (R⁻¹))
  refine lipschitzWith_iff_dist_le_mul.2 fun x y => ?_
  have hsub :=
    mul_sub ((R ^ 3)⁻¹) (omega.toFun (R⁻¹ • x)) (omega.toFun (R⁻¹ • y))
  calc
    dist (bogovskii_cutoff omega R x) (bogovskii_cutoff omega R y)
        = ‖(R ^ 3)⁻¹‖ * dist (omega.toFun (R⁻¹ • x)) (omega.toFun (R⁻¹ • y)) := by
          unfold bogovskii_cutoff
          rw [dist_eq_norm, ← hsub, norm_mul, ← dist_eq_norm]
    _ ≤ ‖(R ^ 3)⁻¹‖ * ((K * ‖R⁻¹‖₊ : ℝ≥0) * dist x y) :=
          mul_le_mul_of_nonneg_left (hinner.dist_le_mul x y) (norm_nonneg _)
    _ = (‖(R ^ 3)⁻¹‖₊ * (K * ‖R⁻¹‖₊) : ℝ≥0) * dist x y := by
          rw [← coe_nnnorm, ← mul_assoc, ← NNReal.coe_mul]

/-- The unit cutoff's expanding rescales. The constant depends on R only
through `‖R⁻³‖₊ * ‖R⁻¹‖₊`. -/
theorem unit_bogovskii_cutoff_lipschitz {R : ℝ} (hR : 0 < R) :
    LipschitzWith (‖(R ^ 3)⁻¹‖₊ * unitCutoffLipschitzConstant * ‖R⁻¹‖₊)
      (bogovskii_cutoff unitBogovskiiCutoff R) := by
  simpa [mul_assoc] using
    bogovskii_cutoff_lipschitz unitBogovskiiCutoff hR unitCutoff_lipschitz

/-- The ray integral in the kernel, cut at a finite upper limit, is the same
integral after `r = t⁻¹`. Off the diagonal the integrand vanishes for large
`r`, so this is the bridge from `BogovskiiKernel` to the nonsingular
double-integral formula. -/
private lemma rayIntegral_reparam (omega : BogovskiiCutoff) (R : ℝ) (x y : R3) {M : ℝ}
    (hM : 1 < M) :
    (∫ r in (1 : ℝ)..M,
        bogovskii_cutoff omega R (y + r • (x - y)) * r ^ 2) =
      ∫ t in (1 / M)..1,
        bogovskii_cutoff omega R (y + t⁻¹ • (x - y)) * (t ^ 4)⁻¹ := by
  let g : ℝ → ℝ := fun r =>
    bogovskii_cutoff omega R (y + r • (x - y)) * r ^ 2
  have hMpos : 0 < M := lt_trans zero_lt_one hM
  have hinvpos : 0 < 1 / M := one_div_pos.2 hMpos
  have hle : 1 / M ≤ 1 := by
    rw [div_le_one hMpos]
    exact hM.le
  have ht_pos : ∀ t ∈ Set.uIcc (1 / M) (1 : ℝ), 0 < t := by
    intro t ht
    rw [Set.uIcc_of_le hle] at ht
    exact lt_of_lt_of_le hinvpos ht.1
  have hg : Continuous g := by
    have hc : Continuous (bogovskii_cutoff omega R) :=
      (bogovskii_cutoff_smooth omega R).continuous
    exact (hc.comp <| continuous_const.add <| continuous_id.smul continuous_const).mul
      (continuous_id.pow 2)
  have hder : ∀ t ∈ Set.uIcc (1 / M) (1 : ℝ),
      HasDerivAt (fun s : ℝ => s⁻¹) (-(t ^ 2)⁻¹) t := by
    intro t ht
    exact hasDerivAt_inv (x := t) (ht_pos t ht).ne'
  have hf' : ContinuousOn (fun t : ℝ => -(t ^ 2)⁻¹) (Set.uIcc (1 / M) 1) :=
    ((continuous_id.pow 2).continuousOn.inv₀ (fun t ht => pow_ne_zero 2 (ht_pos t ht).ne')).neg
  have hsub :=
    _root_.intervalIntegral.integral_comp_smul_deriv'
      (f := fun t : ℝ => t⁻¹) (f' := fun t : ℝ => -(t ^ 2)⁻¹) (g := g) (a := 1 / M) (b := 1)
      hder hf' (hg.continuousOn.mono (Set.subset_univ _))
  have hrewrite : ∀ t, t ≠ 0 →
      (-(t ^ 2)⁻¹) * g (t⁻¹) =
        -(bogovskii_cutoff omega R (y + t⁻¹ • (x - y)) * (t ^ 4)⁻¹) := by
    intro t ht
    have hgdef : g (t⁻¹) =
        bogovskii_cutoff omega R (y + t⁻¹ • (x - y)) * (t⁻¹) ^ 2 := rfl
    have hsq : (t⁻¹) ^ 2 = (t ^ 2)⁻¹ := by field_simp [ht]
    have hmul : (t ^ 2)⁻¹ * (t ^ 2)⁻¹ = (t ^ 4)⁻¹ := by
      rw [← mul_inv, ← pow_add]
    rw [hgdef, hsq]
    calc
      (-(t ^ 2)⁻¹) *
          (bogovskii_cutoff omega R (y + t⁻¹ • (x - y)) * (t ^ 2)⁻¹) =
          -(bogovskii_cutoff omega R (y + t⁻¹ • (x - y)) *
            ((t ^ 2)⁻¹ * (t ^ 2)⁻¹)) := by ring
      _ = -(bogovskii_cutoff omega R (y + t⁻¹ • (x - y)) * (t ^ 4)⁻¹) := by rw [hmul]
  have hneg :
      ∫ t in (1 / M)..1,
          bogovskii_cutoff omega R (y + t⁻¹ • (x - y)) * (t ^ 4)⁻¹ =
        -(∫ t in (1 / M)..1, (-(t ^ 2)⁻¹) * g (t⁻¹)) := by
    rw [← _root_.intervalIntegral.integral_neg]
    refine _root_.intervalIntegral.integral_congr (fun t ht => ?_)
    have ht0 : t ≠ 0 := (ht_pos t ht).ne'
    simpa [neg_neg] using congrArg Neg.neg (hrewrite t ht0).symm
  have hray : ∫ r in (M : ℝ)..1, g r = -(∫ r in (1 : ℝ)..M, g r) :=
    _root_.intervalIntegral.integral_symm (f := g) (1 : ℝ) M
  have hsub' :
      ∫ t in (1 / M)..1, (-(t ^ 2)⁻¹) * g (t⁻¹) = ∫ r in (M : ℝ)..1, g r := by
    simpa [smul_eq_mul] using hsub
  rw [hneg, hsub', hray, neg_neg]

/-- OPEN. Classical divergence inverts the Bogovskii integral on mean-zero
data. `bogovskii_cutoff_integral` is the supporting normalization
`∫ ω_R = 1`. Closing this proposition needs the kernel cancellation, not
the cutoff Lipschitz bound. -/
def BogovskiiDiv_OPEN : Prop :=
  ∀ (omega : BogovskiiCutoff) (R : ℝ) (f : R3 → ℝ),
    0 < R →
    ContDiff ℝ ⊤ f →
    HasCompactSupport f →
    (∫ y, f y ∂(volume : Measure R3)) = 0 →
    Function.support f ⊆ ballR R →
    ContDiff ℝ ⊤ (Bogovskii omega R f) ∧
      HasCompactSupport (Bogovskii omega R f) ∧
      Function.support (Bogovskii omega R f) ⊆ ballR R ∧
      ∀ x, divClassical (Bogovskii omega R f) x = f x

/-- OPEN. Singular-integral bound for the Bogovskii operator. The factor
`(1 + R)` is the standard scaling: `‖B f‖₂` carries a radius and
`‖∇(B f)‖₂` does not. `H1Norm` packages both. The cutoff constant
`‖R⁻³‖₊ * K * ‖R⁻¹‖₊` does not prove this. -/
def BogovskiiCZ_OPEN : Prop :=
  ∀ omega : BogovskiiCutoff,
    ∃ C : ℝ, 0 < C ∧
      ∀ (R : ℝ) (f : R3 → ℝ),
        0 < R →
        ContDiff ℝ ⊤ f →
        HasCompactSupport f →
        (∫ y, f y ∂(volume : Measure R3)) = 0 →
        Function.support f ⊆ ballR R →
        H1Regular (Bogovskii omega R f) ∧
          H1Norm (Bogovskii omega R f) ≤ C * (1 + R) * L2Norm f

end

end TheoremaAureum.Towers.NS.Wall266Bogovskii
