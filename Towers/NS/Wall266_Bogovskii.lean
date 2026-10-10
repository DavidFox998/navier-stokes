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
  `r = t⁻¹`.
* `bogovskiiNonsingular`: the formula
  `u(x) = ∫₀¹ ∫ z ω(x+(1-t)z) f(x-tz) • z dz dt` is smooth and supported
  in the ball of radius R. Its classical divergence equals `f` when
  `∫ ω = 1` and `∫ f = 0`, by differentiating under the integral and the
  fundamental theorem of calculus. The Lipschitz bound `C / R⁴` is the
  derivative estimate for the cutoff, not this support statement.
* `bogovskiiNonsingular_eq_Bogovskii`: the singular integral equals that
  formula. Finite truncations match by `rayIntegral_reparam`; the limit
  uses dominated convergence with a dominant built from the nonsingular
  side, not a Schur test on the kernel.
* `BogovskiiDiv_closed`: `divClassical (Bogovskii ω R f) = f`, and the
  vector field is smooth and supported in the ball of radius R.
* `bogovskii_L2_bound`: `‖B f‖₂ ≤ C R ‖f‖₂`. The nonsingular formula
  equals `Bogovskii`, and on its support `|z| < 2R`. Cauchy–Schwarz in
  `x` and Fubini in `(t,z)` give the same radius factor as the Schur
  integral `∫_{|z|<2R} |z|⁻² dz`, which is `O(R)` in dimension three.
  The constant is read off the unit cutoff and the volume of the unit ball.

What is recorded as OPEN, with no `sorry` and no new axiom:
* `BogovskiiCZ_OPEN`: `H1Norm (B f) ≤ C (1 + R) ‖f‖₂`. This is not a
  theorem. The `L²` piece is the theorem `bogovskii_L2_bound`, with
  constant `16 * M * vol(closedBall 0 1)`, where `M` bounds the unit
  cutoff: `‖B f‖₂ ≤ C R ‖f‖₂`. The gradient piece is not proved.
  `H1Norm` packages both, so the full bound stays open.
  A Schur test on `|∇K| ≤ C / |x-y|³` fails: that kernel is not
  integrable. Differentiating the nonsingular formula and integrating
  by parts in `z` produces a factor `t⁻¹` on `(0,1]`, which is not
  absolutely integrable. `div u = f` does not control `‖∇u‖₂`. For a
  compactly supported field,
  `‖∇u‖₂² = ‖div u‖₂² + ‖curl u‖₂²`, so the left side is at least
  `‖f‖₂`, and a high-frequency divergence-free summand makes it
  arbitrarily larger. This cutoff operator is not the whole-space
  Fourier multiplier right inverse of divergence, so Plancherel would
  not finish the gradient bound. Mathlib v4.12 has no Calderón–Zygmund
  theorem. Closing the gradient estimate means proving, in this file, an
  `L²` bound on each `coordinateDerivative (Bogovskii ω R f) i j`.
* This file does not make the M6 pressure term work. The pressure term
  stays blocked on this open gradient bound.
-/

import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Normed
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.NormedSpace.OperatorNorm.Bilinear
import Mathlib.Analysis.NormedSpace.OperatorNorm.Completeness
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSpace
import Mathlib.Tactic.Module
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.MeasureTheory.Constructions.Prod.Integral
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Instances.ENNReal
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Order.MonotoneConvergence

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

/-- Scalar density of the nonsingular Bogovskii formula. -/
def bogovskiiDensity (omega : BogovskiiCutoff) (R t : ℝ) (f : R3 → ℝ) (x z : R3) : ℝ :=
  bogovskii_cutoff omega R (x + (1 - t) • z) * f (x - t • z)

/-- `u(x) = ∫₀¹ ∫ z ω(x+(1-t)z) f(x-tz) • z dz dt`. -/
def bogovskiiNonsingular (omega : BogovskiiCutoff) (R : ℝ) (f : R3 → ℝ) (x : R3) : R3 :=
  ∫ t in (0 : ℝ)..1, (∫ z, bogovskiiDensity omega R t f x z • z ∂(volume : Measure R3))

private lemma euclidean_sum_coordinates (z : R3) :
    z = ∑ i : Fin 3, z i • EuclideanSpace.single i (1 : ℝ) := by
  ext j
  let ev : R3 →+ ℝ :=
    { toFun := fun w => w j
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  change ev z = ev (∑ i : Fin 3, z i • EuclideanSpace.single i (1 : ℝ))
  rw [map_sum]
  simp [ev, EuclideanSpace.single_apply]

private lemma fderiv_apply_sum (L : R3 →L[ℝ] ℝ) (z : R3) :
    L z = ∑ i : Fin 3, z i * L (EuclideanSpace.single i (1 : ℝ)) := by
  calc
    L z = L (∑ i : Fin 3, z i • EuclideanSpace.single i (1 : ℝ)) :=
      congrArg L (euclidean_sum_coordinates z)
    _ = ∑ i : Fin 3, z i • L (EuclideanSpace.single i (1 : ℝ)) := by
      simp only [map_sum, ContinuousLinearMap.map_smul]
    _ = ∑ i : Fin 3, z i * L (EuclideanSpace.single i (1 : ℝ)) := by
      simp only [smul_eq_mul]

private lemma hasDerivAt_cutoff_path (omega : BogovskiiCutoff) (R : ℝ) (x z : R3) (t : ℝ) :
    HasDerivAt (fun s : ℝ => bogovskii_cutoff omega R (x + (1 - s) • z))
      ((fderiv ℝ (bogovskii_cutoff omega R) (x + (1 - t) • z)) (-z)) t := by
  have hcoeff : HasDerivAt (fun s : ℝ => 1 - s) (-1) t := by
    simpa using (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)
  have hsmul : HasDerivAt (fun s : ℝ => (1 - s) • z) ((-1 : ℝ) • z) t :=
    hcoeff.smul_const z
  have hpath : HasDerivAt (fun s : ℝ => x + (1 - s) • z) (-z) t := by
    simpa using (hasDerivAt_const t x).add hsmul
  have hdiff : Differentiable ℝ (bogovskii_cutoff omega R) :=
    (bogovskii_cutoff_smooth omega R).differentiable le_top
  exact (hdiff.differentiableAt.hasFDerivAt).comp_hasDerivAt t hpath

private lemma hasDerivAt_f_path (f : R3 → ℝ) (hf : ContDiff ℝ ⊤ f) (x z : R3) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (x - s • z))
      ((fderiv ℝ f (x - t • z)) (-z)) t := by
  have hcoeff : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
  have hsmul : HasDerivAt (fun s : ℝ => s • z) ((1 : ℝ) • z) t := hcoeff.smul_const z
  have hpath : HasDerivAt (fun s : ℝ => x - s • z) (-z) t := by
    have hsub : HasDerivAt (fun s : ℝ => x - s • z) (0 - z) t :=
      (hasDerivAt_const t x).sub (by simpa using hsmul)
    simpa using hsub
  have hdiff : Differentiable ℝ f := hf.differentiable le_top
  exact (hdiff.differentiableAt.hasFDerivAt).comp_hasDerivAt t hpath

/-- Chain rule: the `t`-derivative of the density is minus the spatial derivative
in the direction `z`. -/
private lemma hasDerivAt_bogovskiiDensity_t (omega : BogovskiiCutoff) (R : ℝ)
    (f : R3 → ℝ) (hf : ContDiff ℝ ⊤ f) (x z : R3) (t : ℝ) :
    HasDerivAt (fun s => bogovskiiDensity omega R s f x z)
      (-((fderiv ℝ (bogovskii_cutoff omega R) (x + (1 - t) • z)) z * f (x - t • z) +
          bogovskii_cutoff omega R (x + (1 - t) • z) * (fderiv ℝ f (x - t • z)) z)) t := by
  have hω := hasDerivAt_cutoff_path omega R x z t
  have hf' := hasDerivAt_f_path f hf x z t
  have hmul := hω.mul hf'
  have hnegω : (fderiv ℝ (bogovskii_cutoff omega R) (x + (1 - t) • z)) (-z) =
      -((fderiv ℝ (bogovskii_cutoff omega R) (x + (1 - t) • z)) z) := by
    rw [map_neg]
  have hnegf : (fderiv ℝ f (x - t • z)) (-z) = -((fderiv ℝ f (x - t • z)) z) := by
    rw [map_neg]
  refine hmul.congr_deriv ?_
  simp only [bogovskiiDensity, hnegω, hnegf]
  ring

/-- Both factors live in the ball of radius `R`, so their difference `z` does too. -/
private lemma bogovskiiDensity_eq_zero_of_large_z (omega : BogovskiiCutoff) {R : ℝ}
    (hR : 0 < R) {f : R3 → ℝ} (hf : Function.support f ⊆ ballR R) (t : ℝ) (x z : R3)
    (hz : 2 * R ≤ ‖z‖) : bogovskiiDensity omega R t f x z = 0 := by
  by_contra hne
  have hprod : bogovskii_cutoff omega R (x + (1 - t) • z) * f (x - t • z) ≠ 0 := by
    simpa [bogovskiiDensity] using hne
  rw [mul_ne_zero_iff] at hprod
  have hω : x + (1 - t) • z ∈ ballR R :=
    bogovskii_cutoff_support_subset omega hR (Function.mem_support.2 hprod.1)
  have hf' : x - t • z ∈ ballR R := hf (Function.mem_support.2 hprod.2)
  have hz_eq : z = (x + (1 - t) • z) - (x - t • z) := by
    module
  have hlt : ‖z‖ < 2 * R := by
    rw [hz_eq]
    calc
      ‖(x + (1 - t) • z) - (x - t • z)‖ ≤
          ‖x + (1 - t) • z‖ + ‖x - t • z‖ := norm_sub_le _ _
      _ < R + R := by
        have h1 : ‖x + (1 - t) • z‖ < R := by
          simpa [ballR, Metric.mem_ball, dist_eq_norm, sub_zero] using hω
        have h2 : ‖x - t • z‖ < R := by
          simpa [ballR, Metric.mem_ball, dist_eq_norm, sub_zero] using hf'
        exact add_lt_add h1 h2
      _ = 2 * R := by ring
  exact (not_lt.mpr hz) hlt

/-- Outside the ball, every convex combination of the two supported points is impossible. -/
private lemma bogovskiiDensity_eq_zero_of_outside (omega : BogovskiiCutoff) {R : ℝ}
    (hR : 0 < R) {f : R3 → ℝ} (hf : Function.support f ⊆ ballR R) {x : R3}
    (hx : x ∉ ballR R) {t : ℝ}     (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (z : R3) :
    bogovskiiDensity omega R t f x z = 0 := by
  by_contra hne
  have hprod : bogovskii_cutoff omega R (x + (1 - t) • z) * f (x - t • z) ≠ 0 := by
    simpa [bogovskiiDensity] using hne
  rw [mul_ne_zero_iff] at hprod
  have hω : x + (1 - t) • z ∈ ballR R :=
    bogovskii_cutoff_support_subset omega hR (Function.mem_support.2 hprod.1)
  have hf' : x - t • z ∈ ballR R := hf (Function.mem_support.2 hprod.2)
  have hcomb : (1 - t) • (x - t • z) + t • (x + (1 - t) • z) = x := by
    module
  have hxmem : x ∈ ballR R := by
    rw [← hcomb]
    exact (convex_ball (0 : R3) R) hf' hω (sub_nonneg.mpr ht1) ht0 (by ring)
  exact hx hxmem

lemma bogovskiiNonsingular_support (omega : BogovskiiCutoff) {R : ℝ} (hR : 0 < R)
    {f : R3 → ℝ} (hf : Function.support f ⊆ ballR R) :
    Function.support (bogovskiiNonsingular omega R f) ⊆ ballR R := by
  rw [Function.support_subset_iff']
  intro x hx
  rw [bogovskiiNonsingular]
  have hconst : (∫ _ in (0 : ℝ)..1, (0 : R3)) = 0 := _root_.intervalIntegral.integral_zero
  rw [← hconst]
  refine _root_.intervalIntegral.integral_congr fun t ht => ?_
  rw [Set.uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] at ht
  have hden : ∀ z, bogovskiiDensity omega R t f x z = 0 :=
    fun z => bogovskiiDensity_eq_zero_of_outside omega hR hf hx ht.1 ht.2 z
  have hfun : (fun z : R3 => bogovskiiDensity omega R t f x z • z) = 0 := by
    ext z
    simp [hden z, zero_smul]
  simp [hfun, integral_zero]

lemma bogovskiiNonsingular_hasCompactSupport (omega : BogovskiiCutoff) {R : ℝ} (hR : 0 < R)
    {f : R3 → ℝ} (hf : Function.support f ⊆ ballR R) :
    HasCompactSupport (bogovskiiNonsingular omega R f) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : R3) R)
    ((bogovskiiNonsingular_support omega hR hf).trans Metric.ball_subset_closedBall)

private lemma mem_closedBall_norm_zero {z : R3} {r : ℝ} :
    z ∈ Metric.closedBall (0 : R3) r ↔ ‖z‖ ≤ r := by
  simp [Metric.mem_closedBall, dist_eq_norm, sub_zero]

private lemma exists_norm_le_on_closedBalls
    {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup E] {G : P × R3 → E} (hG : Continuous G) (p0 : P) (ε S : ℝ) :
    ∃ C : ℝ, ∀ p z, dist p p0 ≤ ε → ‖z‖ ≤ S → ‖G (p, z)‖ ≤ C := by
  obtain ⟨C, hC⟩ :=
    ((isCompact_closedBall p0 ε).prod (isCompact_closedBall (0 : R3) S)).image
      (continuous_norm.comp hG) |>.bddAbove
  refine ⟨max C 0, ?_⟩
  intro p z hp hz
  by_cases hε : 0 ≤ ε
  · by_cases hS0 : 0 ≤ S
    · have hmem : (p, z) ∈ Metric.closedBall p0 ε ×ˢ Metric.closedBall (0 : R3) S := by
        exact ⟨by simpa [Metric.mem_closedBall] using hp,
          by simpa [mem_closedBall_norm_zero] using hz⟩
      exact (hC ⟨(p, z), hmem, rfl⟩).trans (le_max_left _ _)
    · exact absurd (norm_nonneg z) (not_le.mpr (lt_of_le_of_lt hz (lt_of_not_ge hS0)))
  · exact absurd dist_nonneg (not_le.mpr (lt_of_le_of_lt hp (lt_of_not_ge hε)))

private lemma slice_fderiv
    {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : P → R3 → E} (hF : ContDiff ℝ ⊤ (Function.uncurry F)) (p : P) (z : R3) :
    fderiv ℝ (fun q => F q z) p =
      (fderiv ℝ (Function.uncurry F) (p, z)).comp (ContinuousLinearMap.inl ℝ P R3) := by
  have hΦ : HasFDerivAt (Function.uncurry F)
      (fderiv ℝ (Function.uncurry F) (p, z)) (p, z) :=
    ((hF.differentiable le_top).differentiableAt).hasFDerivAt
  exact (hΦ.comp p (hasFDerivAt_prod_mk_left (𝕜 := ℝ) p z)).fderiv

private lemma slice_fderiv_contDiff
    {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : P → R3 → E} (hF : ContDiff ℝ ⊤ (Function.uncurry F)) :
    ContDiff ℝ ⊤ (Function.uncurry fun p z => fderiv ℝ (fun q => F q z) p) := by
  let L : ((P × R3) →L[ℝ] E) →L[ℝ] P →L[ℝ] E :=
    (ContinuousLinearMap.compL ℝ P (P × R3) E).flip (ContinuousLinearMap.inl ℝ P R3)
  have hfun : Function.uncurry (fun p z => fderiv ℝ (fun q => F q z) p) =
      fun q : P × R3 => L (fderiv ℝ (Function.uncurry F) q) := by
    funext q
    simp only [Function.uncurry]
    rw [slice_fderiv hF q.1 q.2]
    simp [L, ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply]
  rw [hfun]
  exact L.contDiff.comp (contDiff_top_iff_fderiv.mp hF).2

private lemma slice_fderiv_vanish
    {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : P → R3 → E} {S : ℝ} (hS : ∀ p z, S < ‖z‖ → F p z = 0)
    (p : P) (z : R3) (hz : S < ‖z‖) :
    fderiv ℝ (fun q => F q z) p = 0 := by
  have hzero : (fun q => F q z) = fun _ => 0 := by
    ext q
    exact hS q z hz
  simp [hzero, fderiv_const]

private lemma hasFDerivAt_zIntegral
    {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : P → R3 → E) (hF : ContDiff ℝ ⊤ (Function.uncurry F))
    {S : ℝ} (hS : ∀ p z, S < ‖z‖ → F p z = 0)
    {p0 : P} {ε : ℝ} (hε : 0 < ε) :
    HasFDerivAt (fun p => ∫ z, F p z ∂(volume : Measure R3))
      (∫ z, fderiv ℝ (fun q => F q z) p0 ∂(volume : Measure R3)) p0 := by
  let F' : P → R3 → P →L[ℝ] E := fun p z => fderiv ℝ (fun q => F q z) p
  have hslice : ∀ z, ContDiff ℝ ⊤ (fun p => F p z) := by
    intro z
    exact hF.comp (contDiff_id.prod (contDiff_const : ContDiff ℝ ⊤ fun _ : P => z))
  have hS' : ∀ p z, S < ‖z‖ → F' p z = 0 := fun p z hz => slice_fderiv_vanish hS p z hz
  obtain ⟨C, hC⟩ := exists_norm_le_on_closedBalls
    (G := Function.uncurry F') (slice_fderiv_contDiff hF).continuous p0 ε (max S 0)
  let bound : R3 → ℝ := (Metric.closedBall (0 : R3) (max S 0)).indicator fun _ => C
  have hmeasK : MeasurableSet (Metric.closedBall (0 : R3) (max S 0)) := measurableSet_closedBall
  have hbound_int : Integrable bound (volume : Measure R3) := by
    rw [integrable_indicator_iff hmeasK]
    exact integrableOn_const.2
      (Or.inr ((isCompact_closedBall (0 : R3) (max S 0)).measure_lt_top))
  have hcs : HasCompactSupport (F p0) := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : R3) (max S 0)) ?_
    intro z hz
    rw [mem_closedBall_norm_zero, not_le] at hz
    exact hS p0 z (lt_of_le_of_lt (le_max_left _ _) hz)
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := F) (F' := F') (x₀ := p0) (ε := ε) (bound := bound)
    (μ := (volume : Measure R3)) hε
    ?meas ?int ?meas' ?bound ?bint ?diff
  · exact eventually_of_forall fun p =>
      (hF.continuous.comp (continuous_const.prod_mk continuous_id)).aestronglyMeasurable
  · exact (hF.continuous.comp (continuous_const.prod_mk continuous_id)).integrable_of_hasCompactSupport
      hcs
  · exact (slice_fderiv_contDiff hF).continuous.comp
      (continuous_const.prod_mk continuous_id) |>.aestronglyMeasurable
  · refine ae_of_all _ fun z => ?_
    intro p hp
    dsimp only [bound]
    by_cases hz : z ∈ Metric.closedBall (0 : R3) (max S 0)
    · rw [Set.indicator_of_mem hz]
      have hz' : ‖z‖ ≤ max S 0 := mem_closedBall_norm_zero.mp hz
      have hp' : dist p p0 ≤ ε := le_of_lt (Metric.mem_ball.mp hp)
      simpa [F', Function.uncurry] using hC p z hp' hz'
    · rw [Set.indicator_of_not_mem hz]
      have hz' : max S 0 < ‖z‖ := by
        rw [mem_closedBall_norm_zero] at hz
        exact lt_of_not_ge hz
      have hlt : S < ‖z‖ := lt_of_le_of_lt (le_max_left _ _) hz'
      simpa [hS' p z hlt] using (norm_zero : ‖(0 : P →L[ℝ] E)‖ ≤ 0)
  · exact hbound_int
  · refine ae_of_all _ fun z _p _hp => ?_
    exact (hslice z).differentiable le_top |>.differentiableAt.hasFDerivAt

set_option maxHeartbeats 800000 in
private lemma contDiffAt_zIntegral.{u}
    {P : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (n : ℕ) {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : P → R3 → E) (hF : ContDiff ℝ ⊤ (Function.uncurry F))
    {S : ℝ} (hS : ∀ p z, S < ‖z‖ → F p z = 0) (p0 : P) :
    ContDiffAt ℝ n (fun p => ∫ z, F p z ∂(volume : Measure R3)) p0 := by
  suffices ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      (F : P → R3 → E) (hF : ContDiff ℝ ⊤ (Function.uncurry F)) {S : ℝ}
      (hS : ∀ p z, S < ‖z‖ → F p z = 0) (p0 : P),
      ContDiffAt ℝ n (fun p => ∫ z, F p z ∂(volume : Measure R3)) p0 by
    exact this F hF hS p0
  induction n with
  | zero =>
    intro E _ _ _ F hF S hS p0
    rw [Nat.cast_zero, contDiffAt_zero]
    obtain ⟨C, hC⟩ := exists_norm_le_on_closedBalls
      (G := Function.uncurry F) hF.continuous p0 1 (max S 0)
    let bound : R3 → ℝ := (Metric.closedBall (0 : R3) (max S 0)).indicator fun _ => C
    have hmeasK : MeasurableSet (Metric.closedBall (0 : R3) (max S 0)) := measurableSet_closedBall
    have hbound_int : Integrable bound (volume : Measure R3) := by
      rw [integrable_indicator_iff hmeasK]
      exact integrableOn_const.2
        (Or.inr ((isCompact_closedBall (0 : R3) (max S 0)).measure_lt_top))
    refine ⟨Metric.ball p0 1, Metric.ball_mem_nhds _ one_pos, ?_⟩
    apply continuousOn_of_dominated (μ := (volume : Measure R3)) (bound := bound)
    · intro p hp
      exact (hF.continuous.comp (continuous_const.prod_mk continuous_id)).aestronglyMeasurable
    · intro p hp
      refine ae_of_all _ fun z => ?_
      dsimp only [bound]
      by_cases hz : z ∈ Metric.closedBall (0 : R3) (max S 0)
      · rw [Set.indicator_of_mem hz]
        have hz' : ‖z‖ ≤ max S 0 := mem_closedBall_norm_zero.mp hz
        have hp' : dist p p0 ≤ 1 := le_of_lt (Metric.mem_ball.mp hp)
        simpa [Function.uncurry] using hC p z hp' hz'
      · rw [Set.indicator_of_not_mem hz]
        have hz' : max S 0 < ‖z‖ := by
          rw [mem_closedBall_norm_zero] at hz
          exact lt_of_not_ge hz
        have hlt : S < ‖z‖ := lt_of_le_of_lt (le_max_left _ _) hz'
        simp [hS p z hlt]
    · exact hbound_int
    · refine ae_of_all _ fun z => ?_
      exact (hF.comp (contDiff_id.prod
        (contDiff_const : ContDiff ℝ ⊤ fun _ : P => z))).continuous.continuousOn
  | succ n ih =>
    intro E _ _ _ F hF S hS p0
    let F' : P → R3 → P →L[ℝ] E := fun p z => fderiv ℝ (fun q => F q z) p
    have hF' : ContDiff ℝ ⊤ (Function.uncurry F') := slice_fderiv_contDiff hF
    have hS' : ∀ p z, S < ‖z‖ → F' p z = 0 := fun p z hz => slice_fderiv_vanish hS p z hz
    rw [contDiffAt_succ_iff_hasFDerivAt]
    refine ⟨fun p => ∫ z, F' p z ∂(volume : Measure R3), ?_, ?_⟩
    · refine ⟨Metric.ball p0 1, Metric.ball_mem_nhds _ one_pos, fun p _hp => ?_⟩
      simpa [F'] using hasFDerivAt_zIntegral F hF hS one_pos (p0 := p)
    · exact ih (E := P →L[ℝ] E) F' hF' (S := S) hS' p0

private lemma exists_norm_le_on_closedBall_Icc
    {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup E] {G : P × ℝ → E} (hG : Continuous G) (p0 : P) (ε a b : ℝ) :
    ∃ C : ℝ, ∀ p t, dist p p0 ≤ ε → t ∈ Set.Icc a b → ‖G (p, t)‖ ≤ C := by
  obtain ⟨C, hC⟩ :=
    ((isCompact_closedBall p0 ε).prod isCompact_Icc).image (continuous_norm.comp hG) |>.bddAbove
  refine ⟨max C 0, ?_⟩
  intro p t hp ht
  by_cases hε : 0 ≤ ε
  · have hmem : (p, t) ∈ Metric.closedBall p0 ε ×ˢ Set.Icc a b :=
      ⟨by simpa [Metric.mem_closedBall] using hp, ht⟩
    exact (hC ⟨(p, t), hmem, rfl⟩).trans (le_max_left _ _)
  · exact absurd dist_nonneg (not_le.mpr (lt_of_le_of_lt hp (lt_of_not_ge hε)))

private lemma slice_fderiv_real
    {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : P → ℝ → E} (hF : ContDiff ℝ ⊤ (Function.uncurry F)) (p : P) (t : ℝ) :
    fderiv ℝ (fun q => F q t) p =
      (fderiv ℝ (Function.uncurry F) (p, t)).comp (ContinuousLinearMap.inl ℝ P ℝ) := by
  have hΦ : HasFDerivAt (Function.uncurry F)
      (fderiv ℝ (Function.uncurry F) (p, t)) (p, t) :=
    ((hF.differentiable le_top).differentiableAt).hasFDerivAt
  exact (hΦ.comp p (hasFDerivAt_prod_mk_left (𝕜 := ℝ) p t)).fderiv

private lemma slice_fderiv_real_contDiff
    {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : P → ℝ → E} (hF : ContDiff ℝ ⊤ (Function.uncurry F)) :
    ContDiff ℝ ⊤ (Function.uncurry fun p t => fderiv ℝ (fun q => F q t) p) := by
  let L : ((P × ℝ) →L[ℝ] E) →L[ℝ] P →L[ℝ] E :=
    (ContinuousLinearMap.compL ℝ P (P × ℝ) E).flip (ContinuousLinearMap.inl ℝ P ℝ)
  have hfun : Function.uncurry (fun p t => fderiv ℝ (fun q => F q t) p) =
      fun q : P × ℝ => L (fderiv ℝ (Function.uncurry F) q) := by
    funext q
    simp only [Function.uncurry]
    rw [slice_fderiv_real hF q.1 q.2]
    simp [L, ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply]
  rw [hfun]
  exact L.contDiff.comp (contDiff_top_iff_fderiv.mp hF).2

private lemma hasFDerivAt_intervalIntegral
    {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : P → ℝ → E) (hF : ContDiff ℝ ⊤ (Function.uncurry F))
    {a b : ℝ} (hab : a ≤ b) {p0 : P} {ε : ℝ} (hε : 0 < ε) :
    HasFDerivAt (fun p => ∫ t in a..b, F p t)
      (∫ t in a..b, fderiv ℝ (fun q => F q t) p0) p0 := by
  let F' : P → ℝ → P →L[ℝ] E := fun p t => fderiv ℝ (fun q => F q t) p
  obtain ⟨C, hC⟩ := exists_norm_le_on_closedBall_Icc
    (G := Function.uncurry F') (slice_fderiv_real_contDiff hF).continuous p0 ε a b
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le''
    (F := F) (F' := F') (x₀ := p0) (ε := ε) (a := a) (b := b)
    (bound := fun _ => C) (μ := (volume : Measure ℝ)) hε
  · exact Filter.Eventually.of_forall fun p =>
      (hF.continuous.comp (continuous_const.prod_mk continuous_id)).aestronglyMeasurable
  · exact (hF.continuous.comp
      (continuous_const.prod_mk continuous_id)).intervalIntegrable a b
  · exact ((slice_fderiv_real_contDiff hF).continuous.comp
      (continuous_const.prod_mk continuous_id)).aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_uIoc]
    refine Filter.Eventually.of_forall fun t ht => ?_
    intro p hp
    have ht' : t ∈ Set.Icc a b := by
      rw [← Set.uIcc_of_le hab]
      exact Set.uIoc_subset_uIcc ht
    have hp' : dist p p0 ≤ ε := le_of_lt (Metric.mem_ball.mp hp)
    simpa [F', Function.uncurry] using hC p t hp' ht'
  · exact (continuous_const : Continuous fun _ : ℝ => C).intervalIntegrable a b
  · refine ae_of_all _ fun t p _hp =>
      ((hF.comp (contDiff_id.prod (contDiff_const : ContDiff ℝ ⊤ fun _ : P => t))).differentiable
        le_top).differentiableAt.hasFDerivAt

set_option maxHeartbeats 800000 in
private lemma contDiffAt_intervalIntegral.{u}
    {P : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {a b : ℝ} (hab : a ≤ b) (n : ℕ) {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (F : P → ℝ → E) (hF : ContDiff ℝ ⊤ (Function.uncurry F)) (p0 : P) :
    ContDiffAt ℝ n (fun p => ∫ t in a..b, F p t) p0 := by
  suffices ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      (F : P → ℝ → E), ContDiff ℝ ⊤ (Function.uncurry F) → ∀ p0 : P,
      ContDiffAt ℝ n (fun p => ∫ t in a..b, F p t) p0 by
    exact this F hF p0
  induction n with
  | zero =>
    intro E _ _ _ F hF p0
    rw [Nat.cast_zero, contDiffAt_zero]
    obtain ⟨C, hC⟩ := exists_norm_le_on_closedBall_Icc
      (G := Function.uncurry F) hF.continuous p0 1 a b
    refine ⟨Metric.ball p0 1, Metric.ball_mem_nhds _ one_pos, ?_⟩
    have heq : (fun p => ∫ t in a..b, F p t) =
        fun p => ∫ t in Set.Ioc a b, F p t ∂(volume : Measure ℝ) := by
      ext p
      exact _root_.intervalIntegral.integral_of_le hab
    rw [heq]
    apply continuousOn_of_dominated
      (μ := (volume : Measure ℝ).restrict (Set.Ioc a b)) (bound := fun _ => C)
    · intro p hp
      exact (hF.continuous.comp (continuous_const.prod_mk continuous_id)).aestronglyMeasurable
    · intro p hp
      rw [ae_restrict_iff' measurableSet_Ioc]
      refine Filter.Eventually.of_forall fun t ht => ?_
      have ht' : t ∈ Set.Icc a b := Set.Ioc_subset_Icc_self ht
      have hp' : dist p p0 ≤ 1 := le_of_lt (Metric.mem_ball.mp hp)
      simpa [Function.uncurry] using hC p t hp' ht'
    · exact integrableOn_const.2 (Or.inr measure_Ioc_lt_top)
    · refine Filter.Eventually.of_forall fun t => ?_
      exact (hF.comp (contDiff_id.prod
        (contDiff_const : ContDiff ℝ ⊤ fun _ : P => t))).continuous.continuousOn
  | succ n ih =>
    intro E _ _ _ F hF p0
    let F' : P → ℝ → P →L[ℝ] E := fun p t => fderiv ℝ (fun q => F q t) p
    have hF' : ContDiff ℝ ⊤ (Function.uncurry F') := slice_fderiv_real_contDiff hF
    rw [contDiffAt_succ_iff_hasFDerivAt]
    refine ⟨fun p => ∫ t in a..b, F' p t, ?_, ?_⟩
    · refine ⟨Metric.ball p0 1, Metric.ball_mem_nhds _ one_pos, fun p _hp => ?_⟩
      simpa [F'] using hasFDerivAt_intervalIntegral F hF hab one_pos (p0 := p)
    · exact ih (E := P →L[ℝ] E) F' hF' p0

private lemma bogovskiiIntegrand_contDiff (omega : BogovskiiCutoff) (R : ℝ) {f : R3 → ℝ}
    (hf : ContDiff ℝ ⊤ f) :
    ContDiff ℝ ⊤ (Function.uncurry fun (p : R3 × ℝ) (z : R3) =>
      bogovskiiDensity omega R p.2 f p.1 z • z) := by
  have hx : ContDiff ℝ ⊤ (fun q : (R3 × ℝ) × R3 => q.1.1) := contDiff_fst.comp contDiff_fst
  have ht : ContDiff ℝ ⊤ (fun q : (R3 × ℝ) × R3 => q.1.2) := contDiff_snd.comp contDiff_fst
  have hz : ContDiff ℝ ⊤ (fun q : (R3 × ℝ) × R3 => q.2) := contDiff_snd
  have hargω : ContDiff ℝ ⊤ (fun q : (R3 × ℝ) × R3 => q.1.1 + (1 - q.1.2) • q.2) :=
    hx.add ((contDiff_const.sub ht).smul hz)
  have hargf : ContDiff ℝ ⊤ (fun q : (R3 × ℝ) × R3 => q.1.1 - q.1.2 • q.2) :=
    hx.sub (ht.smul hz)
  have hprod : ContDiff ℝ ⊤ (fun q : (R3 × ℝ) × R3 =>
      bogovskii_cutoff omega R (q.1.1 + (1 - q.1.2) • q.2) *
        f (q.1.1 - q.1.2 • q.2)) :=
    ((bogovskii_cutoff_smooth omega R).comp hargω).mul (hf.comp hargf)
  have hvec : ContDiff ℝ ⊤ (fun q : (R3 × ℝ) × R3 =>
      (bogovskii_cutoff omega R (q.1.1 + (1 - q.1.2) • q.2) *
        f (q.1.1 - q.1.2 • q.2)) • q.2) := hprod.smul hz
  have hfun : Function.uncurry (fun (p : R3 × ℝ) z =>
      bogovskiiDensity omega R p.2 f p.1 z • z) = fun q =>
      (bogovskii_cutoff omega R (q.1.1 + (1 - q.1.2) • q.2) *
        f (q.1.1 - q.1.2 • q.2)) • q.2 := by
    funext q
    simp [Function.uncurry, bogovskiiDensity]
  rw [hfun]
  exact hvec

set_option maxHeartbeats 2000000 in
lemma bogovskiiNonsingular_smooth (omega : BogovskiiCutoff) {R : ℝ} (hR : 0 < R)
    {f : R3 → ℝ} (hf : ContDiff ℝ ⊤ f) (hfsupp : Function.support f ⊆ ballR R) :
    ContDiff ℝ ⊤ (bogovskiiNonsingular omega R f) := by
  let F : (R3 × ℝ) → R3 → R3 := fun p z => bogovskiiDensity omega R p.2 f p.1 z • z
  have hF : ContDiff ℝ ⊤ (Function.uncurry F) := bogovskiiIntegrand_contDiff omega R hf
  have hS : ∀ p z, 2 * R < ‖z‖ → F p z = 0 := by
    intro p z hz
    rw [show F p z = bogovskiiDensity omega R p.2 f p.1 z • z from rfl,
      bogovskiiDensity_eq_zero_of_large_z omega hR hfsupp p.2 p.1 z (le_of_lt hz),
      zero_smul]
  let H : R3 × ℝ → R3 := fun p => ∫ z, F p z ∂(volume : Measure R3)
  have hH : ContDiff ℝ ⊤ H := by
    rw [contDiff_iff_contDiffAt]
    intro p
    rw [contDiffAt_top]
    intro n
    simpa [H, F] using contDiffAt_zIntegral n F hF hS p
  have hslice : ContDiff ℝ ⊤ (Function.uncurry fun x t => H (x, t)) := by
    have heq : Function.uncurry (fun x t => H (x, t)) = H := by
      funext q
      simp [Function.uncurry]
    simpa [heq] using hH
  rw [contDiff_iff_contDiffAt]
  intro x
  rw [contDiffAt_top]
  intro n
  have hAt := contDiffAt_intervalIntegral (zero_le_one : (0 : ℝ) ≤ 1) n
    (fun x t => H (x, t)) hslice x
  simpa [bogovskiiNonsingular, H, F] using hAt

private lemma integral_add_right {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (g : R3 → E) (v : R3) :
    ∫ z, g (z + v) ∂(volume : Measure R3) = ∫ z, g z ∂(volume : Measure R3) := by
  have hpres : MeasurePreserving (⇑(MeasurableEquiv.addRight v))
      (volume : Measure R3) (volume : Measure R3) := by
    simpa [MeasurableEquiv.coe_addRight] using
      measurePreserving_add_right (volume : Measure R3) v
  exact hpres.integral_comp' g

private lemma integral_comp_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (g : R3 → E) :
    ∫ z, g (-z) ∂(volume : Measure R3) = ∫ z, g z ∂(volume : Measure R3) := by
  have hneg : ∀ z : R3, -z = (-1 : ℝ) • z := fun z => by simp
  simp_rw [hneg]
  have h := (volume : Measure R3).integral_comp_smul g (-1)
  have hfin : |((-1 : ℝ) ^ finrank ℝ R3)⁻¹| = 1 := by
    rw [finrank_R3]
    norm_num
  rw [h, hfin, one_smul]

private lemma integral_comp_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (g : R3 → E) (x : R3) :
    ∫ z, g (x - z) ∂(volume : Measure R3) = ∫ z, g z ∂(volume : Measure R3) := by
  have hneg : ∫ z, g (x + -z) = ∫ w, g (x + w) := by
    simpa using integral_comp_neg (fun w => g (x + w))
  have hadd : ∫ w, g (w + x) = ∫ w, g w := integral_add_right g x
  have hcomm : ∀ w, x + w = w + x := fun w => add_comm _ _
  simpa [sub_eq_add_neg, hcomm] using hneg.trans (by simpa [hcomm] using hadd)

/-- For `t > 0`, `z = t⁻¹(x - y)` turns the nonsingular slice into the reparametrized ray.
The Jacobian `t⁻³` and the factor `t⁻¹` from `z` multiply to `t⁻⁴`. -/
private lemma bogovskiiSlice_reparam (omega : BogovskiiCutoff) (R : ℝ) (f : R3 → ℝ)
    (x : R3) {t : ℝ} (ht : 0 < t) :
    (∫ z, bogovskiiDensity omega R t f x z • z ∂(volume : Measure R3)) =
      ∫ y, (f y * bogovskii_cutoff omega R (y + t⁻¹ • (x - y)) * (t ^ 4)⁻¹) • (x - y)
        ∂(volume : Measure R3) := by
  let F : R3 → R3 := fun z => bogovskiiDensity omega R t f x z • z
  have hscale := (volume : Measure R3).integral_comp_smul F t⁻¹
  have hfin : |(t⁻¹ ^ finrank ℝ R3)⁻¹| = t ^ 3 := by
    rw [finrank_R3, inv_pow, inv_inv, abs_of_nonneg (pow_nonneg ht.le _)]
  have hscale' : ∫ v, F (t⁻¹ • v) = (t ^ 3) • ∫ z, F z := by
    rw [hfin] at hscale
    exact hscale
  have hF : ∫ z, F z = (t ^ 3)⁻¹ • ∫ v, F (t⁻¹ • v) := by
    rw [hscale', smul_smul, inv_mul_cancel₀ (pow_ne_zero 3 ht.ne'), one_smul]
  let ψ : R3 → R3 := fun y =>
    (f y * bogovskii_cutoff omega R (y + t⁻¹ • (x - y))) • (t⁻¹ • (x - y))
  have hpoint : ∀ v, F (t⁻¹ • v) = ψ (x - v) := by
    intro v
    simp only [F, ψ, bogovskiiDensity]
    have hy : x - t • (t⁻¹ • v) = x - v := by
      rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
    have hv : x - (x - v) = v := by module
    have hω : x + (1 - t) • (t⁻¹ • v) = (x - v) + t⁻¹ • v := by
      rw [smul_smul]
      have hcoeff : (1 - t) * t⁻¹ = t⁻¹ - 1 := by
        rw [sub_mul, one_mul, mul_inv_cancel₀ ht.ne']
      rw [hcoeff, sub_smul, one_smul]
      module
    rw [hy, hω, hv, mul_comm]
  have hpsi : ∫ v, F (t⁻¹ • v) = ∫ y, ψ y := by
    simpa [hpoint] using integral_comp_sub ψ x
  rw [hF, hpsi, ← integral_smul]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only [ψ, smul_smul]
  have hpow : (t ^ 3)⁻¹ * t⁻¹ = (t ^ 4)⁻¹ := by
    rw [← mul_inv, ← pow_succ]
  have hmul : (t ^ 3)⁻¹ * (f y * bogovskii_cutoff omega R (y + t⁻¹ • (x - y)) * t⁻¹) =
      f y * bogovskii_cutoff omega R (y + t⁻¹ • (x - y)) * (t ^ 4)⁻¹ := by
    calc
      (t ^ 3)⁻¹ * (f y * bogovskii_cutoff omega R (y + t⁻¹ • (x - y)) * t⁻¹) =
          f y * bogovskii_cutoff omega R (y + t⁻¹ • (x - y)) * ((t ^ 3)⁻¹ * t⁻¹) := by ring
      _ = f y * bogovskii_cutoff omega R (y + t⁻¹ • (x - y)) * (t ^ 4)⁻¹ := by rw [hpow]
  rw [hmul]

private lemma bogovskiiScalar_zero (omega : BogovskiiCutoff) {R : ℝ} (hR : 0 < R)
    (f : R3 → ℝ) (x : R3) :
    (∫ z, bogovskiiDensity omega R 0 f x z ∂(volume : Measure R3)) = f x := by
  have hden : ∀ z, bogovskiiDensity omega R 0 f x z =
      bogovskii_cutoff omega R (x + z) * f x := by
    intro z
    simp [bogovskiiDensity, sub_zero, one_smul, zero_smul]
  simp_rw [hden, integral_mul_right]
  have htr : ∫ z, bogovskii_cutoff omega R (x + z) ∂(volume : Measure R3) =
      ∫ z, bogovskii_cutoff omega R z ∂(volume : Measure R3) := by
    simpa [add_comm] using integral_add_right (bogovskii_cutoff omega R) x
  rw [htr, bogovskii_cutoff_integral omega hR, one_mul]

private lemma bogovskiiScalar_one (omega : BogovskiiCutoff) (R : ℝ) (f : R3 → ℝ)
    (hf0 : (∫ y, f y ∂(volume : Measure R3)) = 0) (x : R3) :
    (∫ z, bogovskiiDensity omega R 1 f x z ∂(volume : Measure R3)) = 0 := by
  have hden : ∀ z, bogovskiiDensity omega R 1 f x z =
      bogovskii_cutoff omega R x * f (x - z) := by
    intro z
    simp [bogovskiiDensity, sub_self, zero_smul, one_smul]
  simp_rw [hden, integral_mul_left, integral_comp_sub f x, hf0, mul_zero]

private lemma divClassical_eq_fderiv_sum {v : R3 → R3} {x : R3}
    (hv : DifferentiableAt ℝ v x) :
    divClassical v x =
      ∑ i : Fin 3, (fderiv ℝ v x (EuclideanSpace.single i (1 : ℝ))) i := by
  rw [divClassical]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coordinateDerivative]
  have hpath : HasDerivAt (fun t : ℝ => x + t • EuclideanSpace.single i (1 : ℝ))
      (EuclideanSpace.single i (1 : ℝ)) 0 := by
    have hsmul : HasDerivAt (fun t : ℝ => t • EuclideanSpace.single i (1 : ℝ))
        ((1 : ℝ) • EuclideanSpace.single i (1 : ℝ)) 0 :=
      (hasDerivAt_id' 0).smul_const _
    have hadd := (hasDerivAt_const 0 x).add hsmul
    simp only [one_smul, zero_add] at hadd
    exact hadd
  have hv0 : HasFDerivAt v (fderiv ℝ v x)
      ((fun t : ℝ => x + t • EuclideanSpace.single i (1 : ℝ)) 0) := by
    simpa using hv.hasFDerivAt
  have hcomp : HasDerivAt (fun t : ℝ => v (x + t • EuclideanSpace.single i (1 : ℝ)))
      (fderiv ℝ v x (EuclideanSpace.single i (1 : ℝ))) 0 := by
    have hcomp' := hv0.comp_hasDerivAt 0 hpath
    simp only [Function.comp_def] at hcomp'
    exact hcomp'
  have hproj : HasDerivAt (fun t : ℝ => (v (x + t • EuclideanSpace.single i (1 : ℝ))) i)
      ((fderiv ℝ v x (EuclideanSpace.single i (1 : ℝ))) i) 0 := by
    have hp := (EuclideanSpace.proj i).hasFDerivAt.comp_hasDerivAt 0 hcomp
    simp only [Function.comp_def, EuclideanSpace.proj_apply] at hp
    exact hp
  exact hproj.deriv

private lemma div_smul_const {c : R3 → ℝ} {x : R3} (hc : DifferentiableAt ℝ c x) (z : R3) :
    divClassical (fun y => c y • z) x = fderiv ℝ c x z := by
  rw [divClassical_eq_fderiv_sum (hc.smul_const z), fderiv_smul_const hc z]
  simp only [ContinuousLinearMap.smulRight_apply]
  have hcoord : ∀ i, ((fderiv ℝ c x (EuclideanSpace.single i (1 : ℝ))) • z) i =
      fderiv ℝ c x (EuclideanSpace.single i 1) * z i := fun i => by
    simp
  simp_rw [hcoord]
  rw [fderiv_apply_sum (fderiv ℝ c x) z]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- Moving the base point in the direction `v` differentiates the density by the
product rule. At `v = z` this is the negative of the `t`-derivative. -/
private lemma hasDerivAt_density_spatial (omega : BogovskiiCutoff) (R : ℝ)
    {f : R3 → ℝ} (hf : ContDiff ℝ ⊤ f) (t : ℝ) (x z v : R3) :
    HasDerivAt (fun s : ℝ => bogovskiiDensity omega R t f (x + s • v) z)
      ((fderiv ℝ (bogovskii_cutoff omega R) (x + (1 - t) • z)) v * f (x - t • z) +
        bogovskii_cutoff omega R (x + (1 - t) • z) *
          (fderiv ℝ f (x - t • z)) v) 0 := by
  have hsmul : HasDerivAt (fun s : ℝ => s • v) ((1 : ℝ) • v) 0 :=
    (hasDerivAt_id' 0).smul_const v
  have hωpath : HasDerivAt (fun s : ℝ => (x + (1 - t) • z) + s • v) v 0 := by
    have hadd := (hasDerivAt_const 0 (x + (1 - t) • z)).add hsmul
    simp only [one_smul, zero_add] at hadd
    exact hadd
  have hfpath : HasDerivAt (fun s : ℝ => (x - t • z) + s • v) v 0 := by
    have hadd := (hasDerivAt_const 0 (x - t • z)).add hsmul
    simp only [one_smul, zero_add] at hadd
    exact hadd
  have hdiffω : DifferentiableAt ℝ (bogovskii_cutoff omega R) (x + (1 - t) • z) :=
    ((bogovskii_cutoff_smooth omega R).differentiable le_top).differentiableAt
  have hdifff : DifferentiableAt ℝ f (x - t • z) :=
    (hf.differentiable le_top).differentiableAt
  have hω0 : HasFDerivAt (bogovskii_cutoff omega R)
      (fderiv ℝ (bogovskii_cutoff omega R) (x + (1 - t) • z))
      ((fun s : ℝ => (x + (1 - t) • z) + s • v) 0) := by
    simpa using hdiffω.hasFDerivAt
  have hf0 : HasFDerivAt f (fderiv ℝ f (x - t • z))
      ((fun s : ℝ => (x - t • z) + s • v) 0) := by
    simpa using hdifff.hasFDerivAt
  have hω := hω0.comp_hasDerivAt 0 hωpath
  have hf' := hf0.comp_hasDerivAt 0 hfpath
  have hmul := hω.mul hf'
  have hfun : ∀ s : ℝ, bogovskiiDensity omega R t f (x + s • v) z =
      (bogovskii_cutoff omega R ∘ fun u : ℝ => (x + (1 - t) • z) + u • v) s *
        (f ∘ fun u : ℝ => (x - t • z) + u • v) s := by
    intro s
    simp only [Function.comp_def, bogovskiiDensity]
    have h1 : (x + s • v) + (1 - t) • z = (x + (1 - t) • z) + s • v := by module
    have h2 : (x + s • v) - t • z = (x - t • z) + s • v := by module
    rw [h1, h2]
  have hmul' := hmul.congr_of_eventuallyEq (Filter.Eventually.of_forall hfun)
  have hderiv :
      (fderiv ℝ (bogovskii_cutoff omega R) (x + (1 - t) • z)) v *
          (f ∘ fun u : ℝ => (x - t • z) + u • v) 0 +
        (bogovskii_cutoff omega R ∘ fun u : ℝ => (x + (1 - t) • z) + u • v) 0 *
          (fderiv ℝ f (x - t • z)) v =
      (fderiv ℝ (bogovskii_cutoff omega R) (x + (1 - t) • z)) v * f (x - t • z) +
        bogovskii_cutoff omega R (x + (1 - t) • z) *
          (fderiv ℝ f (x - t • z)) v := by
    simp [Function.comp_def, zero_smul, add_zero]
  exact hmul'.congr_deriv hderiv

private lemma density_differentiableAt (omega : BogovskiiCutoff) (R t : ℝ)
    {f : R3 → ℝ} (hf : ContDiff ℝ ⊤ f) (x z : R3) :
    DifferentiableAt ℝ (fun y => bogovskiiDensity omega R t f y z) x := by
  have hω : DifferentiableAt ℝ (fun y => bogovskii_cutoff omega R (y + (1 - t) • z)) x :=
    ((bogovskii_cutoff_smooth omega R).differentiable le_top).differentiableAt.comp x
      ((differentiableAt_id.add (differentiableAt_const ((1 - t) • z))))
  have hf' : DifferentiableAt ℝ (fun y => f (y - t • z)) x :=
    (hf.differentiable le_top).differentiableAt.comp x
      (differentiableAt_id.sub (differentiableAt_const (t • z)))
  simpa [bogovskiiDensity] using hω.mul hf'

private lemma fderiv_density_apply_z (omega : BogovskiiCutoff) (R : ℝ)
    {f : R3 → ℝ} (hf : ContDiff ℝ ⊤ f) (t : ℝ) (x z : R3) :
    (fderiv ℝ (fun y => bogovskiiDensity omega R t f y z) x) z =
      - deriv (fun s => bogovskiiDensity omega R s f x z) t := by
  have hpath : HasDerivAt (fun s : ℝ => x + s • z) z 0 := by
    have hsmul : HasDerivAt (fun s : ℝ => s • z) ((1 : ℝ) • z) 0 :=
      (hasDerivAt_id' 0).smul_const z
    have hadd := (hasDerivAt_const 0 x).add hsmul
    simp only [one_smul, zero_add] at hadd
    exact hadd
  have hden0 : HasFDerivAt (fun y => bogovskiiDensity omega R t f y z)
      (fderiv ℝ (fun y => bogovskiiDensity omega R t f y z) x)
      ((fun s : ℝ => x + s • z) 0) := by
    simpa using (density_differentiableAt omega R t hf x z).hasFDerivAt
  have hdir : HasDerivAt (fun s : ℝ => bogovskiiDensity omega R t f (x + s • z) z)
      ((fderiv ℝ (fun y => bogovskiiDensity omega R t f y z) x) z) 0 := by
    have hdir' := hden0.comp_hasDerivAt 0 hpath
    simp only [Function.comp_def] at hdir'
    exact hdir'
  have hspat := hasDerivAt_density_spatial omega R hf t x z z
  have ht := hasDerivAt_bogovskiiDensity_t omega R f hf x z t
  have hagree : (fderiv ℝ (fun y => bogovskiiDensity omega R t f y z) x) z =
      (fderiv ℝ (bogovskii_cutoff omega R) (x + (1 - t) • z)) z * f (x - t • z) +
        bogovskii_cutoff omega R (x + (1 - t) • z) *
          (fderiv ℝ f (x - t • z)) z := by
    rw [← hspat.deriv, hdir.deriv]
  rw [hagree]
  have htval := ht.deriv
  rw [← neg_neg ((fderiv ℝ (bogovskii_cutoff omega R) (x + (1 - t) • z)) z * f (x - t • z) +
    bogovskii_cutoff omega R (x + (1 - t) • z) * (fderiv ℝ f (x - t • z)) z), ← htval]

private lemma bogovskiiDensity_contDiff_tz (omega : BogovskiiCutoff) (R : ℝ) (x : R3)
    {f : R3 → ℝ} (hf : ContDiff ℝ ⊤ f) :
    ContDiff ℝ ⊤ (Function.uncurry fun (t : ℝ) (z : R3) =>
      bogovskiiDensity omega R t f x z) := by
  have ht : ContDiff ℝ ⊤ (fun q : ℝ × R3 => q.1) := contDiff_fst
  have hz : ContDiff ℝ ⊤ (fun q : ℝ × R3 => q.2) := contDiff_snd
  have hargω : ContDiff ℝ ⊤ (fun q : ℝ × R3 => x + (1 - q.1) • q.2) :=
    contDiff_const.add ((contDiff_const.sub ht).smul hz)
  have hargf : ContDiff ℝ ⊤ (fun q : ℝ × R3 => x - q.1 • q.2) :=
    contDiff_const.sub (ht.smul hz)
  have hprod : ContDiff ℝ ⊤ (fun q : ℝ × R3 =>
      bogovskii_cutoff omega R (x + (1 - q.1) • q.2) * f (x - q.1 • q.2)) :=
    ((bogovskii_cutoff_smooth omega R).comp hargω).mul (hf.comp hargf)
  have hfun : Function.uncurry (fun t z => bogovskiiDensity omega R t f x z) =
      fun q => bogovskii_cutoff omega R (x + (1 - q.1) • q.2) * f (x - q.1 • q.2) := by
    funext q
    simp [Function.uncurry, bogovskiiDensity]
  rw [hfun]
  exact hprod

set_option maxHeartbeats 800000 in
private lemma hasDerivAt_bogovskiiScalar (omega : BogovskiiCutoff) {R : ℝ} (hR : 0 < R)
    {f : R3 → ℝ} (hf : ContDiff ℝ ⊤ f) (hfsupp : Function.support f ⊆ ballR R)
    (x : R3) (t : ℝ) :
    HasDerivAt (fun s => ∫ z, bogovskiiDensity omega R s f x z ∂(volume : Measure R3))
      (∫ z, deriv (fun s => bogovskiiDensity omega R s f x z) t ∂(volume : Measure R3)) t := by
  let F : ℝ → R3 → ℝ := fun s z => bogovskiiDensity omega R s f x z
  have hF : ContDiff ℝ ⊤ (Function.uncurry F) := bogovskiiDensity_contDiff_tz omega R x hf
  have hS : ∀ s z, 2 * R < ‖z‖ → F s z = 0 := fun s z hz =>
    bogovskiiDensity_eq_zero_of_large_z omega hR hfsupp s x z (le_of_lt hz)
  have hfd := hasFDerivAt_zIntegral F hF hS one_pos (p0 := t)
  have hint : Integrable (fun z => fderiv ℝ (fun q => F q z) t) (volume : Measure R3) := by
    have hcont : Continuous (fun z => fderiv ℝ (fun q => F q z) t) :=
      (slice_fderiv_contDiff hF).continuous.comp (continuous_const.prod_mk continuous_id)
    have hsupp : Function.support (fun z => fderiv ℝ (fun q => F q z) t) ⊆
        Metric.closedBall (0 : R3) (max (2 * R) 0) := by
      rw [Function.support_subset_iff']
      intro z hz
      rw [mem_closedBall_norm_zero, not_le] at hz
      exact slice_fderiv_vanish hS t z (lt_of_le_of_lt (le_max_left _ _) hz)
    exact hcont.integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact
        (isCompact_closedBall (0 : R3) (max (2 * R) 0)) hsupp)
  have happly := ContinuousLinearMap.integral_apply hint (1 : ℝ)
  have hpt : ∀ z, (fderiv ℝ (fun q => F q z) t) (1 : ℝ) =
      deriv (fun s => bogovskiiDensity omega R s f x z) t := by
    intro z
    have hdiff : DifferentiableAt ℝ (fun q => F q z) t :=
      ((hF.comp (contDiff_id.prod (contDiff_const : ContDiff ℝ ⊤ fun _ : ℝ => z))).differentiable
        le_top).differentiableAt
    exact hdiff.hasFDerivAt.hasDerivAt.deriv.symm
  have hderiv := hfd.hasDerivAt
  have hfun : (∫ z, fderiv ℝ (fun q => F q z) t ∂(volume : Measure R3)) (1 : ℝ) =
      ∫ z, deriv (fun s => bogovskiiDensity omega R s f x z) t ∂(volume : Measure R3) := by
    rw [happly]
    refine integral_congr_ae (ae_of_all _ hpt)
  simpa [F, hfun] using hderiv

private def divTrace : (R3 →L[ℝ] R3) →L[ℝ] ℝ :=
  ∑ i : Fin 3, (EuclideanSpace.proj i).comp
    (ContinuousLinearMap.apply ℝ R3 (EuclideanSpace.single i (1 : ℝ)))

private lemma divTrace_apply (A : R3 →L[ℝ] R3) :
    divTrace A = ∑ i : Fin 3, (A (EuclideanSpace.single i (1 : ℝ))) i := by
  simp [divTrace, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply, EuclideanSpace.proj_apply]

private lemma divClassical_eq_divTrace {v : R3 → R3} {x : R3} (hv : DifferentiableAt ℝ v x) :
    divClassical v x = divTrace (fderiv ℝ v x) := by
  rw [divClassical_eq_fderiv_sum hv, divTrace_apply]

private lemma density_smul_contDiff_fixed_t (omega : BogovskiiCutoff) (R t : ℝ)
    {f : R3 → ℝ} (hf : ContDiff ℝ ⊤ f) :
    ContDiff ℝ ⊤ (Function.uncurry fun (y : R3) (z : R3) =>
      bogovskiiDensity omega R t f y z • z) := by
  have hjoint := bogovskiiIntegrand_contDiff omega R hf
  have hmap : ContDiff ℝ ⊤
      (fun q : R3 × R3 => ((q.1, t), q.2) : R3 × R3 → (R3 × ℝ) × R3) :=
    ((contDiff_fst.prod (contDiff_const : ContDiff ℝ ⊤ fun _ : R3 × R3 => t)).prod contDiff_snd)
  have heq : Function.uncurry (fun y z => bogovskiiDensity omega R t f y z • z) =
      (Function.uncurry fun (p : R3 × ℝ) z => bogovskiiDensity omega R p.2 f p.1 z • z) ∘
        fun q : R3 × R3 => ((q.1, t), q.2) := by
    funext q
    simp [Function.uncurry]
  rw [heq]
  exact hjoint.comp hmap

private lemma integrable_slice_fderiv {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : P → R3 → E) (hF : ContDiff ℝ ⊤ (Function.uncurry F))
    {S : ℝ} (hS : ∀ p z, S < ‖z‖ → F p z = 0) (p : P) :
    Integrable (fun z => fderiv ℝ (fun q => F q z) p) (volume : Measure R3) := by
  have hcont : Continuous (fun z => fderiv ℝ (fun q => F q z) p) :=
    (slice_fderiv_contDiff hF).continuous.comp (continuous_const.prod_mk continuous_id)
  have hsupp : Function.support (fun z => fderiv ℝ (fun q => F q z) p) ⊆
      Metric.closedBall (0 : R3) (max S 0) := by
    rw [Function.support_subset_iff']
    intro z hz
    rw [mem_closedBall_norm_zero, not_le] at hz
    exact slice_fderiv_vanish hS p z (lt_of_le_of_lt (le_max_left _ _) hz)
  exact hcont.integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact
      (isCompact_closedBall (0 : R3) (max S 0)) hsupp)

set_option maxHeartbeats 800000 in
private lemma trace_density_slice (omega : BogovskiiCutoff) {R : ℝ} (hR : 0 < R)
    {f : R3 → ℝ} (hf : ContDiff ℝ ⊤ f) (hfsupp : Function.support f ⊆ ballR R)
    (t : ℝ) (x : R3) :
    ∑ i : Fin 3,
        ((fderiv ℝ (fun y =>
            ∫ z, bogovskiiDensity omega R t f y z • z ∂(volume : Measure R3)) x)
          (EuclideanSpace.single i (1 : ℝ))) i =
      -(∫ z, deriv (fun s => bogovskiiDensity omega R s f x z) t ∂(volume : Measure R3)) := by
  let G : R3 → R3 → R3 := fun y z => bogovskiiDensity omega R t f y z • z
  have hG : ContDiff ℝ ⊤ (Function.uncurry G) := density_smul_contDiff_fixed_t omega R t hf
  have hS : ∀ y z, 2 * R < ‖z‖ → G y z = 0 := by
    intro y z hz
    simp [G, bogovskiiDensity_eq_zero_of_large_z omega hR hfsupp t y z (le_of_lt hz), zero_smul]
  have hfd := (hasFDerivAt_zIntegral G hG hS one_pos (p0 := x)).fderiv
  have hint := integrable_slice_fderiv G hG hS x
  rw [hfd]
  have hcomp : ∀ i : Fin 3,
      ((∫ z, fderiv ℝ (fun q => G q z) x ∂(volume : Measure R3))
        (EuclideanSpace.single i (1 : ℝ))) i =
      ∫ z, (fderiv ℝ (fun q => G q z) x (EuclideanSpace.single i (1 : ℝ))) i
        ∂(volume : Measure R3) := by
    intro i
    let L : (R3 →L[ℝ] R3) →L[ℝ] ℝ :=
      (EuclideanSpace.proj i).comp
        (ContinuousLinearMap.apply ℝ R3 (EuclideanSpace.single i (1 : ℝ)))
    have happly := L.integral_comp_comm hint
    simpa [L, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
      EuclideanSpace.proj_apply] using happly.symm
  simp_rw [hcomp]
  rw [← integral_finset_sum]
  · have hinner : ∀ z, ∑ i : Fin 3,
        (fderiv ℝ (fun q => G q z) x (EuclideanSpace.single i (1 : ℝ))) i =
        - deriv (fun s => bogovskiiDensity omega R s f x z) t := by
      intro z
      have hc : DifferentiableAt ℝ (fun y => bogovskiiDensity omega R t f y z) x :=
        density_differentiableAt omega R t hf x z
      have hdiv := div_smul_const hc z
      rw [divClassical_eq_fderiv_sum (hc.smul_const z)] at hdiv
      simpa [G, fderiv_density_apply_z omega R hf t x z] using hdiv
    rw [integral_congr_ae (ae_of_all _ hinner), integral_neg]
  · intro i _
    let L : (R3 →L[ℝ] R3) →L[ℝ] ℝ :=
      (EuclideanSpace.proj i).comp
        (ContinuousLinearMap.apply ℝ R3 (EuclideanSpace.single i (1 : ℝ)))
    simpa [L, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
      EuclideanSpace.proj_apply] using L.integrable_comp hint

private lemma bogovskiiScalar_ftc (omega : BogovskiiCutoff) {R : ℝ} (hR : 0 < R)
    {f : R3 → ℝ} (hf : ContDiff ℝ ⊤ f) (hfsupp : Function.support f ⊆ ballR R)
    (hf0 : (∫ y, f y ∂(volume : Measure R3)) = 0) (x : R3) :
    (∫ t in (0 : ℝ)..1,
        ∫ z, deriv (fun s => bogovskiiDensity omega R s f x z) t ∂(volume : Measure R3)) =
      - f x := by
  let σ : ℝ → ℝ := fun s => ∫ z, bogovskiiDensity omega R s f x z ∂(volume : Measure R3)
  let σ' : ℝ → ℝ := fun t =>
    ∫ z, deriv (fun s => bogovskiiDensity omega R s f x z) t ∂(volume : Measure R3)
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt σ (σ' t) t :=
    fun t _ => hasDerivAt_bogovskiiScalar omega hR hf hfsupp x t
  let F : ℝ → R3 → ℝ := fun s z => bogovskiiDensity omega R s f x z
  have hF : ContDiff ℝ ⊤ (Function.uncurry F) := bogovskiiDensity_contDiff_tz omega R x hf
  have hS : ∀ s z, 2 * R < ‖z‖ → F s z = 0 := fun s z hz =>
    bogovskiiDensity_eq_zero_of_large_z omega hR hfsupp s x z (le_of_lt hz)
  have hσ : ContDiff ℝ ⊤ σ := by
    rw [contDiff_iff_contDiffAt]
    intro t
    rw [contDiffAt_top]
    intro n
    simpa [σ, F] using contDiffAt_zIntegral n F hF hS t
  have hder_eq : deriv σ = σ' := by
    ext t
    exact (hasDerivAt_bogovskiiScalar omega hR hf hfsupp x t).deriv
  have hint : IntervalIntegrable σ' (volume : Measure ℝ) 0 1 := by
    rw [← hder_eq]
    exact (hσ.continuous_deriv (le_top : (1 : ℕ∞) ≤ ⊤)).intervalIntegrable 0 1
  have hsub := _root_.intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have h0 : σ 0 = f x := bogovskiiScalar_zero omega hR f x
  have h1 : σ 1 = 0 := bogovskiiScalar_one omega R f hf0 x
  rw [hsub, h1, h0, zero_sub]

set_option maxHeartbeats 4000000 in
lemma bogovskiiNonsingular_div (omega : BogovskiiCutoff) {R : ℝ} (hR : 0 < R)
    {f : R3 → ℝ} (hf : ContDiff ℝ ⊤ f) (hfsupp : Function.support f ⊆ ballR R)
    (hf0 : (∫ y, f y ∂(volume : Measure R3)) = 0) (x : R3) :
    divClassical (bogovskiiNonsingular omega R f) x = f x := by
  let H : R3 × ℝ → R3 := fun p =>
    ∫ z, bogovskiiDensity omega R p.2 f p.1 z • z ∂(volume : Measure R3)
  have hH : ContDiff ℝ ⊤ H := by
    let F : (R3 × ℝ) → R3 → R3 := fun p z => bogovskiiDensity omega R p.2 f p.1 z • z
    have hF : ContDiff ℝ ⊤ (Function.uncurry F) := bogovskiiIntegrand_contDiff omega R hf
    have hS : ∀ p z, 2 * R < ‖z‖ → F p z = 0 := by
      intro p z hz
      rw [show F p z = bogovskiiDensity omega R p.2 f p.1 z • z from rfl,
        bogovskiiDensity_eq_zero_of_large_z omega hR hfsupp p.2 p.1 z (le_of_lt hz), zero_smul]
    rw [contDiff_iff_contDiffAt]
    intro p
    rw [contDiffAt_top]
    intro n
    exact contDiffAt_zIntegral n F hF hS p
  let u := bogovskiiNonsingular omega R f
  have hu : u = fun y => ∫ t in (0 : ℝ)..1, H (y, t) := by
    funext y
    rfl
  have hslice : ContDiff ℝ ⊤ (Function.uncurry fun y t => H (y, t)) := by
    have heq : Function.uncurry (fun y t => H (y, t)) = H := by
      funext q
      rfl
    rw [heq]
    exact hH
  have hAt := hasFDerivAt_intervalIntegral (fun y t => H (y, t)) hslice
    (zero_le_one : (0 : ℝ) ≤ 1) one_pos (p0 := x)
  have hu_diff : DifferentiableAt ℝ u x :=
    ((bogovskiiNonsingular_smooth omega hR hf hfsupp).differentiable le_top).differentiableAt
  rw [divClassical_eq_divTrace hu_diff]
  have hfderiv : fderiv ℝ u x =
      ∫ t in (0 : ℝ)..1, fderiv ℝ (fun y => H (y, t)) x := by
    rw [hu]
    exact hAt.fderiv
  rw [hfderiv, _root_.intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1)]
  have hφ_int : IntervalIntegrable (fun t => fderiv ℝ (fun y => H (y, t)) x)
      (volume : Measure ℝ) 0 1 := by
    have hfd : ContDiff ℝ ⊤ (Function.uncurry fun y t => fderiv ℝ (fun q => H (q, t)) y) :=
      slice_fderiv_real_contDiff hslice
    have hcomp : ContDiff ℝ ⊤ (fun t : ℝ => fderiv ℝ (fun y => H (y, t)) x) := by
      have heq : (fun t : ℝ => fderiv ℝ (fun y => H (y, t)) x) =
          (Function.uncurry fun y t => fderiv ℝ (fun q => H (q, t)) y) ∘ fun t : ℝ => (x, t) := by
        funext t
        rfl
      rw [heq]
      exact hfd.comp (contDiff_const.prod contDiff_id)
    exact hcomp.continuous.intervalIntegrable 0 1
  have hint : Integrable (fun t => fderiv ℝ (fun y => H (y, t)) x)
      ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)) := by
    simpa [Set.uIoc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using hφ_int.def'
  have hcomm := (divTrace.integral_comp_comm hint).symm
  rw [hcomm]
  have hpt : ∀ t : ℝ, divTrace (fderiv ℝ (fun y => H (y, t)) x) =
      -(∫ z, deriv (fun s => bogovskiiDensity omega R s f x z) t ∂(volume : Measure R3)) := by
    intro t
    rw [divTrace_apply]
    exact trace_density_slice omega hR hf hfsupp t x
  rw [integral_congr_ae (ae_of_all _ hpt), integral_neg]
  have hftc := bogovskiiScalar_ftc omega hR hf hfsupp hf0 x
  rw [_root_.intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1)] at hftc
  rw [hftc, neg_neg]

private lemma continuousOn_reparamSlice (omega : BogovskiiCutoff) (R : ℝ)
    {f : R3 → ℝ} (hf : Continuous f) (x : R3) {ε : ℝ} (hε : 0 < ε) :
    ContinuousOn (fun p : ℝ × R3 =>
      (f p.2 * bogovskii_cutoff omega R (p.2 + p.1⁻¹ • (x - p.2)) * (p.1 ^ 4)⁻¹) • (x - p.2))
      (Set.Icc ε 1 ×ˢ (Set.univ : Set R3)) := by
  have hne : ∀ p : ℝ × R3, p ∈ Set.Icc ε 1 ×ˢ (Set.univ : Set R3) → p.1 ≠ 0 :=
    fun p hp => (lt_of_lt_of_le hε hp.1.1).ne'
  have hinv : ContinuousOn (fun p : ℝ × R3 => p.1⁻¹)
      (Set.Icc ε 1 ×ˢ (Set.univ : Set R3)) :=
    continuousOn_inv₀.comp continuous_fst.continuousOn hne
  have hcut : Continuous (bogovskii_cutoff omega R) :=
    (bogovskii_cutoff_smooth omega R).continuous
  have harg : ContinuousOn (fun p : ℝ × R3 => p.2 + p.1⁻¹ • (x - p.2))
      (Set.Icc ε 1 ×ˢ (Set.univ : Set R3)) :=
    continuous_snd.continuousOn.add
      (hinv.smul ((continuous_const.sub continuous_snd).continuousOn))
  have hpow : ContinuousOn (fun p : ℝ × R3 => (p.1 ^ 4)⁻¹)
      (Set.Icc ε 1 ×ˢ (Set.univ : Set R3)) :=
    ((continuous_fst.continuousOn.pow 4).inv₀ (fun p hp => pow_ne_zero 4 (hne p hp)))
  exact ((hf.comp_continuousOn continuous_snd.continuousOn).mul (hcut.comp_continuousOn harg)).mul
      hpow |>.smul (continuous_const.continuousOn.sub continuous_snd.continuousOn)

/-- On `ε ≤ t ≤ 1` the nonsingular slice is the ray cut at `r = 1/ε`. -/
private lemma bogovskii_truncated_eq (omega : BogovskiiCutoff) {R : ℝ} (_hR : 0 < R)
    {f : R3 → ℝ} (hf : ContDiff ℝ ⊤ f) (hfsupp : Function.support f ⊆ ballR R)
    (x : R3) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (∫ t in ε..1, ∫ z, bogovskiiDensity omega R t f x z • z ∂(volume : Measure R3)) =
      ∫ y, (∫ r in (1 : ℝ)..(ε⁻¹),
          bogovskii_cutoff omega R (y + r • (x - y)) * r ^ 2) • (f y • (x - y))
        ∂(volume : Measure R3) := by
  by_cases hεeq : ε = 1
  · subst hεeq
    simp only [inv_one]
    rw [_root_.intervalIntegral.integral_same]
    simp_rw [_root_.intervalIntegral.integral_same, zero_smul]
    simp [integral_zero]
  have hεlt : ε < 1 := lt_of_le_of_ne hε1 hεeq
  let K : ℝ → R3 → R3 := fun t y =>
    (f y * bogovskii_cutoff omega R (y + t⁻¹ • (x - y)) * (t ^ 4)⁻¹) • (x - y)
  have hK : ∀ t ∈ Set.uIcc ε 1, (∫ z, bogovskiiDensity omega R t f x z • z) = ∫ y, K t y := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le hε0 (by
      rw [Set.uIcc_of_le hε1] at ht
      exact ht.1)
    simpa [K] using bogovskiiSlice_reparam omega R f x ht0
  rw [_root_.intervalIntegral.integral_congr hK]
  let S : Set R3 := Metric.closedBall (0 : R3) R
  have hzero : ∀ t y, y ∉ S → K t y = 0 := by
    intro t y hy
    have hy' : y ∉ ballR R := fun h => hy (Metric.ball_subset_closedBall h)
    have hf0 : f y = 0 := by
      rw [← Function.nmem_support]
      exact fun hs => hy' (hfsupp hs)
    simp [K, hf0, zero_mul, zero_smul]
  have hslice : ∀ t, ∫ y in S, K t y ∂(volume : Measure R3) = ∫ y, K t y := fun t =>
    setIntegral_eq_integral_of_forall_compl_eq_zero (μ := (volume : Measure R3)) (hzero t)
  have hcont : ContinuousOn (Function.uncurry K) (Set.Icc ε 1 ×ˢ S) :=
    (continuousOn_reparamSlice omega R hf.continuous x hε0).mono (fun _ hp => ⟨hp.1, Set.mem_univ _⟩)
  have hint : IntegrableOn (Function.uncurry K) (Set.Icc ε 1 ×ˢ S) (volume : Measure (ℝ × R3)) :=
    hcont.integrableOn_compact (isCompact_Icc.prod (isCompact_closedBall _ _))
  have hswap := setIntegral_prod (μ := (volume : Measure ℝ)) (ν := (volume : Measure R3))
    (Function.uncurry K) (by simpa [Measure.volume_eq_prod] using hint)
  simp only [Function.uncurry_apply_pair] at hswap
  have hleft :
      (∫ t in ε..1, ∫ y, K t y ∂(volume : Measure R3)) =
        ∫ p in Set.Icc ε 1 ×ˢ S, Function.uncurry K p ∂(volume : Measure (ℝ × R3)) := by
    rw [_root_.intervalIntegral.integral_of_le hε1, ← integral_Icc_eq_integral_Ioc]
    have hcong :
        (∫ t in Set.Icc ε 1, ∫ y, K t y ∂(volume : Measure R3)) =
          ∫ t in Set.Icc ε 1, ∫ y in S, K t y ∂(volume : Measure R3) :=
      setIntegral_congr measurableSet_Icc fun t _ => (hslice t).symm
    rw [hcong, Measure.volume_eq_prod, ← hswap]
  have hint' : Integrable (Function.uncurry K)
      (((volume : Measure ℝ).restrict (Set.Icc ε 1)).prod
        ((volume : Measure R3).restrict S)) := by
    simpa [Measure.prod_restrict, IntegrableOn, Measure.volume_eq_prod] using hint
  have hord := integral_integral_swap (f := K) hint'
  have hyzero : ∀ y, y ∉ S →
      (∫ t in Set.Icc ε 1, K t y ∂(volume : Measure ℝ)) = 0 := by
    intro y hy
    have hfun : (fun t => K t y) = fun _ => (0 : R3) :=
      funext fun t => hzero t y hy
    rw [hfun]
    simp
  have hyint :
      (∫ y in S, ∫ t in Set.Icc ε 1, K t y ∂(volume : Measure ℝ) ∂(volume : Measure R3)) =
        ∫ y, ∫ t in Set.Icc ε 1, K t y ∂(volume : Measure ℝ) ∂(volume : Measure R3) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (μ := (volume : Measure R3)) hyzero
  have hright :
      (∫ y, ∫ t in Set.Icc ε 1, K t y ∂(volume : Measure ℝ) ∂(volume : Measure R3)) =
        ∫ p in Set.Icc ε 1 ×ˢ S, Function.uncurry K p ∂(volume : Measure (ℝ × R3)) := by
    rw [← hyint, ← hord, Measure.volume_eq_prod, hswap]
  rw [hleft, ← hright]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  have hfac :
      (∫ t in Set.Icc ε 1, K t y ∂(volume : Measure ℝ)) =
        (∫ t in Set.Icc ε 1,
            bogovskii_cutoff omega R (y + t⁻¹ • (x - y)) * (t ^ 4)⁻¹ ∂(volume : Measure ℝ)) •
          (f y • (x - y)) := by
    have hrewrite : ∀ t, K t y =
        (f y * (bogovskii_cutoff omega R (y + t⁻¹ • (x - y)) * (t ^ 4)⁻¹)) • (x - y) := by
      intro t
      simp only [K, mul_assoc]
    simp_rw [hrewrite, integral_smul_const, integral_mul_left, smul_smul]
    rw [mul_comm (f y)]
  beta_reduce
  rw [hfac]
  have hIcc : (∫ t in Set.Icc ε 1,
        bogovskii_cutoff omega R (y + t⁻¹ • (x - y)) * (t ^ 4)⁻¹ ∂(volume : Measure ℝ)) =
      ∫ t in ε..1, bogovskii_cutoff omega R (y + t⁻¹ • (x - y)) * (t ^ 4)⁻¹ := by
    rw [integral_Icc_eq_integral_Ioc, ← _root_.intervalIntegral.integral_of_le hε1]
  rw [hIcc]
  have hM : 1 < ε⁻¹ := one_lt_inv hε0 hεlt
  have hray := rayIntegral_reparam omega R x y hM
  have hdiv : 1 / ε⁻¹ = ε := by
    rw [one_div, inv_inv]
  rw [hdiv] at hray
  exact congrArg (fun s : ℝ => s • (f y • (x - y))) hray.symm

private lemma continuous_bogovskiiSlice (omega : BogovskiiCutoff) {R : ℝ} (hR : 0 < R)
    {f : R3 → ℝ} (hf : ContDiff ℝ ⊤ f) (hfsupp : Function.support f ⊆ ballR R) (x : R3) :
    Continuous (fun t : ℝ =>
      ∫ z, bogovskiiDensity omega R t f x z • z ∂(volume : Measure R3)) := by
  let F : ℝ → R3 → R3 := fun t z => bogovskiiDensity omega R t f x z • z
  have hF : ContDiff ℝ ⊤ (Function.uncurry F) := by
    have hjoint := bogovskiiIntegrand_contDiff omega R hf
    have hcomp : Function.uncurry F =
        (Function.uncurry fun (p : R3 × ℝ) (z : R3) =>
          bogovskiiDensity omega R p.2 f p.1 z • z) ∘
          fun q : ℝ × R3 => ((x, q.1), q.2) := by
      funext q
      rfl
    rw [hcomp]
    exact hjoint.comp ((contDiff_const.prod contDiff_fst).prod contDiff_snd)
  have hS : ∀ t z, 2 * R < ‖z‖ → F t z = 0 := by
    intro t z hz
    rw [show F t z = bogovskiiDensity omega R t f x z • z from rfl,
      bogovskiiDensity_eq_zero_of_large_z omega hR hfsupp t x z (le_of_lt hz), zero_smul]
  rw [continuous_iff_continuousAt]
  intro t
  exact (contDiffAt_zIntegral 0 F hF hS t).continuousAt

private lemma bogovskiiSlice_head_tendsto (omega : BogovskiiCutoff) {R : ℝ} (hR : 0 < R)
    {f : R3 → ℝ} (hf : ContDiff ℝ ⊤ f) (hfsupp : Function.support f ⊆ ballR R) (x : R3) :
    Tendsto (fun n : ℕ => ∫ t in (0 : ℝ)..(1 / ((n : ℝ) + 1)),
      ∫ z, bogovskiiDensity omega R t f x z • z ∂(volume : Measure R3))
      atTop (𝓝 0) := by
  let H : ℝ → R3 := fun t =>
    ∫ z, bogovskiiDensity omega R t f x z • z ∂(volume : Measure R3)
  have hH : Continuous H := continuous_bogovskiiSlice omega hR hf hfsupp x
  have hcont : ContinuousOn (fun t => ‖H t‖) (Set.Icc (0 : ℝ) 1) :=
    (continuous_norm.comp hH).continuousOn
  obtain ⟨t0, -, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr (zero_le_one : (0 : ℝ) ≤ 1)) hcont
  let C : ℝ := ‖H t0‖
  have hC : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖H t‖ ≤ C := fun _ ht => hmax ht
  have hε : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    simpa [one_div] using hnat.inv_tendsto_atTop
  have hscale : Tendsto (fun n : ℕ => C * ((1 : ℝ) / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hε)
  refine (tendsto_zero_iff_norm_tendsto_zero).2 ?_
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hscale
    (fun n => norm_nonneg _) ?_
  intro n
  have hε1 : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact (le_add_of_nonneg_left (Nat.cast_nonneg n))
  have hmem : ∀ t ∈ Ι (0 : ℝ) (1 / ((n : ℝ) + 1)), ‖H t‖ ≤ C := by
    intro t ht
    rw [Set.uIoc_of_le (by positivity : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1))] at ht
    exact hC t ⟨ht.1.le, ht.2.trans hε1⟩
  have hineq := _root_.intervalIntegral.norm_integral_le_of_norm_le_const (f := H) hmem
  dsimp [H] at hineq
  rw [sub_zero, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1))] at hineq
  exact hineq

/-- The cutoff along the ray from `y` through `x` vanishes once `r` is large. -/
private lemma cutoff_ray_vanishes (omega : BogovskiiCutoff) {R : ℝ} (hR : 0 < R)
    {x y : R3} (hxy : x ≠ y) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ r, M ≤ r →
      bogovskii_cutoff omega R (y + r • (x - y)) = 0 := by
  let δ : ℝ := ‖x - y‖
  have hδ : 0 < δ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  refine ⟨max 1 ((R + ‖y‖) / δ), le_max_left _ _, ?_⟩
  intro r hr
  have hr' : (R + ‖y‖) / δ ≤ r := (le_max_right _ _).trans hr
  have hr0 : 0 ≤ r := le_trans (zero_le_one : (0 : ℝ) ≤ 1) ((le_max_left _ _).trans hr)
  have hbig : R ≤ ‖y + r • (x - y)‖ := by
    have hmul : R + ‖y‖ ≤ r * δ := by
      rwa [div_le_iff₀ hδ] at hr'
    have hsub : r * δ - ‖y‖ ≤ ‖r • (x - y)‖ - ‖y‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr0]
    have htri : ‖r • (x - y)‖ ≤ ‖y + r • (x - y)‖ + ‖y‖ := by
      have hEq : r • (x - y) = (y + r • (x - y)) - y := by
        rw [smul_sub, add_sub_cancel_left]
      have hnorm : ‖r • (x - y)‖ = ‖(y + r • (x - y)) - y‖ := congrArg norm hEq
      rw [hnorm]
      exact norm_sub_le (y + r • (x - y)) y
    linarith
  have hnot : y + r • (x - y) ∉ ballR R := by
    intro hmem
    have hlt : ‖y + r • (x - y)‖ < R := by
      simpa [ballR, Metric.mem_ball, dist_eq_norm, sub_zero] using hmem
    exact (not_lt.mpr hbig) hlt
  exact Function.nmem_support.mp
    (fun hs => hnot (bogovskii_cutoff_support_subset omega hR hs))

private lemma rayIntegral_eq_Ioi_of_tail {g : ℝ → ℝ} (_hg : Continuous g) {M : ℝ}
    (hM : 1 ≤ M) (htail : ∀ r, M ≤ r → g r = 0) :
    (∫ r in Set.Ioi (1 : ℝ), g r ∂(volume : Measure ℝ)) = ∫ r in (1 : ℝ)..M, g r := by
  have htail' : ∀ r ∈ Set.Ioi (1 : ℝ) \ Set.Ioc (1 : ℝ) M, g r = 0 := by
    intro r hr
    have hr1 : 1 < r := hr.1
    have hrM : M < r := by
      have hnot : ¬(1 < r ∧ r ≤ M) := by
        intro h
        exact hr.2 ⟨h.1, h.2⟩
      exact lt_of_not_ge fun hle => hnot ⟨hr1, hle⟩
    exact htail r hrM.le
  have heq : (∫ r in Set.Ioi (1 : ℝ), g r) = ∫ r in Set.Ioc (1 : ℝ) M, g r :=
    setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi
      Set.Ioc_subset_Ioi_self htail'
  rw [heq, ← _root_.intervalIntegral.integral_of_le hM]

private lemma rayIntegral_stable {g : ℝ → ℝ} (hg : Continuous g) {M N : ℝ}
    (hN : M ≤ N) (htail : ∀ r, M ≤ r → g r = 0) :
    ∫ r in (1 : ℝ)..N, g r = ∫ r in (1 : ℝ)..M, g r := by
  have hadd := _root_.intervalIntegral.integral_add_adjacent_intervals
    (hg.intervalIntegrable (μ := (volume : Measure ℝ)) (1 : ℝ) M)
    (hg.intervalIntegrable (μ := (volume : Measure ℝ)) M N)
  have hzero : ∫ r in M..N, g r = 0 := by
    rw [← _root_.intervalIntegral.integral_zero]
    refine _root_.intervalIntegral.integral_congr fun r hr => ?_
    rw [Set.uIcc_of_le hN] at hr
    exact htail r hr.1
  rw [hzero, add_zero] at hadd
  exact hadd.symm

private lemma exists_abs_bound_of_ball {g : R3 → ℝ} (hg : Continuous g)
    (hsupp : Function.support g ⊆ ballR R) (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z, |g z| ≤ C := by
  have hcont : ContinuousOn (fun z => |g z|) (Metric.closedBall (0 : R3) R) :=
    (continuous_abs.comp hg).continuousOn
  obtain ⟨z0, -, hmax⟩ := (isCompact_closedBall (0 : R3) R).exists_isMaxOn
    (Metric.nonempty_closedBall.mpr hR.le) hcont
  refine ⟨|g z0|, abs_nonneg _, fun z => ?_⟩
  by_cases hz : z ∈ Metric.closedBall (0 : R3) R
  · exact hmax hz
  · have hg0 : g z = 0 := by
      rw [← Function.nmem_support]
      intro hs
      exact hz (Metric.ball_subset_closedBall (hsupp hs))
    simp [hg0]

/-- The change of variables `z = t⁻¹(x - y)` on the norm of one nonsingular slice. -/
private lemma bogovskiiSlice_norm_reparam (omega : BogovskiiCutoff) (R : ℝ) (f : R3 → ℝ)
    (x : R3) {t : ℝ} (ht : 0 < t) :
    (∫ z, ‖bogovskiiDensity omega R t f x z • z‖ ∂(volume : Measure R3)) =
      ∫ y, ‖(f y * bogovskii_cutoff omega R (y + t⁻¹ • (x - y)) * (t ^ 4)⁻¹) • (x - y)‖
        ∂(volume : Measure R3) := by
  let F : R3 → ℝ := fun z => ‖bogovskiiDensity omega R t f x z • z‖
  have hscale := (volume : Measure R3).integral_comp_smul F t⁻¹
  have hfin : |(t⁻¹ ^ finrank ℝ R3)⁻¹| = t ^ 3 := by
    rw [finrank_R3, inv_pow, inv_inv, abs_of_nonneg (pow_nonneg ht.le _)]
  have hscale' : ∫ v, F (t⁻¹ • v) = (t ^ 3) • ∫ z, F z := by
    rw [hfin] at hscale
    exact hscale
  have hF : ∫ z, F z = (t ^ 3)⁻¹ • ∫ v, F (t⁻¹ • v) := by
    rw [hscale', smul_smul, inv_mul_cancel₀ (pow_ne_zero 3 ht.ne'), one_smul]
  let ψ : R3 → ℝ := fun y =>
    |f y * bogovskii_cutoff omega R (y + t⁻¹ • (x - y))| * t⁻¹ * ‖x - y‖
  have hpoint : ∀ v, F (t⁻¹ • v) = ψ (x - v) := by
    intro v
    simp only [F, ψ, bogovskiiDensity]
    have hy : x - t • (t⁻¹ • v) = x - v := by
      rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
    have hv : x - (x - v) = v := by
      rw [sub_sub_cancel]
    have hω : x + (1 - t) • (t⁻¹ • v) = (x - v) + t⁻¹ • v := by
      rw [smul_smul]
      have hcoeff : (1 - t) * t⁻¹ = t⁻¹ - 1 := by
        rw [sub_mul, one_mul, mul_inv_cancel₀ ht.ne']
      rw [hcoeff, sub_smul, one_smul]
      module
    rw [hy, hω, hv, mul_comm (bogovskii_cutoff omega R (x - v + t⁻¹ • v))]
    rw [norm_smul, Real.norm_eq_abs, abs_mul]
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr ht.le)]
    ring
  have hpsi : ∫ v, F (t⁻¹ • v) = ∫ y, ψ y := by
    simpa [hpoint] using integral_comp_sub ψ x
  rw [hF, hpsi, ← integral_smul]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only [ψ, smul_eq_mul]
  have hpow : (t ^ 3)⁻¹ * t⁻¹ = (t ^ 4)⁻¹ := by
    rw [← mul_inv, ← pow_succ]
  have habs : |(t ^ 4)⁻¹| = (t ^ 4)⁻¹ :=
    abs_of_nonneg (inv_nonneg.mpr (pow_nonneg ht.le 4))
  have hsplit : |f y * bogovskii_cutoff omega R (y + t⁻¹ • (x - y)) * (t ^ 4)⁻¹| =
      |f y * bogovskii_cutoff omega R (y + t⁻¹ • (x - y))| * (t ^ 4)⁻¹ := by
    rw [abs_mul, habs]
  have hmul : (t ^ 3)⁻¹ * (|f y * bogovskii_cutoff omega R (y + t⁻¹ • (x - y))| * t⁻¹ * ‖x - y‖) =
      |f y * bogovskii_cutoff omega R (y + t⁻¹ • (x - y)) * (t ^ 4)⁻¹| * ‖x - y‖ := by
    calc
      (t ^ 3)⁻¹ * (|f y * bogovskii_cutoff omega R (y + t⁻¹ • (x - y))| * t⁻¹ * ‖x - y‖) =
          |f y * bogovskii_cutoff omega R (y + t⁻¹ • (x - y))| * ((t ^ 3)⁻¹ * t⁻¹) * ‖x - y‖ := by
            ring
      _ = |f y * bogovskii_cutoff omega R (y + t⁻¹ • (x - y))| * (t ^ 4)⁻¹ * ‖x - y‖ := by
            rw [hpow]
      _ = |f y * bogovskii_cutoff omega R (y + t⁻¹ • (x - y)) * (t ^ 4)⁻¹| * ‖x - y‖ := by
            rw [← hsplit]
  rw [hmul, norm_smul, Real.norm_eq_abs]

private lemma norm_density_bound (omega : BogovskiiCutoff) {R : ℝ} (hR : 0 < R)
    {f : R3 → ℝ} (hf : ContDiff ℝ ⊤ f) (hfsupp : Function.support f ⊆ ballR R) (x : R3) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ,
      (∫ z, ‖bogovskiiDensity omega R t f x z • z‖ ∂(volume : Measure R3)) ≤ B := by
  obtain ⟨Cω, hCω0, hCω⟩ := exists_abs_bound_of_ball
    (bogovskii_cutoff_smooth omega R).continuous (bogovskii_cutoff_support_subset omega hR) hR
  obtain ⟨Cf, hCf0, hCf⟩ := exists_abs_bound_of_ball hf.continuous hfsupp hR
  let C : ℝ := Cω * Cf * (2 * R)
  have hC : 0 ≤ C :=
    mul_nonneg (mul_nonneg hCω0 hCf0) (mul_nonneg zero_le_two hR.le)
  let G : R3 → ℝ := (Metric.closedBall (0 : R3) (2 * R)).indicator fun _ => C
  have hG : Integrable G (volume : Measure R3) := by
    rw [integrable_indicator_iff measurableSet_closedBall]
    exact integrableOn_const.2 (Or.inr ((isCompact_closedBall (0 : R3) (2 * R)).measure_lt_top))
  have hB : 0 ≤ ∫ z, G z ∂(volume : Measure R3) := integral_nonneg fun z => by
    by_cases hz : z ∈ Metric.closedBall (0 : R3) (2 * R)
    · simp [G, hz, hC]
    · simp [G, hz]
  refine ⟨∫ z, G z, hB, fun t => ?_⟩
  have hle : ∀ z, ‖bogovskiiDensity omega R t f x z • z‖ ≤ G z := by
    intro z
    by_cases hz : z ∈ Metric.closedBall (0 : R3) (2 * R)
    · have hGval : G z = C := by simp [G, hz]
      rw [hGval, norm_smul, Real.norm_eq_abs, bogovskiiDensity, abs_mul]
      have hzn : ‖z‖ ≤ 2 * R := mem_closedBall_norm_zero.mp hz
      have hprod : |bogovskii_cutoff omega R (x + (1 - t) • z)| * |f (x - t • z)| ≤ Cω * Cf :=
        mul_le_mul (hCω _) (hCf _) (abs_nonneg _) hCω0
      calc
        |bogovskii_cutoff omega R (x + (1 - t) • z)| * |f (x - t • z)| * ‖z‖ ≤
            (Cω * Cf) * ‖z‖ := mul_le_mul_of_nonneg_right hprod (norm_nonneg _)
        _ ≤ (Cω * Cf) * (2 * R) :=
            mul_le_mul_of_nonneg_left hzn (mul_nonneg hCω0 hCf0)
        _ = C := by ring
    · have hGval : G z = 0 := by simp [G, hz]
      rw [hGval]
      have hlt : 2 * R < ‖z‖ := by
        rw [mem_closedBall_norm_zero] at hz
        exact lt_of_not_ge hz
      rw [bogovskiiDensity_eq_zero_of_large_z omega hR hfsupp t x z hlt.le, zero_smul, norm_zero]
  have hint : Integrable (fun z => ‖bogovskiiDensity omega R t f x z • z‖) (volume : Measure R3) := by
    have hcont : Continuous (fun z => bogovskiiDensity omega R t f x z • z) := by
      have hden : Continuous (fun z => bogovskiiDensity omega R t f x z) :=
        ((bogovskii_cutoff_smooth omega R).continuous.comp
          (continuous_const.add ((continuous_const.sub continuous_const).smul continuous_id))).mul
          (hf.continuous.comp (continuous_const.sub (continuous_const.smul continuous_id)))
      exact hden.smul continuous_id
    have hnorm_supp : Function.support (fun z => ‖bogovskiiDensity omega R t f x z • z‖) ⊆
        Metric.closedBall (0 : R3) (2 * R) := by
      intro z hz
      by_contra hnot
      have hlt : 2 * R < ‖z‖ := by
        rw [mem_closedBall_norm_zero] at hnot
        exact lt_of_not_ge hnot
      apply hz
      change ‖bogovskiiDensity omega R t f x z • z‖ = 0
      rw [bogovskiiDensity_eq_zero_of_large_z omega hR hfsupp t x z hlt.le, zero_smul, norm_zero]
    exact (continuous_norm.comp hcont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall _ _) hnorm_supp)
  exact integral_mono hint hG hle

private lemma norm_slice_integral (omega : BogovskiiCutoff) {R : ℝ} (_hR : 0 < R)
    {f : R3 → ℝ} (hf : ContDiff ℝ ⊤ f) (hfsupp : Function.support f ⊆ ballR R) (x : R3)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (∫ y, ∫ t in ε..1,
        ‖(f y * bogovskii_cutoff omega R (y + t⁻¹ • (x - y)) * (t ^ 4)⁻¹) • (x - y)‖
          ∂(volume : Measure ℝ) ∂(volume : Measure R3)) =
      ∫ t in ε..1,
        ∫ z, ‖bogovskiiDensity omega R t f x z • z‖ ∂(volume : Measure R3) := by
  let N : ℝ → R3 → ℝ := fun t y =>
    ‖(f y * bogovskii_cutoff omega R (y + t⁻¹ • (x - y)) * (t ^ 4)⁻¹) • (x - y)‖
  let S : Set R3 := Metric.closedBall (0 : R3) R
  have hzero : ∀ t y, y ∉ S → N t y = 0 := by
    intro t y hy
    have hy' : y ∉ ballR R := fun h => hy (Metric.ball_subset_closedBall h)
    have hf0 : f y = 0 := by
      rw [← Function.nmem_support]
      exact fun hs => hy' (hfsupp hs)
    simp [N, hf0]
  have hslice : ∀ t, ∫ y in S, N t y ∂(volume : Measure R3) = ∫ y, N t y := fun t =>
    setIntegral_eq_integral_of_forall_compl_eq_zero (μ := (volume : Measure R3)) (hzero t)
  have hcont : ContinuousOn (Function.uncurry N) (Set.Icc ε 1 ×ˢ S) :=
    (continuous_norm.comp_continuousOn
      (continuousOn_reparamSlice omega R hf.continuous x hε0)).mono
      (fun (p : ℝ × R3) hp => ⟨hp.1, Set.mem_univ p.2⟩)
  have hint : IntegrableOn (Function.uncurry N) (Set.Icc ε 1 ×ˢ S) (volume : Measure (ℝ × R3)) :=
    hcont.integrableOn_compact (isCompact_Icc.prod (isCompact_closedBall _ _))
  have hswap := setIntegral_prod (μ := (volume : Measure ℝ)) (ν := (volume : Measure R3))
    (Function.uncurry N) (by simpa [Measure.volume_eq_prod] using hint)
  simp only [Function.uncurry_apply_pair] at hswap
  have hleft :
      (∫ t in ε..1, ∫ y, N t y ∂(volume : Measure R3)) =
        ∫ p in Set.Icc ε 1 ×ˢ S, Function.uncurry N p ∂(volume : Measure (ℝ × R3)) := by
    rw [_root_.intervalIntegral.integral_of_le hε1, ← integral_Icc_eq_integral_Ioc]
    have hcong :
        (∫ t in Set.Icc ε 1, ∫ y, N t y ∂(volume : Measure R3)) =
          ∫ t in Set.Icc ε 1, ∫ y in S, N t y ∂(volume : Measure R3) :=
      setIntegral_congr measurableSet_Icc fun t _ => (hslice t).symm
    rw [hcong, Measure.volume_eq_prod, ← hswap]
  have hint' : Integrable (Function.uncurry N)
      (((volume : Measure ℝ).restrict (Set.Icc ε 1)).prod
        ((volume : Measure R3).restrict S)) := by
    simpa [Measure.prod_restrict, IntegrableOn, Measure.volume_eq_prod] using hint
  have hord := integral_integral_swap (f := N) hint'
  have hyzero : ∀ y, y ∉ S → (∫ t in Set.Icc ε 1, N t y ∂(volume : Measure ℝ)) = 0 := by
    intro y hy
    have hfun : (fun t => N t y) = fun _ => (0 : ℝ) := funext fun t => hzero t y hy
    rw [hfun]
    simp
  have hyint :
      (∫ y in S, ∫ t in Set.Icc ε 1, N t y ∂(volume : Measure ℝ) ∂(volume : Measure R3)) =
        ∫ y, ∫ t in Set.Icc ε 1, N t y ∂(volume : Measure ℝ) ∂(volume : Measure R3) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (μ := (volume : Measure R3)) hyzero
  have hright :
      (∫ y, ∫ t in Set.Icc ε 1, N t y ∂(volume : Measure ℝ) ∂(volume : Measure R3)) =
        ∫ p in Set.Icc ε 1 ×ˢ S, Function.uncurry N p ∂(volume : Measure (ℝ × R3)) := by
    rw [← hyint, ← hord, Measure.volume_eq_prod, hswap]
  have hIcc : (∫ y, ∫ t in ε..1, N t y ∂(volume : Measure ℝ) ∂(volume : Measure R3)) =
      ∫ y, ∫ t in Set.Icc ε 1, N t y ∂(volume : Measure ℝ) ∂(volume : Measure R3) := by
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    beta_reduce
    rw [_root_.intervalIntegral.integral_of_le hε1, ← integral_Icc_eq_integral_Ioc]
  rw [hIcc, hright, ← hleft]
  refine _root_.intervalIntegral.integral_congr fun t ht => ?_
  have ht0 : 0 < t := lt_of_lt_of_le hε0 (by
    rw [Set.uIcc_of_le hε1] at ht
    exact ht.1)
  simpa [N] using (bogovskiiSlice_norm_reparam omega R f x ht0).symm

/-- One truncated kernel value is the interval integral of the reparametrized slice. -/
private lemma intervalKernel_eq_ray (omega : BogovskiiCutoff) (R : ℝ) (f : R3 → ℝ)
    (x y : R3) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (∫ r in (1 : ℝ)..ε⁻¹,
        bogovskii_cutoff omega R (y + r • (x - y)) * r ^ 2) • (f y • (x - y)) =
      ∫ t in ε..1,
        (f y * bogovskii_cutoff omega R (y + t⁻¹ • (x - y)) * (t ^ 4)⁻¹) • (x - y) := by
  by_cases hεeq : ε = 1
  · subst hεeq
    simp only [inv_one]
    rw [_root_.intervalIntegral.integral_same, zero_smul, _root_.intervalIntegral.integral_same]
  have hεlt : ε < 1 := lt_of_le_of_ne hε1 hεeq
  let K : ℝ → R3 := fun t =>
    (f y * bogovskii_cutoff omega R (y + t⁻¹ • (x - y)) * (t ^ 4)⁻¹) • (x - y)
  have hI : (∫ t in ε..1, K t) = ∫ t in Set.Icc ε 1, K t ∂(volume : Measure ℝ) := by
    rw [_root_.intervalIntegral.integral_of_le hε1, ← integral_Icc_eq_integral_Ioc]
  have hfac :
      (∫ t in Set.Icc ε 1, K t ∂(volume : Measure ℝ)) =
        (∫ t in Set.Icc ε 1,
            bogovskii_cutoff omega R (y + t⁻¹ • (x - y)) * (t ^ 4)⁻¹ ∂(volume : Measure ℝ)) •
          (f y • (x - y)) := by
    have hrewrite : ∀ t, K t =
        (f y * (bogovskii_cutoff omega R (y + t⁻¹ • (x - y)) * (t ^ 4)⁻¹)) • (x - y) := by
      intro t
      simp only [K, mul_assoc]
    simp_rw [hrewrite, integral_smul_const, integral_mul_left, smul_smul]
    rw [mul_comm (f y)]
  have hIcc :
      (∫ t in Set.Icc ε 1,
          bogovskii_cutoff omega R (y + t⁻¹ • (x - y)) * (t ^ 4)⁻¹ ∂(volume : Measure ℝ)) =
        ∫ t in ε..1, bogovskii_cutoff omega R (y + t⁻¹ • (x - y)) * (t ^ 4)⁻¹ := by
    rw [integral_Icc_eq_integral_Ioc, ← _root_.intervalIntegral.integral_of_le hε1]
  have hM : 1 < ε⁻¹ := one_lt_inv hε0 hεlt
  have hray := rayIntegral_reparam omega R x y hM
  have hdiv : 1 / ε⁻¹ = ε := by rw [one_div, inv_inv]
  rw [hdiv] at hray
  have hray' :
      (∫ r in (1 : ℝ)..ε⁻¹, bogovskii_cutoff omega R (y + r • (x - y)) * r ^ 2) •
          (f y • (x - y)) =
        (∫ t in ε..1, bogovskii_cutoff omega R (y + t⁻¹ • (x - y)) * (t ^ 4)⁻¹) •
          (f y • (x - y)) :=
    congrArg (fun s : ℝ => s • (f y • (x - y))) hray
  rw [hray', ← hIcc, ← hfac, ← hI]

/-- On `ε ≤ t ≤ 1` the reparametrized slice is bounded, uniformly in `y`. -/
private lemma reparamSlice_norm_bound (omega : BogovskiiCutoff) {R : ℝ} (hR : 0 < R)
    {f : R3 → ℝ} (hf : Continuous f) (hfsupp : Function.support f ⊆ ballR R)
    (x : R3) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t y, t ∈ Set.Icc ε 1 →
      ‖(f y * bogovskii_cutoff omega R (y + t⁻¹ • (x - y)) * (t ^ 4)⁻¹) • (x - y)‖ ≤ C := by
  obtain ⟨Cω, hCω0, hCω⟩ := exists_abs_bound_of_ball
    (bogovskii_cutoff_smooth omega R).continuous (bogovskii_cutoff_support_subset omega hR) hR
  obtain ⟨Cf, hCf0, hCf⟩ := exists_abs_bound_of_ball hf hfsupp hR
  let C : ℝ := Cf * Cω * (ε ^ 4)⁻¹ * (‖x‖ + R)
  have hC : 0 ≤ C :=
    mul_nonneg (mul_nonneg (mul_nonneg hCf0 hCω0)
      (inv_nonneg.mpr (pow_nonneg hε.le 4))) (add_nonneg (norm_nonneg _) hR.le)
  refine ⟨C, hC, fun t y ht => ?_⟩
  by_cases hy : y ∈ Metric.closedBall (0 : R3) R
  · have ht0 : 0 < t := lt_of_lt_of_le hε ht.1
    have hinv : (t ^ 4)⁻¹ ≤ (ε ^ 4)⁻¹ :=
      (inv_le_inv (pow_pos ht0 4) (pow_pos hε 4)).mpr (pow_le_pow_left hε.le ht.1 4)
    have habs : |(t ^ 4)⁻¹| = (t ^ 4)⁻¹ :=
      abs_of_nonneg (inv_nonneg.mpr (pow_nonneg ht0.le 4))
    have hxy : ‖x - y‖ ≤ ‖x‖ + R := by
      calc
        ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le _ _
        _ ≤ ‖x‖ + R := add_le_add_left (mem_closedBall_norm_zero.mp hy) _
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_mul, habs]
    calc
      |f y| * |bogovskii_cutoff omega R (y + t⁻¹ • (x - y))| * (t ^ 4)⁻¹ * ‖x - y‖ ≤
          Cf * |bogovskii_cutoff omega R (y + t⁻¹ • (x - y))| * (t ^ 4)⁻¹ * ‖x - y‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (hCf y) (abs_nonneg _)) (inv_nonneg.mpr (pow_nonneg ht0.le _))) (norm_nonneg _)
      _ ≤ Cf * Cω * (t ^ 4)⁻¹ * ‖x - y‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hCω _) hCf0) (inv_nonneg.mpr (pow_nonneg ht0.le _)))
          (norm_nonneg _)
      _ ≤ Cf * Cω * (ε ^ 4)⁻¹ * ‖x - y‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hinv
          (mul_nonneg hCf0 hCω0)) (norm_nonneg _)
      _ ≤ Cf * Cω * (ε ^ 4)⁻¹ * (‖x‖ + R) :=
        mul_le_mul_of_nonneg_left hxy
          (mul_nonneg (mul_nonneg hCf0 hCω0) (inv_nonneg.mpr (pow_nonneg hε.le 4)))
      _ = C := rfl
  · have hf0 : f y = 0 := by
      rw [← Function.nmem_support]
      intro hs
      exact hy (Metric.ball_subset_closedBall (hfsupp hs))
    simp [hf0, zero_mul, zero_smul, norm_zero, hC]

private lemma reparamKernel_continuousOn (omega : BogovskiiCutoff) (R : ℝ)
    {f : R3 → ℝ} (hf : Continuous f) (x y : R3) {a : ℝ} (ha : 0 < a) :
    ContinuousOn (fun t : ℝ =>
      (f y * bogovskii_cutoff omega R (y + t⁻¹ • (x - y)) * (t ^ 4)⁻¹) • (x - y))
      (Set.Icc a 1) :=
  (continuousOn_reparamSlice omega R hf x ha).comp
    (continuous_id.prod_mk continuous_const).continuousOn
    (fun _ ht => ⟨ht, Set.mem_univ y⟩)

private lemma reparamKernel_norm_continuousOn (omega : BogovskiiCutoff) (R : ℝ)
    {f : R3 → ℝ} (hf : Continuous f) (x y : R3) {a : ℝ} (ha : 0 < a) :
    ContinuousOn (fun t : ℝ =>
      ‖(f y * bogovskii_cutoff omega R (y + t⁻¹ • (x - y)) * (t ^ 4)⁻¹) • (x - y)‖)
      (Set.Icc a 1) :=
  continuous_norm.comp_continuousOn (reparamKernel_continuousOn omega R hf x y ha)

private lemma truncatedKernel_tendsto (omega : BogovskiiCutoff) {R : ℝ} (hR : 0 < R)
    (f : R3 → ℝ) (x y : R3) :
    Tendsto (fun n : ℕ =>
      (∫ r in (1 : ℝ)..((n : ℝ) + 1),
          bogovskii_cutoff omega R (y + r • (x - y)) * r ^ 2) • (f y • (x - y)))
      atTop (𝓝 (
        (∫ r in Set.Ioi (1 : ℝ),
            bogovskii_cutoff omega R (y + r • (x - y)) * r ^ 2) • (f y • (x - y)))) := by
  by_cases hxy : x = y
  · subst hxy
    simp_rw [sub_self, smul_zero]
    exact tendsto_const_nhds
  · obtain ⟨M, hM, hvan⟩ := cutoff_ray_vanishes omega hR hxy
    let g : ℝ → ℝ := fun r =>
      bogovskii_cutoff omega R (y + r • (x - y)) * r ^ 2
    have hg : Continuous g := by
      have hc : Continuous (bogovskii_cutoff omega R) :=
        (bogovskii_cutoff_smooth omega R).continuous
      exact (hc.comp <| continuous_const.add <| continuous_id.smul continuous_const).mul
        (continuous_id.pow 2)
    have htail : ∀ r, M ≤ r → g r = 0 := fun r hr => by
      simp [g, hvan r hr, zero_mul]
    have hlimN : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    have hev : ∀ᶠ n : ℕ in atTop, M ≤ (n : ℝ) + 1 :=
      tendsto_atTop.mp hlimN M
    let target : R3 :=
      (∫ r in Set.Ioi (1 : ℝ), g r ∂(volume : Measure ℝ)) • (f y • (x - y))
    have heq : (fun _ : ℕ => target) =ᶠ[atTop]
        fun n => (∫ r in (1 : ℝ)..((n : ℝ) + 1), g r ∂(volume : Measure ℝ)) •
          (f y • (x - y)) := by
      filter_upwards [hev] with n hn
      have hstable := rayIntegral_stable hg hn htail
      have hIoi := (rayIntegral_eq_Ioi_of_tail hg hM htail).symm
      have hsc : (∫ r in (1 : ℝ)..((n : ℝ) + 1), g r ∂(volume : Measure ℝ)) =
          ∫ r in Set.Ioi (1 : ℝ), g r ∂(volume : Measure ℝ) := by
        rw [hstable, hIoi]
      exact (congrArg (fun s : ℝ => s • (f y • (x - y))) hsc).symm
    simpa [g, target] using tendsto_const_nhds.congr' heq

private lemma continuous_truncatedKernel (omega : BogovskiiCutoff) {R : ℝ} (hR : 0 < R)
    {f : R3 → ℝ} (hf : ContDiff ℝ ⊤ f) (hfsupp : Function.support f ⊆ ballR R)
    (x : R3) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    Continuous (fun y : R3 => ∫ t in ε..1,
      (f y * bogovskii_cutoff omega R (y + t⁻¹ • (x - y)) * (t ^ 4)⁻¹) • (x - y)
        ∂(volume : Measure ℝ)) := by
  obtain ⟨C, _, hC⟩ := reparamSlice_norm_bound omega hR hf.continuous hfsupp x hε0
  refine _root_.intervalIntegral.continuous_of_dominated_interval
    (μ := (volume : Measure ℝ)) (bound := fun _ => C) ?_ ?_ ?_ ?_
  · intro y
    rw [Set.uIoc_of_le hε1]
    exact ((reparamKernel_continuousOn omega R hf.continuous x y hε0).mono
      Set.Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  · intro y
    refine ae_of_all _ fun t ht => ?_
    rw [Set.uIoc_of_le hε1] at ht
    exact hC t y ⟨ht.1.le, ht.2⟩
  · exact (continuous_const : Continuous fun _ : ℝ => C).intervalIntegrable ε 1
  · refine ae_of_all _ fun t ht => ?_
    rw [Set.uIoc_of_le hε1] at ht
    exact (continuousOn_reparamSlice omega R hf.continuous x hε0).comp_continuous
      (continuous_const.prod_mk continuous_id) fun y => ⟨⟨ht.1.le, ht.2⟩, Set.mem_univ y⟩

private lemma continuous_sliceNorm (omega : BogovskiiCutoff) {R : ℝ} (hR : 0 < R)
    {f : R3 → ℝ} (hf : ContDiff ℝ ⊤ f) (hfsupp : Function.support f ⊆ ballR R)
    (x : R3) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    Continuous (fun y : R3 => ∫ t in ε..1,
      ‖(f y * bogovskii_cutoff omega R (y + t⁻¹ • (x - y)) * (t ^ 4)⁻¹) • (x - y)‖
        ∂(volume : Measure ℝ)) := by
  obtain ⟨C, _, hC⟩ := reparamSlice_norm_bound omega hR hf.continuous hfsupp x hε0
  refine _root_.intervalIntegral.continuous_of_dominated_interval
    (μ := (volume : Measure ℝ)) (bound := fun _ => C) ?_ ?_ ?_ ?_
  · intro y
    rw [Set.uIoc_of_le hε1]
    exact ((reparamKernel_norm_continuousOn omega R hf.continuous x y hε0).mono
      Set.Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  · intro y
    refine ae_of_all _ fun t ht => ?_
    rw [Set.uIoc_of_le hε1] at ht
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact hC t y ⟨ht.1.le, ht.2⟩
  · exact (continuous_const : Continuous fun _ : ℝ => C).intervalIntegrable ε 1
  · refine ae_of_all _ fun t ht => ?_
    rw [Set.uIoc_of_le hε1] at ht
    exact continuous_norm.comp <|
      (continuousOn_reparamSlice omega R hf.continuous x hε0).comp_continuous
        (continuous_const.prod_mk continuous_id) fun y => ⟨⟨ht.1.le, ht.2⟩, Set.mem_univ y⟩

private lemma sliceNorm_integral_le (omega : BogovskiiCutoff) {R : ℝ} (hR : 0 < R)
    {f : R3 → ℝ} (hf : ContDiff ℝ ⊤ f) (hfsupp : Function.support f ⊆ ballR R)
    (x : R3) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ t : ℝ, (∫ z, ‖bogovskiiDensity omega R t f x z • z‖ ∂(volume : Measure R3)) ≤ B)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (∫ y, ∫ t in ε..1,
        ‖(f y * bogovskii_cutoff omega R (y + t⁻¹ • (x - y)) * (t ^ 4)⁻¹) • (x - y)‖
          ∂(volume : Measure ℝ) ∂(volume : Measure R3)) ≤ B := by
  rw [norm_slice_integral omega hR hf hfsupp x hε0 hε1]
  let ψ : ℝ → ℝ := fun t =>
    ∫ z, ‖bogovskiiDensity omega R t f x z • z‖ ∂(volume : Measure R3)
  have hψ0 : ∀ t, 0 ≤ ψ t := fun t => integral_nonneg fun _ => norm_nonneg _
  have hnorm := _root_.intervalIntegral.norm_integral_le_of_norm_le_const
    (f := ψ) (a := ε) (b := 1) (C := B) (fun t _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hψ0 t)]
      exact hB t)
  have hpos : 0 ≤ ∫ t in ε..1, ψ t :=
    _root_.intervalIntegral.integral_nonneg hε1 fun t _ => hψ0 t
  have hint : ∫ t in ε..1, ψ t ≤ B * |1 - ε| := by
    have hnorm' : ‖∫ t in ε..1, ψ t‖ ≤ B * |1 - ε| := hnorm
    rw [Real.norm_eq_abs, abs_of_nonneg hpos] at hnorm'
    exact hnorm'
  have hspan : B * |1 - ε| ≤ B := by
    rw [abs_of_nonneg (sub_nonneg.mpr hε1)]
    exact mul_le_of_le_one_right hB0 (by linarith)
  change (∫ t in ε..1, ψ t) ≤ B
  exact hint.trans hspan

set_option maxHeartbeats 4000000 in
lemma bogovskiiNonsingular_eq_Bogovskii (omega : BogovskiiCutoff) {R : ℝ} (hR : 0 < R)
    {f : R3 → ℝ} (hf : ContDiff ℝ ⊤ f) (hfsupp : Function.support f ⊆ ballR R) :
    bogovskiiNonsingular omega R f = Bogovskii omega R f := by
  funext x
  obtain ⟨B, hB0, hBt⟩ := norm_density_bound omega hR hf hfsupp x
  let εn : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε0 : ∀ n, 0 < εn n := fun _ => by positivity
  have hε1 : ∀ n, εn n ≤ 1 := fun n => by
    rw [div_le_one (by positivity)]
    exact le_add_of_nonneg_left (Nat.cast_nonneg n)
  have hεsucc : ∀ n, εn (n + 1) ≤ εn n := by
    intro n
    have hcast : ((n + 1 : ℕ) : ℝ) + 1 = (n : ℝ) + 2 := by
      rw [Nat.cast_add, Nat.cast_one]
      ring
    simp only [εn]
    rw [hcast]
    exact div_le_div_of_nonneg_left zero_le_one (by positivity) (by linarith)
  have hinv : ∀ n, (εn n)⁻¹ = (n : ℝ) + 1 := fun _ => by rw [inv_div, div_one]
  let K : ℝ → R3 → R3 := fun t y =>
    (f y * bogovskii_cutoff omega R (y + t⁻¹ • (x - y)) * (t ^ 4)⁻¹) • (x - y)
  let φseq : ℕ → R3 → ℝ := fun n y => ∫ t in εn n..1, ‖K t y‖ ∂(volume : Measure ℝ)
  have hnn : ∀ n y, 0 ≤ φseq n y := fun n y => by
    dsimp [φseq]
    exact _root_.intervalIntegral.integral_nonneg (hε1 n) fun _ _ => norm_nonneg _
  have hmono : ∀ y, Monotone fun n => φseq n y := by
    intro y
    refine monotone_nat_of_le_succ fun n => ?_
    have hρ := reparamKernel_norm_continuousOn omega R hf.continuous x y (hε0 (n + 1))
    have hleft : IntervalIntegrable (fun t => ‖K t y‖) (volume : Measure ℝ)
        (εn (n + 1)) (εn n) :=
      (hρ.mono fun t ht => ⟨ht.1, ht.2.trans (hε1 n)⟩).intervalIntegrable_of_Icc (hεsucc n)
    have hright : IntervalIntegrable (fun t => ‖K t y‖) (volume : Measure ℝ) (εn n) 1 :=
      (hρ.mono fun t ht => ⟨(hεsucc n).trans ht.1, ht.2⟩).intervalIntegrable_of_Icc (hε1 n)
    have hadd := _root_.intervalIntegral.integral_add_adjacent_intervals hleft hright
    have hpiece : 0 ≤ ∫ t in εn (n + 1)..εn n, ‖K t y‖ ∂(volume : Measure ℝ) :=
      _root_.intervalIntegral.integral_nonneg (hεsucc n) fun _ _ => norm_nonneg _
    dsimp [φseq]
    rw [← hadd]
    exact le_add_of_nonneg_left hpiece
  have hbdd : ∀ y, BddAbove (Set.range fun n => φseq n y) := by
    intro y
    by_cases hxy : x = y
    · refine ⟨0, ?_⟩
      rintro _ ⟨n, rfl⟩
      apply le_of_eq
      dsimp [φseq]
      rw [← _root_.intervalIntegral.integral_zero]
      refine _root_.intervalIntegral.integral_congr fun _ _ => ?_
      simp [K, hxy, sub_self, smul_zero, norm_zero]
    · obtain ⟨M, hM, hvan⟩ := cutoff_ray_vanishes omega hR hxy
      let δ : ℝ := M⁻¹
      have hδ0 : 0 < δ := inv_pos.mpr (lt_of_lt_of_le zero_lt_one hM)
      have hδ1 : δ ≤ 1 := inv_le_one hM
      have hεtend : Tendsto εn atTop (𝓝 0) := by
        have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
          tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
        simpa [εn, one_div] using hnat.inv_tendsto_atTop
      have hev : ∀ᶠ n : ℕ in atTop, εn n ≤ δ :=
        (hεtend.eventually (Iio_mem_nhds hδ0)).mono fun _ hn => hn.le
      rw [eventually_atTop] at hev
      obtain ⟨n0, hn0⟩ := hev
      let C : ℝ := ∫ t in δ..1, ‖K t y‖ ∂(volume : Measure ℝ)
      have hstab : ∀ n, n0 ≤ n → φseq n y = C := by
        intro n hn
        have hεδ : εn n ≤ δ := hn0 n hn
        have hρ := reparamKernel_norm_continuousOn omega R hf.continuous x y (hε0 n)
        have hleft : IntervalIntegrable (fun t => ‖K t y‖) (volume : Measure ℝ) (εn n) δ :=
          (hρ.mono fun t ht => ⟨ht.1, ht.2.trans hδ1⟩).intervalIntegrable_of_Icc hεδ
        have hright : IntervalIntegrable (fun t => ‖K t y‖) (volume : Measure ℝ) δ 1 :=
          (reparamKernel_norm_continuousOn omega R hf.continuous x y hδ0).intervalIntegrable_of_Icc
            hδ1
        have hadd := _root_.intervalIntegral.integral_add_adjacent_intervals hleft hright
        have hzero : ∫ t in εn n..δ, ‖K t y‖ ∂(volume : Measure ℝ) = 0 := by
          rw [← _root_.intervalIntegral.integral_zero]
          refine _root_.intervalIntegral.integral_congr fun t ht => ?_
          rw [Set.uIcc_of_le hεδ] at ht
          have ht0 : 0 < t := lt_of_lt_of_le (hε0 n) ht.1
          have hge : M ≤ t⁻¹ := by
            have hinvle : δ⁻¹ ≤ t⁻¹ := (inv_le_inv hδ0 ht0).mpr ht.2
            simpa [δ, inv_inv] using hinvle
          simp [K, hvan _ hge, mul_zero, zero_mul, zero_smul, norm_zero]
        rw [hzero, zero_add] at hadd
        simpa [φseq, C] using hadd.symm
      refine ⟨C, ?_⟩
      rintro _ ⟨n, rfl⟩
      by_cases hn : n0 ≤ n
      · exact le_of_eq (hstab n hn)
      · exact (hmono y (le_of_lt (lt_of_not_ge hn))).trans (le_of_eq (hstab n0 le_rfl))
  let φ : R3 → ℝ := fun y => ⨆ n, φseq n y
  have hφ0 : ∀ y, 0 ≤ φ y := fun y => (hnn 0 y).trans (le_ciSup (hbdd y) 0)
  have hφcont : ∀ n, Continuous (φseq n) := fun n => by
    simpa [φseq, K] using continuous_sliceNorm omega hR hf hfsupp x (hε0 n) (hε1 n)
  have hφint : ∀ n, Integrable (φseq n) (volume : Measure R3) := by
    intro n
    have hsupp : Function.support (φseq n) ⊆ Metric.closedBall (0 : R3) R := by
      intro y hy
      by_contra hnot
      have hf0 : f y = 0 := by
        rw [← Function.nmem_support]
        intro hs
        exact hnot (Metric.ball_subset_closedBall (hfsupp hs))
      apply hy
      dsimp [φseq]
      rw [← _root_.intervalIntegral.integral_zero]
      refine _root_.intervalIntegral.integral_congr fun _ _ => ?_
      simp [K, hf0, zero_mul, zero_smul, norm_zero]
    exact (hφcont n).integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall _ _) hsupp)
  have hφle : ∀ n, (∫ y, φseq n y ∂(volume : Measure R3)) ≤ B := fun n => by
    simpa [φseq, K] using sliceNorm_integral_le omega hR hf hfsupp x hB0 hBt (hε0 n) (hε1 n)
  have hmonoE : Monotone fun n : ℕ => fun y : R3 => ENNReal.ofReal (φseq n y) := by
    intro n m hnm y
    exact ENNReal.ofReal_le_ofReal (hmono y hnm)
  have hsup_eq : ∀ y, ENNReal.ofReal (φ y) = ⨆ n, ENNReal.ofReal (φseq n y) := fun y =>
    Monotone.map_ciSup_of_continuousAt (f := ENNReal.ofReal) (g := fun n => φseq n y)
      ENNReal.continuous_ofReal.continuousAt (fun a b hab => ENNReal.ofReal_le_ofReal hab) (hbdd y)
  have hlin : (∫⁻ y, ENNReal.ofReal (φ y) ∂(volume : Measure R3)) =
      ⨆ n, ENNReal.ofReal (∫ y, φseq n y ∂(volume : Measure R3)) := by
    simp_rw [hsup_eq]
    have hL := lintegral_iSup (μ := (volume : Measure R3))
      (f := fun n y => ENNReal.ofReal (φseq n y))
      (fun n => (ENNReal.continuous_ofReal.comp (hφcont n)).measurable) hmonoE
    exact hL.trans <| iSup_congr fun n =>
      (ofReal_integral_eq_lintegral_ofReal (hφint n) (Eventually.of_forall (hnn n))).symm
  have hHF : HasFiniteIntegral φ (volume : Measure R3) := by
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hφ0)]
    rw [hlin]
    exact lt_of_le_of_lt (iSup_le fun n => ENNReal.ofReal_le_ofReal (hφle n)) ENNReal.ofReal_lt_top
  have hsm : StronglyMeasurable φ :=
    stronglyMeasurable_of_tendsto atTop (fun n => (hφcont n).stronglyMeasurable) (by
      rw [tendsto_pi_nhds]
      intro y
      exact tendsto_atTop_ciSup (hmono y) (hbdd y))
  have hφInt : Integrable φ (volume : Measure R3) := ⟨hsm.aestronglyMeasurable, hHF⟩
  let g : ℕ → R3 → R3 := fun n y =>
    (∫ r in (1 : ℝ)..((n : ℝ) + 1),
        bogovskii_cutoff omega R (y + r • (x - y)) * r ^ 2) • (f y • (x - y))
  let L : R3 → R3 := fun y =>
    (∫ r in Set.Ioi (1 : ℝ),
        bogovskii_cutoff omega R (y + r • (x - y)) * r ^ 2) • (f y • (x - y))
  have hg_eq : ∀ n y, g n y = ∫ t in εn n..1, K t y ∂(volume : Measure ℝ) := by
    intro n y
    have h := intervalKernel_eq_ray omega R f x y (hε0 n) (hε1 n)
    rw [hinv n] at h
    simpa [g, K, εn] using h
  have hgcont : ∀ n, Continuous (g n) := by
    intro n
    have hcont := continuous_truncatedKernel omega hR hf hfsupp x (hε0 n) (hε1 n)
    have hfun : g n = fun y => ∫ t in εn n..1, K t y ∂(volume : Measure ℝ) :=
      funext fun y => hg_eq n y
    simpa [hfun, K, εn] using hcont
  have hgle : ∀ n y, ‖g n y‖ ≤ φ y := by
    intro n y
    have hnorm := _root_.intervalIntegral.norm_integral_le_integral_norm
      (μ := (volume : Measure ℝ)) (a := εn n) (b := 1) (hε1 n) (f := fun t => K t y)
    rw [← hg_eq n y] at hnorm
    exact (show ‖g n y‖ ≤ φseq n y by simpa [φseq] using hnorm).trans (le_ciSup (hbdd y) n)
  have hDCT := tendsto_integral_of_dominated_convergence (μ := (volume : Measure R3))
    (F := g) (f := L) φ (fun n => (hgcont n).aestronglyMeasurable) hφInt
    (fun n => ae_of_all _ fun y => hgle n y)
    (ae_of_all _ fun y => by simpa [g, L] using truncatedKernel_tendsto omega hR f x y)
  let H : ℝ → R3 := fun t =>
    ∫ z, bogovskiiDensity omega R t f x z • z ∂(volume : Measure R3)
  have hH : Continuous H := continuous_bogovskiiSlice omega hR hf hfsupp x
  have htail : ∀ n, (∫ t in εn n..1, H t) = ∫ y, g n y ∂(volume : Measure R3) := by
    intro n
    have h := bogovskii_truncated_eq omega hR hf hfsupp x (hε0 n) (hε1 n)
    rw [hinv n] at h
    simpa [H, g, εn] using h
  have hconst : ∀ n,
      (∫ t in (0 : ℝ)..εn n, H t) + ∫ y, g n y ∂(volume : Measure R3) =
        bogovskiiNonsingular omega R f x := by
    intro n
    have hadd := _root_.intervalIntegral.integral_add_adjacent_intervals
      (hH.intervalIntegrable (μ := (volume : Measure ℝ)) 0 (εn n))
      (hH.intervalIntegrable (μ := (volume : Measure ℝ)) (εn n) 1)
    rw [← htail n, hadd]
    simp [bogovskiiNonsingular, H, εn]
  have hsum : Tendsto (fun n => (∫ t in (0 : ℝ)..εn n, H t) + ∫ y, g n y ∂(volume : Measure R3))
      atTop (𝓝 (0 + ∫ y, L y ∂(volume : Measure R3))) :=
    (bogovskiiSlice_head_tendsto omega hR hf hfsupp x).add hDCT
  have hconst_tendsto : Tendsto
      (fun n => (∫ t in (0 : ℝ)..εn n, H t) + ∫ y, g n y ∂(volume : Measure R3))
      atTop (𝓝 (bogovskiiNonsingular omega R f x)) :=
    tendsto_const_nhds.congr' (Eventually.of_forall fun n => (hconst n).symm)
  have hun := tendsto_nhds_unique hconst_tendsto hsum
  have hBog : Bogovskii omega R f x = ∫ y, L y ∂(volume : Measure R3) := by
    simp only [Bogovskii, BogovskiiKernel, L]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    beta_reduce
    rw [smul_smul]
    conv_rhs => rw [smul_smul]
    set s : ℝ := ∫ r in Set.Ioi (1 : ℝ),
      bogovskii_cutoff omega R (y + r • (x - y)) * r ^ 2
    rw [mul_comm (f y) s]
  rw [zero_add] at hun
  rw [hun, hBog]

/-- Classical divergence inverts `Bogovskii` on smooth mean-zero data supported
in the ball. The nonsingular formula is differentiated under the integral,
the `t`-derivative is a divergence, and the fundamental theorem of calculus
on `σ(t) = ∫ density` uses `∫ ω = 1` and `∫ f = 0`. The singular kernel
equals that formula by the ray reparametrization and dominated convergence. -/
theorem BogovskiiDiv_closed (omega : BogovskiiCutoff) {R : ℝ} (hR : 0 < R)
    {f : R3 → ℝ} (hf : ContDiff ℝ ⊤ f) (_hfc : HasCompactSupport f)
    (hf0 : (∫ y, f y ∂(volume : Measure R3)) = 0)
    (hfsupp : Function.support f ⊆ ballR R) :
    ContDiff ℝ ⊤ (Bogovskii omega R f) ∧
      HasCompactSupport (Bogovskii omega R f) ∧
      Function.support (Bogovskii omega R f) ⊆ ballR R ∧
      ∀ x, divClassical (Bogovskii omega R f) x = f x := by
  have heq : Bogovskii omega R f = bogovskiiNonsingular omega R f :=
    (bogovskiiNonsingular_eq_Bogovskii omega hR hf hfsupp).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [heq]
    exact bogovskiiNonsingular_smooth omega hR hf hfsupp
  · rw [heq]
    exact bogovskiiNonsingular_hasCompactSupport omega hR hfsupp
  · rw [heq]
    exact bogovskiiNonsingular_support omega hR hfsupp
  · intro x
    rw [heq]
    exact bogovskiiNonsingular_div omega hR hf hfsupp hf0 x

open scoped RealInnerProductSpace

private lemma cutoff_unit_bound (omega : BogovskiiCutoff) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |omega.toFun x| ≤ M :=
  exists_abs_bound_of_ball omega.smooth.continuous omega.support_in_unit_ball one_pos

private lemma cutoff_scaled_bound (omega : BogovskiiCutoff) {R : ℝ} (hR : 0 < R) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |bogovskii_cutoff omega R x| ≤ M * (R ^ 3)⁻¹ := by
  obtain ⟨M, hM, hle⟩ := cutoff_unit_bound omega
  refine ⟨M, hM, fun x => ?_⟩
  unfold bogovskii_cutoff
  have hinv : 0 ≤ (R ^ 3)⁻¹ := inv_nonneg.mpr (pow_nonneg hR.le 3)
  calc |(R ^ 3)⁻¹ * omega.toFun (R⁻¹ • x)|
      = (R ^ 3)⁻¹ * |omega.toFun (R⁻¹ • x)| := by rw [abs_mul, abs_of_nonneg hinv]
    _ ≤ (R ^ 3)⁻¹ * M := mul_le_mul_of_nonneg_left (hle (R⁻¹ • x)) hinv
    _ = M * (R ^ 3)⁻¹ := mul_comm _ _

private lemma l2_sq_of_compact {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {g : R3 → E} (hg : Continuous g) (hsupp : HasCompactSupport g) :
    Memℒp g 2 (volume : Measure R3) ∧
      (eLpNorm g 2 (volume : Measure R3)).toReal ^ 2 =
        ∫ x, ‖g x‖ ^ 2 ∂(volume : Measure R3) := by
  have hsuppeq : Function.support (fun x => ‖g x‖ ^ 2) = Function.support g := by
    ext x
    simp [Function.mem_support, sq_eq_zero_iff, norm_eq_zero]
  have hsqsupp : HasCompactSupport (fun x => ‖g x‖ ^ 2) := by
    simpa [HasCompactSupport, tsupport, hsuppeq] using hsupp
  have hsqcont : Continuous (fun x => ‖g x‖ ^ 2) := (continuous_norm.comp hg).pow 2
  have hsq : Integrable (fun x => ‖g x‖ ^ 2) (volume : Measure R3) :=
    hsqcont.integrable_of_hasCompactSupport hsqsupp
  have hmem : Memℒp g 2 (volume : Measure R3) :=
    (memℒp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).2 hsq
  have hnonneg : 0 ≤ ∫ x, ‖g x‖ ^ (2 : ℝ) ∂(volume : Measure R3) :=
    integral_nonneg fun _ => by positivity
  have hnorm := hmem.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.two_ne_top
  have htwo : (2 : ENNReal).toReal = 2 := by norm_num
  rw [htwo] at hnorm
  have hto : (eLpNorm g 2 (volume : Measure R3)).toReal =
      (∫ x, ‖g x‖ ^ (2 : ℝ) ∂(volume : Measure R3)) ^ (2 : ℝ)⁻¹ := by
    rw [hnorm, ENNReal.toReal_ofReal (Real.rpow_nonneg hnonneg _)]
  refine ⟨hmem, ?_⟩
  have hhalf : (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
  calc (eLpNorm g 2 (volume : Measure R3)).toReal ^ 2
      = ((∫ x, ‖g x‖ ^ (2 : ℝ) ∂(volume : Measure R3)) ^ (2 : ℝ)⁻¹) ^ 2 := by rw [hto]
    _ = (Real.sqrt (∫ x, ‖g x‖ ^ (2 : ℝ) ∂(volume : Measure R3))) ^ 2 := by
          rw [hhalf, ← Real.sqrt_eq_rpow]
    _ = ∫ x, ‖g x‖ ^ (2 : ℝ) ∂(volume : Measure R3) :=
          Real.sq_sqrt (integral_nonneg fun _ => by positivity)
    _ = ∫ x, ‖g x‖ ^ 2 ∂(volume : Measure R3) := by
          refine integral_congr_ae (ae_of_all _ fun x => ?_)
          exact Real.rpow_two _

private lemma mul_L2_of_ball {f : R3 → ℝ} {u : R3 → R3} {v : R3} {R : ℝ}
    (hf : Continuous f) (hfsupp : Function.support f ⊆ ballR R)
    (hu : Continuous u) (huc : HasCompactSupport u) :
    ∫ x, |f (x - v)| * ‖u x‖ ∂(volume : Measure R3) ≤
      (eLpNorm f 2 (volume : Measure R3)).toReal *
        (eLpNorm u 2 (volume : Measure R3)).toReal := by
  have hshift_supp : Function.support (fun x => f (x - v)) ⊆ Metric.closedBall v R := by
    intro x hx
    have hxball : x - v ∈ ballR R :=
      hfsupp (by simpa [Function.mem_support] using hx)
    have hlt : ‖x - v‖ < R := by
      simpa [ballR, Metric.mem_ball, dist_zero_right] using hxball
    rw [Metric.mem_closedBall, dist_eq_norm]
    simpa using (le_of_lt hlt)
  have hfc' : HasCompactSupport (fun x => f (x - v)) :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall v R) hshift_supp
  have hf' : Continuous (fun x => f (x - v)) :=
    hf.comp (continuous_id.sub continuous_const)
  have hfc0 : HasCompactSupport f :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : R3) R)
      (hfsupp.trans Metric.ball_subset_closedBall)
  obtain ⟨hfmem, _⟩ := l2_sq_of_compact hf' hfc'
  obtain ⟨_, hfsq0⟩ := l2_sq_of_compact hf hfc0
  obtain ⟨_, husq⟩ := l2_sq_of_compact hu huc
  have hunorm : Memℒp (fun x => ‖u x‖) 2 (volume : Measure R3) := by
    have hint : Integrable (fun x => ‖u x‖ ^ 2) (volume : Measure R3) :=
      (memℒp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).1
        (l2_sq_of_compact hu huc).1
    exact (memℒp_two_iff_integrable_sq (continuous_norm.comp hu).aestronglyMeasurable).2 hint
  have hshift := integral_add_right (fun x => ‖f x‖ ^ 2) (-v)
  have hconj : (2 : ℝ).IsConjExponent 2 := by
    rw [Real.isConjExponent_iff]
    norm_num
  have htwo : ENNReal.ofReal 2 = 2 := by norm_num
  have hholder := integral_mul_norm_le_Lp_mul_Lq (μ := (volume : Measure R3)) hconj
    (f := fun x => f (x - v)) (g := fun x => ‖u x‖)
    (by simpa [htwo] using hfmem) (by simpa [htwo] using hunorm)
  have habs : (∫ x, |f (x - v)| * ‖u x‖ ∂(volume : Measure R3)) =
      ∫ x, ‖f (x - v)‖ * ‖‖u x‖‖ ∂(volume : Measure R3) := by
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp [norm_norm, Real.norm_eq_abs]
  have hsqf : (∫ x, ‖f (x - v)‖ ^ 2 ∂(volume : Measure R3)) ^ (2 : ℝ)⁻¹ =
      (eLpNorm f 2 (volume : Measure R3)).toReal := by
    rw [show (∫ x, ‖f (x - v)‖ ^ 2 ∂(volume : Measure R3)) =
        ∫ x, ‖f (x + -v)‖ ^ 2 ∂(volume : Measure R3) by rfl, hshift, ← hfsq0]
    have hinv : (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
    rw [hinv, ← Real.sqrt_eq_rpow, Real.sqrt_sq ENNReal.toReal_nonneg]
  have hsqu : (∫ x, ‖‖u x‖‖ ^ 2 ∂(volume : Measure R3)) ^ (2 : ℝ)⁻¹ =
      (eLpNorm u 2 (volume : Measure R3)).toReal := by
    rw [show (∫ x, ‖‖u x‖‖ ^ 2 ∂(volume : Measure R3)) =
        ∫ x, ‖u x‖ ^ 2 ∂(volume : Measure R3) by
          refine integral_congr_ae (ae_of_all _ fun x => ?_)
          simp [norm_norm], ← husq]
    have hinv : (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
    rw [hinv, ← Real.sqrt_eq_rpow, Real.sqrt_sq ENNReal.toReal_nonneg]
  rw [habs]
  calc ∫ x, ‖f (x - v)‖ * ‖‖u x‖‖ ∂(volume : Measure R3)
      ≤ (∫ x, ‖f (x - v)‖ ^ 2 ∂(volume : Measure R3)) ^ (1 / 2 : ℝ) *
          (∫ x, ‖‖u x‖‖ ^ 2 ∂(volume : Measure R3)) ^ (1 / 2 : ℝ) := hholder
    _ = (∫ x, ‖f (x - v)‖ ^ 2 ∂(volume : Measure R3)) ^ (2 : ℝ)⁻¹ *
          (∫ x, ‖‖u x‖‖ ^ 2 ∂(volume : Measure R3)) ^ (2 : ℝ)⁻¹ := by
          congr 1 <;> congr 1 <;> norm_num
    _ = (eLpNorm f 2 (volume : Measure R3)).toReal *
          (eLpNorm u 2 (volume : Measure R3)).toReal := by rw [hsqf, hsqu]

/-- Volume of a closed ball of radius `r` in `R3`, scaled from the unit ball. -/
private lemma closedBall_volume_toReal {r : ℝ} (hr : 0 ≤ r) :
    (volume (Metric.closedBall (0 : R3) r)).toReal =
      r ^ 3 * (volume (Metric.closedBall (0 : R3) 1)).toReal := by
  have hrB := InnerProductSpace.volume_closedBall (0 : R3) r
  have h1 := InnerProductSpace.volume_closedBall (0 : R3) (1 : ℝ)
  rw [finrank_R3] at hrB h1
  have h1' : volume (Metric.closedBall (0 : R3) 1) =
      ENNReal.ofReal (Real.sqrt Real.pi ^ 3 / Real.Gamma (↑(3 : ℕ) / 2 + 1)) := by
    simpa [ENNReal.ofReal_one, one_pow, one_mul] using h1
  rw [hrB, ← ENNReal.ofReal_pow hr 3, ← h1', ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hr 3)]

/-- The radius factor produced by `|z| ≤ 2R` and the cutoff height `R⁻³`. -/
private lemma bogovskii_L2_factor {R M V : ℝ} (hR : 0 < R) :
    M * (R ^ 3)⁻¹ * (2 * R) * ((2 * R) ^ 3 * V) = 16 * M * V * R := by
  have hpow : (2 * R) ^ 3 = 8 * (R ^ 3) := by ring
  have hinv : (R ^ 3)⁻¹ * (R ^ 3) = 1 := inv_mul_cancel₀ (pow_ne_zero 3 hR.ne')
  calc
    M * (R ^ 3)⁻¹ * (2 * R) * ((2 * R) ^ 3 * V)
        = M * (R ^ 3)⁻¹ * (2 * R) * ((8 * (R ^ 3)) * V) := by rw [hpow]
    _ = M * ((R ^ 3)⁻¹ * (R ^ 3)) * (2 * R) * 8 * V := by ring
    _ = M * 1 * (2 * R) * 8 * V := by rw [hinv]
    _ = 16 * M * V * R := by ring

/-- On the nonsingular slice, `|z| ≥ 2R` kills the density, and inside that ball
`|ω_R| ≤ M R⁻³`. -/
private lemma bogovskiiSlice_norm_le (omega : BogovskiiCutoff) {R : ℝ} (hR : 0 < R)
    {f : R3 → ℝ} (hf : Continuous f) (hfsupp : Function.support f ⊆ ballR R)
    {M : ℝ} (hM : 0 ≤ M)
    (hcut : ∀ x, |bogovskii_cutoff omega R x| ≤ M * (R ^ 3)⁻¹) (t : ℝ) (x : R3) :
    ‖∫ z, bogovskiiDensity omega R t f x z • z ∂(volume : Measure R3)‖ ≤
      (M * (R ^ 3)⁻¹ * (2 * R)) *
        ∫ z in Metric.closedBall (0 : R3) (2 * R),
          |f (x - t • z)| ∂(volume : Measure R3) := by
  let B : Set R3 := Metric.closedBall (0 : R3) (2 * R)
  let c0 : ℝ := M * (R ^ 3)⁻¹ * (2 * R)
  let F : R3 → R3 := fun z => bogovskiiDensity omega R t f x z • z
  have hden : Continuous (fun z => bogovskiiDensity omega R t f x z) := by
    unfold bogovskiiDensity
    exact ((bogovskii_cutoff_smooth omega R).continuous.comp
        (continuous_const.add ((continuous_const.sub continuous_const).smul continuous_id))).mul
      (hf.comp (continuous_const.sub (continuous_const.smul continuous_id)))
  have hFcont : Continuous F := hden.smul continuous_id
  have hFsupp : Function.support F ⊆ B := by
    intro z hz
    by_contra hnot
    have hlt : 2 * R < ‖z‖ :=
      lt_of_not_ge fun hle => hnot ((mem_closedBall_norm_zero).2 hle)
    have h0 : bogovskiiDensity omega R t f x z = 0 :=
      bogovskiiDensity_eq_zero_of_large_z omega hR hfsupp t x z hlt.le
    exact hz (by simp [F, h0, zero_smul])
  have hFcs : HasCompactSupport F :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall _ _) hFsupp
  have hnormsupp : HasCompactSupport (fun z => ‖F z‖) := by
    have hsuppeq : Function.support (fun z => ‖F z‖) = Function.support F := by
      ext z
      simp [Function.mem_support, norm_eq_zero]
    simpa [HasCompactSupport, tsupport, hsuppeq] using hFcs
  have hnormint : Integrable (fun z => ‖F z‖) (volume : Measure R3) :=
    (continuous_norm.comp hFcont).integrable_of_hasCompactSupport hnormsupp
  let major : R3 → ℝ := fun z => c0 * B.indicator (fun w => |f (x - t • w)|) z
  have hfabs : Continuous (fun z => |f (x - t • z)|) :=
    (continuous_abs.comp hf).comp (continuous_const.sub (continuous_const.smul continuous_id))
  have hmaj : Integrable major (volume : Measure R3) := by
    have hintB : IntegrableOn (fun z => |f (x - t • z)|) B (volume : Measure R3) :=
      hfabs.continuousOn.integrableOn_compact (isCompact_closedBall _ _)
    simpa [major] using
      (hintB.integrable_indicator measurableSet_closedBall).const_mul c0
  have hpoint : ∀ z, ‖F z‖ ≤ major z := by
    intro z
    by_cases hz : z ∈ B
    · have hzn : ‖z‖ ≤ 2 * R := (mem_closedBall_norm_zero).1 hz
      simp only [major, Set.indicator_of_mem hz]
      calc ‖F z‖
          = |bogovskiiDensity omega R t f x z| * ‖z‖ := by
              rw [norm_smul, Real.norm_eq_abs]
        _ = |bogovskii_cutoff omega R (x + (1 - t) • z)| * |f (x - t • z)| * ‖z‖ := by
              rw [bogovskiiDensity, abs_mul]
        _ ≤ (M * (R ^ 3)⁻¹) * |f (x - t • z)| * ‖z‖ := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right (hcut _) (abs_nonneg _)) (norm_nonneg _)
        _ ≤ (M * (R ^ 3)⁻¹) * |f (x - t • z)| * (2 * R) := by
              exact mul_le_mul_of_nonneg_left hzn
                (mul_nonneg (mul_nonneg hM (inv_nonneg.mpr (pow_nonneg hR.le 3))) (abs_nonneg _))
        _ = c0 * |f (x - t • z)| := by ring
    · have hlt : 2 * R < ‖z‖ :=
        lt_of_not_ge fun hle => hz ((mem_closedBall_norm_zero).2 hle)
      have h0 : bogovskiiDensity omega R t f x z = 0 :=
        bogovskiiDensity_eq_zero_of_large_z omega hR hfsupp t x z hlt.le
      simp [F, major, h0, Set.indicator_of_not_mem hz, zero_smul, norm_zero]
  have hint_eq : ∫ z, major z ∂(volume : Measure R3) =
      c0 * ∫ z in B, |f (x - t • z)| ∂(volume : Measure R3) := by
    simp only [major]
    rw [integral_mul_left, integral_indicator measurableSet_closedBall]
  calc ‖∫ z, F z ∂(volume : Measure R3)‖
      ≤ ∫ z, ‖F z‖ ∂(volume : Measure R3) := norm_integral_le_integral_norm _
    _ ≤ ∫ z, major z ∂(volume : Measure R3) := integral_mono hnormint hmaj hpoint
    _ = c0 * ∫ z in B, |f (x - t • z)| ∂(volume : Measure R3) := hint_eq

/-- Minkowski in the translation parameter, on a finite-measure set of shifts. -/
private lemma shift_setIntegral_L2 {f : R3 → ℝ} {u : R3 → R3} {t r : ℝ}
    (hf : Continuous f) (hfsupp : Function.support f ⊆ ballR r) (hr : 0 < r)
    (hu : Continuous u) (huc : HasCompactSupport u) {B : Set R3}
    (hBm : MeasurableSet B) (hBfin : volume B < ⊤) :
    ∫ x, ‖u x‖ * (∫ z in B, |f (x - t • z)| ∂(volume : Measure R3))
        ∂(volume : Measure R3) ≤
      (volume B).toReal * (eLpNorm f 2 (volume : Measure R3)).toReal *
        (eLpNorm u 2 (volume : Measure R3)).toReal := by
  obtain ⟨Mf, hMf0, hMf⟩ := exists_abs_bound_of_ball hf hfsupp hr
  have hun : Integrable (fun x => ‖u x‖) (volume : Measure R3) := by
    have hsuppeq : Function.support (fun x => ‖u x‖) = Function.support u := by
      ext x
      simp [Function.mem_support, norm_eq_zero]
    have hcs : HasCompactSupport (fun x => ‖u x‖) := by
      simpa [HasCompactSupport, tsupport, hsuppeq] using huc
    exact (continuous_norm.comp hu).integrable_of_hasCompactSupport hcs
  let ν : Measure R3 := (volume : Measure R3).restrict B
  have hone : Integrable (fun _ : R3 => (1 : ℝ)) ν := by
    rw [integrable_const_iff]
    refine Or.inr ?_
    rw [Measure.restrict_apply_univ]
    exact hBfin
  have hdom : Integrable (fun p : R3 × R3 => Mf * ‖u p.1‖) ((volume : Measure R3).prod ν) := by
    simpa using ((hun.const_mul Mf).prod_mul hone)
  have hψ : Integrable (fun p : R3 × R3 => ‖u p.1‖ * |f (p.1 - t • p.2)|)
      ((volume : Measure R3).prod ν) := by
    refine hdom.mono' ?_ ?_
    · exact ((continuous_norm.comp hu).comp continuous_fst).mul
        ((continuous_abs.comp hf).comp
          (continuous_fst.sub (continuous_const.smul continuous_snd)))
        |>.aestronglyMeasurable
    · refine ae_of_all _ fun p => ?_
      have hnn : 0 ≤ ‖u p.1‖ * |f (p.1 - t • p.2)| :=
        mul_nonneg (norm_nonneg _) (abs_nonneg _)
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      exact mul_le_mul_of_nonneg_left (hMf _) (norm_nonneg _) |>.trans_eq (mul_comm _ _)
  have hψu : Integrable (Function.uncurry fun x z => ‖u x‖ * |f (x - t • z)|)
      ((volume : Measure R3).prod ν) := by
    simpa [Function.uncurry] using hψ
  have hswap := integral_integral_swap
    (μ := (volume : Measure R3)) (ν := ν)
    (f := fun x z => ‖u x‖ * |f (x - t • z)|) hψu
  have hpull : ∀ x, ∫ z in B, ‖u x‖ * |f (x - t • z)| ∂(volume : Measure R3) =
      ‖u x‖ * ∫ z in B, |f (x - t • z)| ∂(volume : Measure R3) := by
    intro x
    simpa using (integral_mul_left (‖u x‖) (fun z => |f (x - t • z)|) (μ := ν))
  have hpt : ∀ z, ∫ x, ‖u x‖ * |f (x - t • z)| ∂(volume : Measure R3) ≤
      (eLpNorm f 2 (volume : Measure R3)).toReal *
        (eLpNorm u 2 (volume : Measure R3)).toReal := by
    intro z
    have hcomm : ∫ x, ‖u x‖ * |f (x - t • z)| ∂(volume : Measure R3) =
        ∫ x, |f (x - t • z)| * ‖u x‖ ∂(volume : Measure R3) := by
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      ring
    rw [hcomm]
    exact mul_L2_of_ball hf hfsupp hu huc
  have hintz : IntegrableOn
      (fun z => ∫ x, ‖u x‖ * |f (x - t • z)| ∂(volume : Measure R3)) B
      (volume : Measure R3) :=
    hψu.integral_prod_right
  have hconst : IntegrableOn
      (fun _ : R3 => (eLpNorm f 2 (volume : Measure R3)).toReal *
        (eLpNorm u 2 (volume : Measure R3)).toReal) B (volume : Measure R3) :=
    (integrableOn_const.2 (Or.inr hBfin))
  have hineq := setIntegral_mono_on (μ := (volume : Measure R3)) (s := B) hintz hconst hBm
    (fun z _ => hpt z)
  calc ∫ x, ‖u x‖ * (∫ z in B, |f (x - t • z)| ∂(volume : Measure R3))
        ∂(volume : Measure R3)
      = ∫ x, (∫ z in B, ‖u x‖ * |f (x - t • z)| ∂(volume : Measure R3))
          ∂(volume : Measure R3) := by
          refine integral_congr_ae (ae_of_all _ fun x => ?_)
          exact (hpull x).symm
    _ = ∫ z in B, (∫ x, ‖u x‖ * |f (x - t • z)| ∂(volume : Measure R3))
          ∂(volume : Measure R3) := hswap
    _ ≤ ∫ z in B, (eLpNorm f 2 (volume : Measure R3)).toReal *
          (eLpNorm u 2 (volume : Measure R3)).toReal ∂(volume : Measure R3) := hineq
    _ = (volume B).toReal * ((eLpNorm f 2 (volume : Measure R3)).toReal *
          (eLpNorm u 2 (volume : Measure R3)).toReal) := by
          simpa using (setIntegral_const (μ := (volume : Measure R3)) (s := B)
            ((eLpNorm f 2 (volume : Measure R3)).toReal *
              (eLpNorm u 2 (volume : Measure R3)).toReal))
    _ = (volume B).toReal * (eLpNorm f 2 (volume : Measure R3)).toReal *
          (eLpNorm u 2 (volume : Measure R3)).toReal := by ring

set_option maxHeartbeats 2000000 in
/-- `‖Bogovskii ω R f‖₂ ≤ C R ‖f‖₂`. The factor `R` is the volume of the
region `|z| ≤ 2R` on which the nonsingular density can be nonzero, times
the `R⁻³` height of the rescaled cutoff. This is the same scaling as
`∫_{|z|<2R} |z|⁻² dz` in the Schur test for `|K| ≤ C / |x-y|²`. -/
lemma bogovskii_L2_bound (omega : BogovskiiCutoff) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {R : ℝ} {f : R3 → ℝ},
      0 < R →
      ContDiff ℝ ⊤ f →
      Function.support f ⊆ ballR R →
      L2Norm (fun x => ‖Bogovskii omega R f x‖) ≤ C * R * L2Norm f := by
  obtain ⟨M, hM, hcut⟩ := cutoff_unit_bound omega
  let V : ℝ := (volume (Metric.closedBall (0 : R3) 1)).toReal
  refine ⟨16 * M * V, mul_nonneg (mul_nonneg (by norm_num) hM) ENNReal.toReal_nonneg, ?_⟩
  intro R f hR hf hfsupp
  have hcutR : ∀ x, |bogovskii_cutoff omega R x| ≤ M * (R ^ 3)⁻¹ := by
    intro x
    unfold bogovskii_cutoff
    have hinv : 0 ≤ (R ^ 3)⁻¹ := inv_nonneg.mpr (pow_nonneg hR.le 3)
    calc |(R ^ 3)⁻¹ * omega.toFun (R⁻¹ • x)|
        = (R ^ 3)⁻¹ * |omega.toFun (R⁻¹ • x)| := by rw [abs_mul, abs_of_nonneg hinv]
      _ ≤ (R ^ 3)⁻¹ * M := mul_le_mul_of_nonneg_left (hcut _) hinv
      _ = M * (R ^ 3)⁻¹ := mul_comm _ _
  let H : ℝ → R3 → R3 := fun t x =>
    ∫ z, bogovskiiDensity omega R t f x z • z ∂(volume : Measure R3)
  let u : R3 → R3 := bogovskiiNonsingular omega R f
  have hu_eq : Bogovskii omega R f = u :=
    (bogovskiiNonsingular_eq_Bogovskii omega hR hf hfsupp).symm
  have hu_supp : HasCompactSupport u := bogovskiiNonsingular_hasCompactSupport omega hR hfsupp
  have hu_cont : Continuous u :=
    (bogovskiiNonsingular_smooth omega hR hf hfsupp).continuous
  have hf_supp : HasCompactSupport f :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : R3) R)
      (hfsupp.trans Metric.ball_subset_closedBall)
  obtain ⟨_, hfu⟩ := l2_sq_of_compact hu_cont hu_supp
  let Nu : ℝ := (eLpNorm u 2 (volume : Measure R3)).toReal
  let Nf : ℝ := (eLpNorm f 2 (volume : Measure R3)).toReal
  have hNu : L2Norm (fun x => ‖Bogovskii omega R f x‖) = Nu := by
    simp [L2Norm, Nu, hu_eq, eLpNorm_norm]
  have hNf : L2Norm f = Nf := rfl
  have hNusq : Nu ^ 2 = ∫ x, ‖u x‖ ^ 2 ∂(volume : Measure R3) := hfu
  let B : Set R3 := Metric.closedBall (0 : R3) (2 * R)
  let c0 : ℝ := M * (R ^ 3)⁻¹ * (2 * R)
  have hc0 : 0 ≤ c0 :=
    mul_nonneg (mul_nonneg hM (inv_nonneg.mpr (pow_nonneg hR.le 3)))
      (mul_nonneg zero_le_two hR.le)
  have hslice : ∀ t x, ‖H t x‖ ≤
      c0 * ∫ z in B, |f (x - t • z)| ∂(volume : Measure R3) := by
    intro t x
    simpa [H, B, c0] using
      bogovskiiSlice_norm_le omega hR hf.continuous hfsupp hM hcutR t x
  have hHjoint : Continuous (fun p : R3 × ℝ => H p.2 p.1) := by
    refine (contDiff_zero (𝕜 := ℝ)).1 ?_
    rw [contDiff_iff_contDiffAt]
    intro p
    dsimp only [H]
    exact contDiffAt_zIntegral (n := 0) (S := 2 * R)
      (F := fun q z => bogovskiiDensity omega R q.2 f q.1 z • z)
      (bogovskiiIntegrand_contDiff omega R hf)
      (fun q z hz => by
        simp [bogovskiiDensity_eq_zero_of_large_z omega hR hfsupp q.2 q.1 z hz.le, zero_smul])
      p
  let S : Set (R3 × ℝ) := Metric.closedBall (0 : R3) R ×ˢ Set.Icc (0 : ℝ) 1
  have hSne : S.Nonempty :=
    ⟨(0, 0), ⟨Metric.mem_closedBall_self hR.le, ⟨le_rfl, zero_le_one⟩⟩⟩
  obtain ⟨p0, -, hmax⟩ :=
    ((isCompact_closedBall (0 : R3) R).prod isCompact_Icc).exists_isMaxOn hSne
      (continuous_norm.comp hHjoint).continuousOn
  let Cbound : ℝ := ‖H p0.2 p0.1‖
  have hCbound : ∀ q ∈ S, ‖H q.2 q.1‖ ≤ Cbound := fun q hq => hmax hq
  have hun : Integrable (fun x => ‖u x‖) (volume : Measure R3) := by
    have hsuppeq : Function.support (fun x => ‖u x‖) = Function.support u := by
      ext x
      simp [Function.mem_support, norm_eq_zero]
    have hcs : HasCompactSupport (fun x => ‖u x‖) := by
      simpa [HasCompactSupport, tsupport, hsuppeq] using hu_supp
    exact (continuous_norm.comp hu_cont).integrable_of_hasCompactSupport hcs
  let ν : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)
  have hone : Integrable (fun _ : ℝ => (1 : ℝ)) ν := by
    rw [integrable_const_iff]
    refine Or.inr ?_
    rw [Measure.restrict_apply_univ]
    exact measure_Ioc_lt_top
  have hdom : Integrable (fun p : R3 × ℝ => Cbound * ‖u p.1‖)
      ((volume : Measure R3).prod ν) := by
    simpa using ((hun.const_mul Cbound).prod_mul hone)
  have hu_out : ∀ x, x ∉ Metric.closedBall (0 : R3) R → u x = 0 := by
    intro x hx
    exact Function.nmem_support.mp fun hs =>
      hx (Metric.ball_subset_closedBall (bogovskiiNonsingular_support omega hR hfsupp hs))
  have habs_ae : ∀ᵐ p ∂((volume : Measure R3).prod ν),
      ‖⟪u p.1, H p.2 p.1⟫‖ ≤ Cbound * ‖u p.1‖ := by
    have hfull : ∀ᵐ p ∂((volume : Measure R3).prod ν), p.2 ∈ Set.Ioc (0 : ℝ) 1 := by
      rw [ae_iff]
      have hs : {p : R3 × ℝ | p.2 ∉ Set.Ioc (0 : ℝ) 1} =
          (Set.univ : Set R3) ×ˢ (Set.Ioc (0 : ℝ) 1)ᶜ := by
        ext p
        simp [Set.mem_prod]
      rw [hs, Measure.prod_prod, Measure.restrict_apply measurableSet_Ioc.compl]
      simp [Set.compl_inter_self]
    refine hfull.mono fun p hp => ?_
    by_cases hx : p.1 ∈ Metric.closedBall (0 : R3) R
    · have ht : p.2 ∈ Set.Icc (0 : ℝ) 1 := Set.Ioc_subset_Icc_self hp
      have hHle := hCbound (p.1, p.2) ⟨hx, ht⟩
      calc ‖⟪u p.1, H p.2 p.1⟫‖
          = |⟪u p.1, H p.2 p.1⟫| := by rw [Real.norm_eq_abs]
        _ ≤ ‖u p.1‖ * ‖H p.2 p.1‖ := abs_real_inner_le_norm _ _
        _ ≤ ‖u p.1‖ * Cbound := mul_le_mul_of_nonneg_left hHle (norm_nonneg _)
        _ = Cbound * ‖u p.1‖ := mul_comm _ _
    · have h0 : u p.1 = 0 := hu_out p.1 hx
      simp [h0, Real.norm_eq_abs]
  have hφ : Integrable (fun p : R3 × ℝ => ⟪u p.1, H p.2 p.1⟫)
      ((volume : Measure R3).prod ν) := by
    refine hdom.mono' ?_ habs_ae
    exact (continuous_inner.comp (hu_cont.comp continuous_fst |>.prod_mk hHjoint)).aestronglyMeasurable
  have hφu : Integrable (Function.uncurry fun x t => ⟪u x, H t x⟫)
      ((volume : Measure R3).prod ν) := by
    simpa [Function.uncurry] using hφ
  have hswap := integral_integral_swap (μ := (volume : Measure R3)) (ν := ν)
    (f := fun x t => ⟪u x, H t x⟫) hφu
  have hsqx : ∀ x, ‖u x‖ ^ 2 =
      ∫ t in Set.Ioc (0 : ℝ) 1, ⟪u x, H t x⟫ ∂(volume : Measure ℝ) := by
    intro x
    have hcont : Continuous (fun t => H t x) := continuous_bogovskiiSlice omega hR hf hfsupp x
    have hintH : IntegrableOn (fun t => H t x) (Set.Ioc (0 : ℝ) 1) (volume : Measure ℝ) :=
      hcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
    have hHu : u x = ∫ t in Set.Ioc (0 : ℝ) 1, H t x ∂(volume : Measure ℝ) := by
      simpa [u, bogovskiiNonsingular, H] using
        (_root_.intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1)
          (μ := (volume : Measure ℝ))
          (f := fun t =>
            ∫ z, bogovskiiDensity omega R t f x z • z ∂(volume : Measure R3)))
    rw [← real_inner_self_eq_norm_sq]
    calc ⟪u x, u x⟫
        = ⟪u x, ∫ t in Set.Ioc (0 : ℝ) 1, H t x ∂(volume : Measure ℝ)⟫ := by rw [hHu]
      _ = ∫ t in Set.Ioc (0 : ℝ) 1, ⟪u x, H t x⟫ ∂(volume : Measure ℝ) :=
          (integral_inner hintH (u x)).symm
  have hsq_swap : ∫ x, ‖u x‖ ^ 2 ∂(volume : Measure R3) =
      ∫ t in Set.Ioc (0 : ℝ) 1,
        (∫ x, ⟪u x, H t x⟫ ∂(volume : Measure R3)) ∂(volume : Measure ℝ) := by
    have hcongr : ∫ x, ‖u x‖ ^ 2 ∂(volume : Measure R3) =
        ∫ x, (∫ t in Set.Ioc (0 : ℝ) 1, ⟪u x, H t x⟫ ∂(volume : Measure ℝ))
          ∂(volume : Measure R3) := by
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      exact hsqx x
    rw [hcongr]
    simpa [ν] using hswap
  have hshift : ∀ t : ℝ, ∫ x, ‖u x‖ *
        (∫ z in B, |f (x - t • z)| ∂(volume : Measure R3)) ∂(volume : Measure R3) ≤
      (volume B).toReal * Nf * Nu := by
    intro t
    simpa [B, Nf, Nu] using
      shift_setIntegral_L2 hf.continuous hfsupp hR hu_cont hu_supp measurableSet_closedBall
        ((isCompact_closedBall (0 : R3) (2 * R)).measure_lt_top) (t := t) (B := B)
  have hinner_le : ∀ t : ℝ, ∫ x, ⟪u x, H t x⟫ ∂(volume : Measure R3) ≤
      c0 * (volume B).toReal * Nf * Nu := by
    intro t
    have hHt : Continuous (fun x => H t x) :=
      hHjoint.comp (continuous_id.prod_mk continuous_const)
    have hφcont : Continuous (fun x => ⟪u x, H t x⟫) :=
      continuous_inner.comp (hu_cont.prod_mk hHt)
    have hφcs : HasCompactSupport (fun x => ⟪u x, H t x⟫) := by
      have hsub : Function.support (fun x => ⟪u x, H t x⟫) ⊆ Function.support u := by
        intro x hx
        by_contra hnot
        exact hx (by simp [Function.nmem_support.mp hnot])
      exact HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : R3) R)
        (hsub.trans ((bogovskiiNonsingular_support omega hR hfsupp).trans
          Metric.ball_subset_closedBall))
    have hφint : Integrable (fun x => ⟪u x, H t x⟫) (volume : Measure R3) :=
      hφcont.integrable_of_hasCompactSupport hφcs
    have hrhs : Integrable (fun x => c0 * ‖u x‖ *
        (∫ z in B, |f (x - t • z)| ∂(volume : Measure R3))) (volume : Measure R3) := by
      obtain ⟨Mf, hMf0, hMf⟩ := exists_abs_bound_of_ball hf.continuous hfsupp hR
      have hIle : ∀ x, ∫ z in B, |f (x - t • z)| ∂(volume : Measure R3) ≤
          Mf * (volume B).toReal := by
        intro x
        have hint : IntegrableOn (fun z => |f (x - t • z)|) B (volume : Measure R3) :=
          ((continuous_abs.comp hf.continuous).comp
            (continuous_const.sub (continuous_const.smul continuous_id))).continuousOn.integrableOn_compact
            (isCompact_closedBall _ _)
        have hconst : IntegrableOn (fun _ : R3 => Mf) B (volume : Measure R3) :=
          (integrableOn_const.2 (Or.inr (isCompact_closedBall _ _).measure_lt_top))
        have hmono := setIntegral_mono_on hint hconst measurableSet_closedBall
          (fun z _ => hMf (x - t • z))
        have hconst_int := setIntegral_const (μ := (volume : Measure R3)) (s := B) Mf
        calc ∫ z in B, |f (x - t • z)| ∂(volume : Measure R3)
            ≤ ∫ z in B, Mf ∂(volume : Measure R3) := hmono
          _ = (volume B).toReal * Mf := by simpa [smul_eq_mul] using hconst_int
          _ = Mf * (volume B).toReal := by ring
      let ρ : ℝ := R + |t| * (2 * R)
      let K : Set R3 := Metric.closedBall (0 : R3) ρ
      have hind : Integrable (K.indicator fun _ => Mf) (volume : Measure R3) := by
        rw [integrable_indicator_iff measurableSet_closedBall]
        exact integrableOn_const.2 (Or.inr (isCompact_closedBall _ _).measure_lt_top)
      have honeB : Integrable (fun _ : R3 => (1 : ℝ))
          ((volume : Measure R3).restrict B) := by
        rw [integrable_const_iff]
        refine Or.inr ?_
        rw [Measure.restrict_apply_univ]
        exact (isCompact_closedBall _ _).measure_lt_top
      have hdomp : Integrable (fun p : R3 × R3 => K.indicator (fun _ => Mf) p.1 * (1 : ℝ))
          ((volume : Measure R3).prod ((volume : Measure R3).restrict B)) :=
        hind.prod_mul honeB
      have hψf : Integrable (fun p : R3 × R3 => |f (p.1 - t • p.2)|)
          ((volume : Measure R3).prod ((volume : Measure R3).restrict B)) := by
        refine hdomp.mono' ?_ ?_
        · exact ((continuous_abs.comp hf.continuous).comp
            (continuous_fst.sub (continuous_const.smul continuous_snd))).aestronglyMeasurable
        · have hfull : ∀ᵐ p ∂((volume : Measure R3).prod ((volume : Measure R3).restrict B)),
              p.2 ∈ B := by
            rw [ae_iff]
            have hs : {p : R3 × R3 | p.2 ∉ B} =
                (Set.univ : Set R3) ×ˢ Bᶜ := by
              ext p; simp [Set.mem_prod]
            rw [hs, Measure.prod_prod, Measure.restrict_apply measurableSet_closedBall.compl]
            simp [Set.compl_inter_self]
          refine hfull.mono fun p hp => ?_
          have hnn : 0 ≤ |f (p.1 - t • p.2)| := abs_nonneg _
          rw [Real.norm_eq_abs, abs_of_nonneg hnn]
          by_cases hx : p.1 ∈ K
          · rw [Set.indicator_of_mem hx, mul_one]
            exact hMf _
          · rw [Set.indicator_of_not_mem hx, zero_mul]
            have hbig : ρ < ‖p.1‖ := by
              rw [mem_closedBall_norm_zero] at hx
              exact lt_of_not_ge hx
            have hzero : f (p.1 - t • p.2) = 0 := by
              rw [← Function.nmem_support]
              intro hs
              have hlt : ‖p.1 - t • p.2‖ < R := by
                simpa [ballR, Metric.mem_ball, dist_zero_right] using hfsupp hs
              have hzn : ‖p.2‖ ≤ 2 * R := (mem_closedBall_norm_zero).1 hp
              have hle : ‖p.1‖ ≤ ‖p.1 - t • p.2‖ + ‖t • p.2‖ := by
                simpa [sub_add_cancel] using norm_add_le (p.1 - t • p.2) (t • p.2)
              have htz : ‖t • p.2‖ = |t| * ‖p.2‖ := by
                rw [norm_smul, Real.norm_eq_abs]
              have : ‖p.1‖ < R + |t| * (2 * R) := by
                calc ‖p.1‖ ≤ ‖p.1 - t • p.2‖ + ‖t • p.2‖ := hle
                  _ < R + |t| * ‖p.2‖ := by
                      rw [htz]
                      exact add_lt_add_right hlt _
                  _ ≤ R + |t| * (2 * R) := by
                      gcongr
              exact lt_irrefl _ (this.trans hbig)
            simp [hzero]
      have hI : Integrable (fun x => ∫ z in B, |f (x - t • z)| ∂(volume : Measure R3))
          (volume : Measure R3) := by
        simpa using hψf.integral_prod_left
      have hdomx : Integrable (fun x => (c0 * Mf * (volume B).toReal) * ‖u x‖)
          (volume : Measure R3) := hun.const_mul _
      refine hdomx.mono' ?_ ?_
      · exact (((continuous_const.mul (continuous_norm.comp hu_cont)).aestronglyMeasurable).mul
          hI.aestronglyMeasurable)
      · refine ae_of_all _ fun x => ?_
        have hnn : 0 ≤ c0 * ‖u x‖ * ∫ z in B, |f (x - t • z)| ∂(volume : Measure R3) :=
          mul_nonneg (mul_nonneg hc0 (norm_nonneg _))
            (integral_nonneg fun _ => abs_nonneg _)
        rw [Real.norm_eq_abs, abs_of_nonneg hnn]
        calc c0 * ‖u x‖ * ∫ z in B, |f (x - t • z)| ∂(volume : Measure R3)
            ≤ c0 * ‖u x‖ * (Mf * (volume B).toReal) := by
              exact mul_le_mul_of_nonneg_left (hIle x) (mul_nonneg hc0 (norm_nonneg _))
          _ = (c0 * Mf * (volume B).toReal) * ‖u x‖ := by ring
    have habs : ∀ x, ⟪u x, H t x⟫ ≤
        c0 * ‖u x‖ * ∫ z in B, |f (x - t • z)| ∂(volume : Measure R3) := by
      intro x
      calc ⟪u x, H t x⟫ ≤ |⟪u x, H t x⟫| := le_abs_self _
        _ ≤ ‖u x‖ * ‖H t x‖ := abs_real_inner_le_norm _ _
        _ ≤ ‖u x‖ * (c0 * ∫ z in B, |f (x - t • z)| ∂(volume : Measure R3)) :=
            mul_le_mul_of_nonneg_left (hslice t x) (norm_nonneg _)
        _ = c0 * ‖u x‖ * ∫ z in B, |f (x - t • z)| ∂(volume : Measure R3) := by ring
    calc ∫ x, ⟪u x, H t x⟫ ∂(volume : Measure R3)
        ≤ ∫ x, c0 * ‖u x‖ * ∫ z in B, |f (x - t • z)| ∂(volume : Measure R3)
            ∂(volume : Measure R3) := integral_mono hφint hrhs habs
      _ = c0 * ∫ x, ‖u x‖ * ∫ z in B, |f (x - t • z)| ∂(volume : Measure R3)
            ∂(volume : Measure R3) := by
          rw [← integral_mul_left]
          refine integral_congr_ae (ae_of_all _ fun x => ?_)
          ring
      _ ≤ c0 * ((volume B).toReal * Nf * Nu) :=
          mul_le_mul_of_nonneg_left (hshift t) hc0
      _ = c0 * (volume B).toReal * Nf * Nu := by ring
  have hton : IntegrableOn (fun t => ∫ x, ⟪u x, H t x⟫ ∂(volume : Measure R3))
      (Set.Ioc (0 : ℝ) 1) (volume : Measure ℝ) := hφu.integral_prod_right
  have hconst_t : IntegrableOn (fun _ : ℝ => c0 * (volume B).toReal * Nf * Nu)
      (Set.Ioc (0 : ℝ) 1) (volume : Measure ℝ) :=
    (integrableOn_const.2 (Or.inr measure_Ioc_lt_top))
  have havg := setIntegral_mono_on (μ := (volume : Measure ℝ)) (s := Set.Ioc (0 : ℝ) 1)
    hton hconst_t measurableSet_Ioc (fun t _ => hinner_le t)
  have hlen : ∫ t in Set.Ioc (0 : ℝ) 1, c0 * (volume B).toReal * Nf * Nu
      ∂(volume : Measure ℝ) = c0 * (volume B).toReal * Nf * Nu := by
    rw [setIntegral_const, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal zero_le_one, one_smul]
  have hsq_le : Nu ^ 2 ≤ c0 * (volume B).toReal * Nf * Nu := by
    rw [hNusq, hsq_swap]
    exact havg.trans_eq hlen
  have hvol : (volume B).toReal = (2 * R) ^ 3 * V := by
    simpa [B, V] using closedBall_volume_toReal (mul_nonneg zero_le_two hR.le)
  have hfac : c0 * (volume B).toReal = (16 * M * V) * R := by
    rw [hvol]
    simpa [c0] using bogovskii_L2_factor hR (M := M) (V := V)
  have hfinal : Nu ^ 2 ≤ ((16 * M * V) * R * Nf) * Nu := by
    calc Nu ^ 2 ≤ c0 * (volume B).toReal * Nf * Nu := hsq_le
      _ = ((16 * M * V) * R) * Nf * Nu := by rw [hfac]
      _ = ((16 * M * V) * R * Nf) * Nu := by ring
  rw [hNu, hNf]
  by_cases h0 : Nu = 0
  · rw [h0]
    positivity
  · have hpos : 0 < Nu := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm h0)
    have hmul : Nu * Nu ≤ Nu * ((16 * M * V) * R * Nf) := by
      simpa [sq, mul_comm, mul_left_comm, mul_assoc] using hfinal
    exact le_of_mul_le_mul_left hmul hpos

/-- OPEN. `H¹` bound for the Bogovskii operator. Not a theorem.

The factor `(1 + R)` is the standard scaling: `bogovskii_L2_bound` gives
`‖B f‖₂ ≤ C R ‖f‖₂` with `C = 16 M vol(closedBall 0 1)`, while
`‖∇(B f)‖₂` is dimensionless. `H1Norm` packages both, so this proposition
stays open until the gradient piece is proved.

The gradient piece is not the Schur test `|∇K| ≤ C/|x-y|³`: that majorant
is not integrable. Integration by parts in the nonsingular formula leaves
a factor `t⁻¹` on `(0,1]`, which is not absolutely integrable. It is also
not the identity `‖∇u‖₂² ≤ C(‖u‖₂² + ‖div u‖₂²)`. For a compactly supported
field, `‖∇u‖₂² = ‖div u‖₂² + ‖curl u‖₂²`, so `div u = f` only lower-bounds
the gradient by `‖f‖₂`. A high-frequency divergence-free summand makes the
gradient arbitrarily larger. The cutoff operator is not the whole-space
Fourier multiplier right inverse of divergence, so Plancherel would not
close it. Mathlib v4.12 has no Calderón–Zygmund theorem. The missing
lemma is an `L²` bound on each `coordinateDerivative (Bogovskii ω R f)`. -/
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
