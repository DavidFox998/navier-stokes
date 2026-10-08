/-
Wall266 H4/L4 norm scaffolding.

This file introduces a genuine L4 quantity through Mathlib's eLpNorm and an
H1 quantity built from the vector L2 norm and the componentwise L2 norm of
the classical first derivatives. `H4Norm` is the square root of that same H1
energy plus the L2 energies of the ordered coordinate derivatives of length
2, 3, and 4. `H4Norm_placeholder` is unchanged and is not an H4 norm.

The noncompact smooth vector-valued H1 embedding below has a written proof:
coordinate derivative comparisons, explicit expanding compact cutoffs,
the pinned compact Sobolev inequality, Fatou, and L2/L6 interpolation.
The proof preserves the square-root H1 quantity, keeps the original finite
coordinate-derivative hypotheses, and proves extended-real finiteness before
converting to a real norm. It does not assert a theorem about a separately
formalized weak H1 space. Compilation and a kernel dependency audit have
not been run.
The 4-4-2 Holder inequality uses Mathlib's extended-real Holder API.
`trilinear_H4_bound` is the analytic estimate
|b(u,v,w)| ≤ C_trilinear * H4Norm u * H4Norm v * L2Norm w,
obtained from holder_4442 with exponents 4, 4, 2, the H1→L4 bound, and
H1Norm ≤ H4Norm. The factors are ‖u‖₄, ‖∇v‖₄, and ‖w‖₂.
Compilation and a kernel dependency audit have not been run.
-/

import Towers.NS.Wall266_TrilinearForm
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Normed.MulAction
import Mathlib.Analysis.NormedSpace.OperatorNorm.Bilinear
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace TheoremaAureum.Towers.NS.Wall266

open MeasureTheory EuclideanSpace
open scoped BigOperators ENNReal NNReal

/-- The real-valued L4 quantity, obtained from Mathlib's extended-real
eLpNorm. The .toReal conversion is needed because eLpNorm itself is
ℝ≥0∞-valued. This is the usual real L4 norm when the extended norm is
finite; .toReal maps infinity to zero, so finiteness is required when using
this quantity as a norm. -/
noncomputable def eLpNorm_L4 (f : R3 → ℝ) : ℝ :=
  (eLpNorm f 4 (volume : Measure R3)).toReal

/-- The classical coordinate derivative of component j in direction i.
For the smooth test fields used below, these are the first derivatives entering
the usual H1 norm. -/
noncomputable def partialDerivative (v : R3 → R3) (i j : Fin 3) : R3 → ℝ :=
  fun x => deriv (fun t : ℝ => (v (x + t • EuclideanSpace.single i 1)) j) 0

/-- The H1 quantity sqrt(‖v‖_L2^2 + ‖∇v‖_L2^2), with the gradient L2
term expressed as the sum of the nine componentwise derivative L2 norms.
This is the classical H1 norm on smooth fields with finite L2 quantities, not
a norm on all arbitrary functions: .toReal maps infinity to zero, and deriv
is the classical derivative. A general weak-derivative H1 space remains OPEN. -/
noncomputable def H1Norm (v : R3 → R3) : ℝ :=
  Real.sqrt
    ((eLpNorm v 2 (volume : Measure R3)).toReal ^ 2 +
      ∑ i : Fin 3, ∑ j : Fin 3,
        (eLpNorm (partialDerivative v i j) 2 (volume : Measure R3)).toReal ^ 2)

/-- OPEN: iterated weak derivatives are not defined in this development, so
this is only the underlying L2 norm. It is a placeholder, not an H4 norm. -/
noncomputable def H4Norm_placeholder (v : L2DivFree) : ℝ := ‖v‖

/-- The existing Mathlib W1,1 Sobolev constant for dimension three.
This is an actual defined constant, not an assumed inequality. -/
noncomputable def C1 : ℝ≥0 :=
  eLpNormLESNormFDerivOneConst (volume : Measure R3) (3 / 2 : ℝ)

/-- The existing Mathlib Hilbert-valued p = 2 Sobolev constant on R3. -/
noncomputable def C_Sobolev : ℝ≥0 :=
  eLpNormLESNormFDerivOfEqInnerConst (volume : Measure R3) (2 : ℝ)

/-- The interpolation constant arising from the compact-support L6 estimate. -/
noncomputable def C_GN : ℝ≥0 := C_Sobolev ^ (3 / 4 : ℝ)

private theorem ennreal_ofNat (n : ℕ) : (n : ℝ≥0∞) = ENNReal.ofReal (n : ℝ) :=
  (ENNReal.ofReal_coe_nnreal (p := (n : ℝ≥0))).symm

private theorem ennreal_inv_add_inv_two :
    (2 : ℝ≥0∞)⁻¹ + (2 : ℝ≥0∞)⁻¹ = 1 := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hcoe : (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) := by
    rw [← Nat.cast_ofNat]
    exact ennreal_ofNat 2
  have hinv : (2 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (2 : ℝ)⁻¹ := by
    rw [hcoe, ENNReal.ofReal_inv_of_pos h2]
  rw [hinv, ← ENNReal.ofReal_add (inv_nonneg.2 h2.le) (inv_nonneg.2 h2.le)]
  have hsum : (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ = 1 := by norm_num
  rw [hsum]
  exact ENNReal.ofReal_one

private theorem ennreal_inv_four_add :
    (4 : ℝ≥0∞)⁻¹ + (4 : ℝ≥0∞)⁻¹ = (2 : ℝ≥0∞)⁻¹ := by
  have h4 : (0 : ℝ) < 4 := by norm_num
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hcoe4 : (4 : ℝ≥0∞) = ENNReal.ofReal (4 : ℝ) := by
    rw [← Nat.cast_ofNat]
    exact ennreal_ofNat 4
  have hcoe2 : (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) := by
    rw [← Nat.cast_ofNat]
    exact ennreal_ofNat 2
  have hinv4 : (4 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (4 : ℝ)⁻¹ := by
    rw [hcoe4, ENNReal.ofReal_inv_of_pos h4]
  have hinv2 : (2 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (2 : ℝ)⁻¹ := by
    rw [hcoe2, ENNReal.ofReal_inv_of_pos h2]
  rw [hinv4, hinv2, ← ENNReal.ofReal_add (inv_nonneg.2 h4.le) (inv_nonneg.2 h4.le)]
  have hsum : (4 : ℝ)⁻¹ + (4 : ℝ)⁻¹ = (2 : ℝ)⁻¹ := by norm_num
  rw [hsum]

private theorem ennreal_holder_div_122 :
    (1 : ℝ≥0∞) / 1 = 1 / 2 + 1 / 2 := by
  have hdiv1 : (1 : ℝ≥0∞) / 1 = 1 := by
    rw [div_eq_mul_inv, inv_one, mul_one]
  have hdiv2 : (1 : ℝ≥0∞) / 2 = (2 : ℝ≥0∞)⁻¹ := by
    rw [div_eq_mul_inv, one_mul]
  rw [hdiv1, hdiv2]
  exact ennreal_inv_add_inv_two.symm

private theorem ennreal_holder_div_244 :
    (1 : ℝ≥0∞) / 2 = 1 / 4 + 1 / 4 := by
  have hdiv2 : (1 : ℝ≥0∞) / 2 = (2 : ℝ≥0∞)⁻¹ := by
    rw [div_eq_mul_inv, one_mul]
  have hdiv4 : (1 : ℝ≥0∞) / 4 = (4 : ℝ≥0∞)⁻¹ := by
    rw [div_eq_mul_inv, one_mul]
  rw [hdiv2, hdiv4]
  exact ennreal_inv_four_add.symm

section SobolevSteps

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Genuine L2/L6 interpolation, with extended-real norms and explicit measure.
The measurability hypothesis is needed by Mathlib's Holder API. Finiteness is
not needed for this extended-real inequality; it is needed before converting
these quantities to real norms with `.toReal`.

Holder is applied to ‖u‖ and ‖u‖^3 in L2, followed by a fourth root.
No interpolation wrapper is assumed. -/
theorem L4_interpolation_L2_L6 {u : R3 → F}
    (hu : AEStronglyMeasurable u (volume : Measure R3)) :
    eLpNorm u 4 volume ≤
      (eLpNorm u 2 volume) ^ (1 / 4 : ℝ) *
        (eLpNorm u 6 volume) ^ (3 / 4 : ℝ) := by
  have h4 :
      eLpNorm (fun x => ‖u x‖ ^ (4 : ℕ)) 1 volume =
        (eLpNorm u 4 volume) ^ (4 : ℝ) := by
    have h := eLpNorm_norm_rpow (p := (1 : ℝ≥0∞))
      (μ := (volume : Measure R3)) u (by norm_num : 0 < (4 : ℝ))
    have hfun : (fun x => ‖u x‖ ^ (4 : ℝ)) = fun x => ‖u x‖ ^ (4 : ℕ) := by
      funext x
      exact Real.rpow_natCast (‖u x‖) 4
    have hidx : (1 : ℝ≥0∞) * ENNReal.ofReal (4 : ℝ) = 4 := by
      rw [one_mul]
      simpa [Nat.cast_ofNat] using (ennreal_ofNat 4).symm
    rw [hfun, hidx] at h
    exact h
  have h3 :
      eLpNorm (fun x => ‖u x‖ ^ (3 : ℕ)) 2 volume =
        (eLpNorm u 6 volume) ^ (3 : ℝ) := by
    have h := eLpNorm_norm_rpow (p := (2 : ℝ≥0∞))
      (μ := (volume : Measure R3)) u (by norm_num : 0 < (3 : ℝ))
    have hfun : (fun x => ‖u x‖ ^ (3 : ℝ)) = fun x => ‖u x‖ ^ (3 : ℕ) := by
      funext x
      exact Real.rpow_natCast (‖u x‖) 3
    have hmul : (2 : ℝ≥0∞) * ENNReal.ofReal (3 : ℝ) = 6 := by
      have h3eq : ENNReal.ofReal (3 : ℝ) = 3 := by
        simpa [Nat.cast_ofNat] using (ennreal_ofNat 3).symm
      rw [h3eq, ← Nat.cast_ofNat (n := 2), ← Nat.cast_ofNat (n := 3), ← Nat.cast_mul]
      rw [show (2 * 3 : ℕ) = 6 from rfl]
      exact Nat.cast_ofNat
    rw [hfun, hmul] at h
    exact h
  have hHolder :
      eLpNorm (fun x => ‖u x‖ * ‖u x‖ ^ (3 : ℕ)) 1 volume ≤
        eLpNorm (fun x => ‖u x‖) 2 volume *
          eLpNorm (fun x => ‖u x‖ ^ (3 : ℕ)) 2 volume := by
    refine eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm
      hu.norm (hu.norm.pow 3) (fun a b : ℝ => a * b) ?_ ?_
    · exact Filter.Eventually.of_forall
        (fun x => le_of_eq (nnnorm_mul (‖u x‖) (‖u x‖ ^ (3 : ℕ))))
    · exact ennreal_holder_div_122
  have hPower :
      (eLpNorm u 4 volume) ^ (4 : ℝ) ≤
        eLpNorm u 2 volume * (eLpNorm u 6 volume) ^ (3 : ℝ) := by
    calc
      (eLpNorm u 4 volume) ^ (4 : ℝ)
          = eLpNorm (fun x => ‖u x‖ ^ (4 : ℕ)) 1 volume := h4.symm
      _ = eLpNorm (fun x => ‖u x‖ * ‖u x‖ ^ (3 : ℕ)) 1 volume := by
        congr 1
        funext x
        ring
      _ ≤ _ := hHolder
      _ = _ := by rw [eLpNorm_norm, h3]
  have hRoot := ENNReal.rpow_le_rpow hPower (by norm_num : 0 ≤ (1 / 4 : ℝ))
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : 0 ≤ (1 / 4 : ℝ)),
    ← ENNReal.rpow_mul, ← ENNReal.rpow_mul] at hRoot
  norm_num at hRoot ⊢
  exact hRoot

/-- The compact-support W1,1 → L3/2 inequality already proved in Mathlib v4.12.
The derivative is the genuine Frechet derivative, measured with its operator
norm. This is not a statement about undefined coordinate-derivative notation. -/
theorem W11_embedding_L32_R3 {w : R3 → F}
    (hw : HasCompactSupport w) (hs : ContDiff ℝ 1 w) :
    eLpNorm w (3 / 2 : ℝ≥0∞) volume ≤
      (C1 : ℝ≥0∞) * eLpNorm (fderiv ℝ w) 1 volume := by
  have hdim : FiniteDimensional.finrank ℝ R3 = 3 := finrank_euclideanSpace_fin
  have hp : NNReal.IsConjExponent
      (FiniteDimensional.finrank ℝ R3) (3 / 2 : ℝ≥0) := by
    rw [hdim]
    constructor
    · norm_num
    · apply NNReal.coe_injective
      simp only [NNReal.coe_add, NNReal.coe_inv, NNReal.coe_div, NNReal.coe_one,
        NNReal.coe_ofNat]
      norm_num
  have h := eLpNorm_le_eLpNorm_fderiv_one (volume : Measure R3) hs hw hp
  simpa [C1] using h

end SobolevSteps

section HilbertSobolevSteps

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Compact-support H1 → L6, using Mathlib's proved Nirenberg argument.
No scalar H1 norm is invented: the RHS is the L2 seminorm of the actual
Frechet derivative. The existing `H1Norm` is vector-valued and is unchanged. -/
theorem H1_embedding_L6_Sobolev {u : R3 → F}
    (hcs : HasCompactSupport u) (hs : ContDiff ℝ 1 u) :
    eLpNorm u 6 volume ≤
      (C_Sobolev : ℝ≥0∞) * eLpNorm (fderiv ℝ u) 2 volume := by
  have hdim : FiniteDimensional.finrank ℝ R3 = 3 := finrank_euclideanSpace_fin
  have h := eLpNorm_le_eLpNorm_fderiv_of_eq_inner (volume : Measure R3)
    hs hcs (p := (2 : ℝ≥0)) (p' := (6 : ℝ≥0))
    (by norm_num) (by rw [hdim]; norm_num) (by rw [hdim]; norm_num)
  simpa [C_Sobolev] using h

/-- Compact-support Gagliardo-Nirenberg estimate, obtained by combining
the two actual inequalities above. This is not the noncompact vector H1
embedding declared below. -/
theorem H1_embedding_L4_compact_GN {u : R3 → F}
    (hcs : HasCompactSupport u) (hs : ContDiff ℝ 1 u) :
    eLpNorm u 4 volume ≤
      (C_GN : ℝ≥0∞) * (eLpNorm u 2 volume) ^ (1 / 4 : ℝ) *
        (eLpNorm (fderiv ℝ u) 2 volume) ^ (3 / 4 : ℝ) := by
  calc
    eLpNorm u 4 volume ≤
        (eLpNorm u 2 volume) ^ (1 / 4 : ℝ) *
          (eLpNorm u 6 volume) ^ (3 / 4 : ℝ) :=
      L4_interpolation_L2_L6 hs.continuous.aestronglyMeasurable
    _ ≤ (eLpNorm u 2 volume) ^ (1 / 4 : ℝ) *
        ((C_Sobolev : ℝ≥0∞) * eLpNorm (fderiv ℝ u) 2 volume) ^ (3 / 4 : ℝ) :=
      mul_le_mul_left'
        (ENNReal.rpow_le_rpow (H1_embedding_L6_Sobolev hcs hs)
          (by norm_num : 0 ≤ (3 / 4 : ℝ))) _
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : 0 ≤ (3 / 4 : ℝ)),
        ← ENNReal.coe_rpow_of_nonneg _ (by norm_num : 0 ≤ (3 / 4 : ℝ))]
      change (eLpNorm u 2 volume) ^ (1 / 4 : ℝ) *
          ((C_GN : ℝ≥0∞) * (eLpNorm (fderiv ℝ u) 2 volume) ^ (3 / 4 : ℝ)) =
        (C_GN : ℝ≥0∞) * (eLpNorm u 2 volume) ^ (1 / 4 : ℝ) *
          (eLpNorm (fderiv ℝ u) 2 volume) ^ (3 / 4 : ℝ)
      rw [mul_left_comm, mul_assoc]

/-- A genuine Fatou passage for compact approximants with uniformly bounded
L2 Frechet derivatives. The approximation hypotheses are explicit: this lemma
does NOT assert that the previous L2-only density theorem supplies them. -/
theorem L6_bound_of_compact_approximation {u : R3 → F}
    (u_n : ℕ → R3 → F)
    (hcs : ∀ n, HasCompactSupport (u_n n))
    (hs : ∀ n, ContDiff ℝ 1 (u_n n))
    (hpoint : ∀ᵐ x ∂(volume : Measure R3),
      Filter.Tendsto (fun n => u_n n x) Filter.atTop (nhds (u x)))
    {D : ℝ≥0∞}
    (hderiv : ∀ n, eLpNorm (fderiv ℝ (u_n n)) 2 volume ≤ D) :
    eLpNorm u 6 volume ≤ (C_Sobolev : ℝ≥0∞) * D := by
  have hFatou := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := (6 : ℝ≥0∞))
    (fun n => (hs n).continuous.aestronglyMeasurable) u hpoint
  refine hFatou.trans ?_
  apply Filter.liminf_le_of_frequently_le'
  exact (Filter.Eventually.of_forall (fun n =>
    (H1_embedding_L6_Sobolev (hcs n) (hs n)).trans
      (mul_le_mul_left' (hderiv n) _))).frequently

end HilbertSobolevSteps

/-- The vector L2 quantity is bounded by the preserved square-root H1 quantity. -/
theorem H1Norm_L2_le (v : R3 → R3) :
    (eLpNorm v 2 (volume : Measure R3)).toReal ≤ H1Norm v := by
  unfold H1Norm
  apply Real.le_sqrt_of_sq_le
  exact le_add_of_nonneg_right
    (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)

/-- Each of the nine real coordinate-derivative L2 quantities is bounded by H1.
Finiteness must still be supplied before converting extended norms to real ones. -/
theorem H1Norm_partial_L2_le (v : R3 → R3) (i j : Fin 3) :
    (eLpNorm (partialDerivative v i j) 2 (volume : Measure R3)).toReal ≤
      H1Norm v := by
  unfold H1Norm
  apply Real.le_sqrt_of_sq_le
  have hj :
      (eLpNorm (partialDerivative v i j) 2 (volume : Measure R3)).toReal ^ 2 ≤
        ∑ k : Fin 3,
          (eLpNorm (partialDerivative v i k) 2 (volume : Measure R3)).toReal ^ 2 :=
    Finset.single_le_sum
      (f := fun k : Fin 3 =>
        (eLpNorm (partialDerivative v i k) 2 (volume : Measure R3)).toReal ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  have hi :
      (∑ k : Fin 3,
        (eLpNorm (partialDerivative v i k) 2 (volume : Measure R3)).toReal ^ 2) ≤
        ∑ l : Fin 3, ∑ k : Fin 3,
          (eLpNorm (partialDerivative v l k) 2 (volume : Measure R3)).toReal ^ 2 :=
    Finset.single_le_sum
      (f := fun l : Fin 3 => ∑ k : Fin 3,
        (eLpNorm (partialDerivative v l k) 2 (volume : Measure R3)).toReal ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  exact (hj.trans hi).trans (le_add_of_nonneg_left (sq_nonneg _))

private noncomputable def coordinateNormConstant : ℝ≥0 :=
  1 + ∑ i : Fin 3, ‖(EuclideanSpace.proj i : R3 →L[ℝ] ℝ)‖₊

private theorem coordinate_projection_norm_le (i : Fin 3) :
    ‖(EuclideanSpace.proj i : R3 →L[ℝ] ℝ)‖ ≤ (coordinateNormConstant : ℝ) := by
  have h : ‖(EuclideanSpace.proj i : R3 →L[ℝ] ℝ)‖₊ ≤ coordinateNormConstant := by
    unfold coordinateNormConstant
    exact (Finset.single_le_sum
      (f := fun k : Fin 3 => ‖(EuclideanSpace.proj k : R3 →L[ℝ] ℝ)‖₊)
      (fun _ _ => zero_le _) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left (zero_le (1 : ℝ≥0)))
  exact_mod_cast h

private theorem euclidean_sum_coordinates (z : R3) :
    z = ∑ i : Fin 3, z i • EuclideanSpace.single i 1 := by
  ext j
  let ev : R3 →+ ℝ :=
    { toFun := fun w => w j
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  change ev z = ev (∑ i : Fin 3, z i • EuclideanSpace.single i 1)
  rw [map_sum]
  simp [ev, EuclideanSpace.single_apply]

private theorem euclidean_norm_le_sum_coordinates (z : R3) :
    ‖z‖ ≤ ∑ i : Fin 3, ‖z i‖ := by
  calc
    ‖z‖ = ‖∑ i : Fin 3, z i • EuclideanSpace.single i 1‖ :=
      congrArg norm (euclidean_sum_coordinates z)
    _ ≤ ∑ i : Fin 3, ‖z i • EuclideanSpace.single i 1‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_smul, EuclideanSpace.norm_single, norm_one, mul_one]

private theorem scalar_operator_norm_le_coordinates (L : R3 →L[ℝ] ℝ) :
    ‖L‖ ≤ (coordinateNormConstant : ℝ) *
      ∑ i : Fin 3, ‖L (EuclideanSpace.single i 1)‖ := by
  refine L.opNorm_le_bound ?_ ?_
  · exact mul_nonneg (NNReal.coe_nonneg coordinateNormConstant)
      (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  intro z
  have hL : L z = ∑ i : Fin 3, z i • L (EuclideanSpace.single i 1) := by
    conv_lhs => rw [euclidean_sum_coordinates z]
    simp only [map_sum, ContinuousLinearMap.map_smul]
  rw [hL]
  refine (norm_sum_le _ _).trans ?_
  simp only [norm_smul]
  refine (Finset.sum_le_sum fun i _ => ?_).trans ?_
  · apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    rw [← EuclideanSpace.proj_apply i z]
    exact ((EuclideanSpace.proj i).le_opNorm z).trans
      (mul_le_mul_of_nonneg_right (coordinate_projection_norm_le i) (norm_nonneg _))
  · rw [← Finset.mul_sum, mul_assoc,
      mul_comm (‖z‖) (∑ i : Fin 3, ‖L (EuclideanSpace.single i 1)‖), ← mul_assoc]

private theorem partialDerivative_eq_fderiv_component {v : R3 → R3}
    (i j : Fin 3) (x : R3)
    (hv : DifferentiableAt ℝ (fun y => v y j) x) :
    partialDerivative v i j x =
      fderiv ℝ (fun y => v y j) x (EuclideanSpace.single i 1) := by
  have hline : HasDerivAt
      (fun t : ℝ => x + t • EuclideanSpace.single i 1)
      (EuclideanSpace.single i 1) 0 := by
    simpa only [zero_add, one_smul] using
      (hasDerivAt_const (0 : ℝ) x).add
        ((hasDerivAt_id' (0 : ℝ)).smul_const (EuclideanSpace.single i 1))
  have h := hv.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline
    (by simp only [zero_smul, add_zero])
  simpa only [partialDerivative, Function.comp_def] using h.deriv

private def spatialCutoff : ContDiffBump (0 : R3) where
  rIn := 1
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

private noncomputable def spatialCutoffLipschitzConstant : ℝ≥0 :=
  Classical.choose (ContDiff.lipschitzWith_of_hasCompactSupport
    spatialCutoff.hasCompactSupport
    (spatialCutoff.contDiff : ContDiff ℝ 1 (spatialCutoff : R3 → ℝ)) le_rfl)

private theorem spatialCutoff_lipschitz :
    LipschitzWith spatialCutoffLipschitzConstant (spatialCutoff : R3 → ℝ) :=
  Classical.choose_spec (ContDiff.lipschitzWith_of_hasCompactSupport
    spatialCutoff.hasCompactSupport
    (spatialCutoff.contDiff : ContDiff ℝ 1 (spatialCutoff : R3 → ℝ)) le_rfl)

private noncomputable def spatialCutoffScale (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹

private theorem spatialCutoffScale_pos (n : ℕ) : 0 < spatialCutoffScale n := by
  unfold spatialCutoffScale
  positivity

private theorem spatialCutoffScale_le_one (n : ℕ) : spatialCutoffScale n ≤ 1 := by
  unfold spatialCutoffScale
  rw [← one_div]
  exact (div_le_one (by positivity : 0 < (n : ℝ) + 1)).2
    (le_add_of_nonneg_left (Nat.cast_nonneg n))

private theorem spatialCutoffScale_tendsto :
    Filter.Tendsto spatialCutoffScale Filter.atTop (nhds (0 : ℝ)) := by
  exact tendsto_inv_atTop_zero.comp
    (Filter.tendsto_atTop_add_const_right Filter.atTop (1 : ℝ)
      (tendsto_natCast_atTop_atTop :
        Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop))

private noncomputable def spatialCutoffSequence (n : ℕ) (x : R3) : ℝ :=
  spatialCutoff (spatialCutoffScale n • x)

private theorem spatialCutoffSequence_smooth (n : ℕ) :
    ContDiff ℝ 1 (spatialCutoffSequence n) :=
  spatialCutoff.contDiff.comp (contDiff_const_smul (spatialCutoffScale n))

private theorem spatialCutoffSequence_compact (n : ℕ) :
    HasCompactSupport (spatialCutoffSequence n) :=
  spatialCutoff.hasCompactSupport.comp_smul (spatialCutoffScale_pos n).ne'

private theorem spatialCutoffSequence_norm_le_one (n : ℕ) (x : R3) :
    ‖spatialCutoffSequence n x‖ ≤ 1 := by
  change ‖spatialCutoff (spatialCutoffScale n • x)‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_nonneg spatialCutoff.nonneg]
  exact spatialCutoff.le_one

private theorem spatialCutoffSequence_derivative_bound (n : ℕ) (x : R3) :
    ‖fderiv ℝ (spatialCutoffSequence n) x‖ ≤
      (spatialCutoffLipschitzConstant : ℝ) := by
  have hscale : ‖spatialCutoffScale n‖₊ ≤ (1 : ℝ≥0) := by
    have hr : ‖spatialCutoffScale n‖ ≤ (1 : ℝ) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (spatialCutoffScale_pos n).le]
      exact spatialCutoffScale_le_one n
    exact_mod_cast hr
  have hl : LipschitzWith
      (spatialCutoffLipschitzConstant * ‖spatialCutoffScale n‖₊)
      (spatialCutoffSequence n) :=
    spatialCutoff_lipschitz.comp (lipschitzWith_smul (spatialCutoffScale n))
  have hl' : LipschitzWith spatialCutoffLipschitzConstant (spatialCutoffSequence n) :=
    hl.weaken (by simpa only [mul_one] using
      mul_le_mul_left' hscale spatialCutoffLipschitzConstant)
  exact norm_fderiv_le_of_lipschitz ℝ hl'

private theorem spatialCutoffSequence_tendsto (x : R3) :
    Filter.Tendsto (fun n => spatialCutoffSequence n x) Filter.atTop (nhds (1 : ℝ)) := by
  have hx : Filter.Tendsto (fun n => spatialCutoffScale n • x)
      Filter.atTop (nhds (0 : R3)) := by
    simpa only [zero_smul] using spatialCutoffScale_tendsto.smul_const x
  have hzero : spatialCutoff (0 : R3) = 1 :=
    spatialCutoff.one_of_mem_closedBall (by simp [spatialCutoff])
  simpa only [spatialCutoffSequence, hzero] using
    (spatialCutoff.continuous.tendsto (0 : R3)).comp hx

/-- Noncompact smooth Sobolev estimate obtained from explicit expanding compact
cutoffs and the proved Fatou passage. Only a uniform derivative bound is needed;
no H1-density or derivative/convolution commutation lemma is assumed.
The extra L2 term permits a simple uniform cutoff estimate. -/
theorem H1_embedding_L6_noncompact {u : R3 → ℝ} (hs : ContDiff ℝ 1 u) :
    eLpNorm u 6 volume ≤ (C_Sobolev : ℝ≥0∞) *
      (eLpNorm (fderiv ℝ u) 2 volume +
        (spatialCutoffLipschitzConstant : ℝ≥0∞) * eLpNorm u 2 volume) := by
  let u_n : ℕ → R3 → ℝ := fun n x => spatialCutoffSequence n x • u x
  have hcs : ∀ n, HasCompactSupport (u_n n) := fun n =>
    (spatialCutoffSequence_compact n).smul_right
  have hn : ∀ n, ContDiff ℝ 1 (u_n n) := fun n =>
    (spatialCutoffSequence_smooth n).smul hs
  have hpoint : ∀ᵐ x ∂(volume : Measure R3),
      Filter.Tendsto (fun n => u_n n x) Filter.atTop (nhds (u x)) :=
    Filter.Eventually.of_forall fun x => by
      simpa only [u_n, one_smul] using (spatialCutoffSequence_tendsto x).smul_const (u x)
  have hderiv : ∀ n, eLpNorm (fderiv ℝ (u_n n)) 2 volume ≤
      eLpNorm (fderiv ℝ u) 2 volume +
        (spatialCutoffLipschitzConstant : ℝ≥0∞) * eLpNorm u 2 volume := by
    intro n
    have hbound : ∀ x, ‖fderiv ℝ (u_n n) x‖ ≤
        ‖fderiv ℝ u x‖ + (spatialCutoffLipschitzConstant : ℝ) * ‖u x‖ := by
      intro x
      change ‖fderiv ℝ (fun y => spatialCutoffSequence n y • u y) x‖ ≤ _
      rw [fderiv_smul
        ((spatialCutoffSequence_smooth n).differentiable le_rfl).differentiableAt
        (hs.differentiable le_rfl).differentiableAt]
      calc
        ‖spatialCutoffSequence n x • fderiv ℝ u x +
            (fderiv ℝ (spatialCutoffSequence n) x).smulRight (u x)‖
            ≤ ‖spatialCutoffSequence n x • fderiv ℝ u x‖ +
              ‖(fderiv ℝ (spatialCutoffSequence n) x).smulRight (u x)‖ := norm_add_le _ _
        _ = ‖spatialCutoffSequence n x‖ * ‖fderiv ℝ u x‖ +
            ‖fderiv ℝ (spatialCutoffSequence n) x‖ * ‖u x‖ := by
          rw [norm_smul, ContinuousLinearMap.norm_smulRight_apply]
        _ ≤ _ := by
          apply add_le_add
          · exact (mul_le_mul_of_nonneg_right
              (spatialCutoffSequence_norm_le_one n x) (norm_nonneg (fderiv ℝ u x))).trans
              (by rw [one_mul])
          · exact mul_le_mul_of_nonneg_right
              (spatialCutoffSequence_derivative_bound n x) (norm_nonneg (u x))
    have ha : AEStronglyMeasurable (fun x => ‖fderiv ℝ u x‖) (volume : Measure R3) :=
      (hs.continuous_fderiv le_rfl).aestronglyMeasurable.norm
    have hb : AEStronglyMeasurable
        ((spatialCutoffLipschitzConstant : ℝ) • (fun x => ‖u x‖)) (volume : Measure R3) :=
      hs.continuous.aestronglyMeasurable.norm.const_smul (spatialCutoffLipschitzConstant : ℝ)
    calc
      eLpNorm (fderiv ℝ (u_n n)) 2 volume ≤
          eLpNorm (fun x => ‖fderiv ℝ u x‖ +
            (spatialCutoffLipschitzConstant : ℝ) * ‖u x‖) 2 volume :=
        eLpNorm_mono_ae_real (Filter.Eventually.of_forall hbound)
      _ ≤ eLpNorm (fun x => ‖fderiv ℝ u x‖) 2 volume +
          eLpNorm ((spatialCutoffLipschitzConstant : ℝ) • (fun x => ‖u x‖)) 2 volume :=
        eLpNorm_add_le ha hb (by norm_num)
      _ = _ := by
        rw [eLpNorm_norm, eLpNorm_const_smul, eLpNorm_norm,
          Real.ennnorm_eq_ofReal spatialCutoffLipschitzConstant.coe_nonneg,
          ENNReal.ofReal_coe_nnreal]
  exact L6_bound_of_compact_approximation u_n hcs hn hpoint hderiv

private theorem component_fderiv_L2_bound (v : TestVectorField)
    (hderiv : ∀ i j : Fin 3,
      Memℒp (partialDerivative v.toFun i j) 2 (volume : Measure R3))
    (H : ℝ≥0)
    (hpartial : ∀ i j : Fin 3,
      eLpNorm (partialDerivative v.toFun i j) 2 volume ≤ (H : ℝ≥0∞))
    (j : Fin 3) :
    eLpNorm (fderiv ℝ (fun x => v.toFun x j)) 2 volume ≤
      (3 : ℝ≥0∞) * (coordinateNormConstant : ℝ≥0∞) * (H : ℝ≥0∞) := by
  have hs : ContDiff ℝ 1 (fun x => v.toFun x j) := by
    have hfun : (fun x => v.toFun x j) = (EuclideanSpace.proj j) ∘ v.toFun := by
      funext x
      exact (EuclideanSpace.proj_apply j (v.toFun x)).symm
    rw [hfun]
    exact (ContDiff.of_le (EuclideanSpace.proj j).contDiff le_top).comp
      (ContDiff.of_le v.smooth le_top)
  have hbound : ∀ x, ‖fderiv ℝ (fun y => v.toFun y j) x‖ ≤
      (coordinateNormConstant : ℝ) * ‖∑ i : Fin 3, ‖partialDerivative v.toFun i j x‖‖ := by
    intro x
    have h := scalar_operator_norm_le_coordinates
      (fderiv ℝ (fun y => v.toFun y j) x)
    have heq : ∀ i : Fin 3,
        fderiv ℝ (fun y => v.toFun y j) x (EuclideanSpace.single i 1) =
          partialDerivative v.toFun i j x := fun i =>
      (partialDerivative_eq_fderiv_component i j x
        (hs.differentiable le_rfl).differentiableAt).symm
    have hsum_nonneg :
        0 ≤ ∑ i : Fin 3, ‖partialDerivative v.toFun i j x‖ :=
      Finset.sum_nonneg fun i _ => norm_nonneg (partialDerivative v.toFun i j x)
    have hsum_norm :
        ‖∑ i : Fin 3, ‖partialDerivative v.toFun i j x‖‖ =
          ∑ i : Fin 3, ‖partialDerivative v.toFun i j x‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg hsum_nonneg]
    rw [hsum_norm]
    simpa only [heq] using h
  have hnn : ∀ x, ‖fderiv ℝ (fun y => v.toFun y j) x‖₊ ≤
      coordinateNormConstant *
        ‖∑ i : Fin 3, ‖partialDerivative v.toFun i j x‖‖₊ := by
    intro x
    apply NNReal.coe_le_coe.mp
    simp only [NNReal.coe_mul, coe_nnnorm]
    exact hbound x
  have hsum :
      eLpNorm (fun x => ∑ i : Fin 3, ‖partialDerivative v.toFun i j x‖) 2 volume ≤
        ∑ i : Fin 3, eLpNorm (partialDerivative v.toFun i j) 2 volume := by
    simpa only [Finset.sum_fn, Finset.sum_apply, eLpNorm_norm] using
      (eLpNorm_sum_le (s := Finset.univ)
        (f := fun i : Fin 3 => fun x : R3 => ‖partialDerivative v.toFun i j x‖)
        (fun i _ => (hderiv i j).aestronglyMeasurable.norm)
        (by norm_num : 1 ≤ (2 : ℝ≥0∞)))
  calc
    eLpNorm (fderiv ℝ (fun x => v.toFun x j)) 2 volume ≤
        coordinateNormConstant •
          eLpNorm (fun x => ∑ i : Fin 3, ‖partialDerivative v.toFun i j x‖) 2 volume :=
      eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
        (c := coordinateNormConstant)
        (Filter.Eventually.of_forall hnn) 2
    _ = (coordinateNormConstant : ℝ≥0∞) *
          eLpNorm (fun x => ∑ i : Fin 3, ‖partialDerivative v.toFun i j x‖) 2 volume := by
      rw [ENNReal.smul_def, smul_eq_mul]
    _ ≤ (coordinateNormConstant : ℝ≥0∞) *
        (∑ i : Fin 3, eLpNorm (partialDerivative v.toFun i j) 2 volume) :=
      mul_le_mul_left' hsum _
    _ ≤ (coordinateNormConstant : ℝ≥0∞) * (∑ _ : Fin 3, (H : ℝ≥0∞)) :=
      mul_le_mul_left' (Finset.sum_le_sum fun i _ => hpartial i j) _
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [mul_left_comm, mul_assoc, Nat.cast_ofNat]

private theorem L4_bound_of_L2_L6 {u : R3 → ℝ}
    (hu : AEStronglyMeasurable u (volume : Measure R3)) (M : ℝ≥0∞)
    (h2 : eLpNorm u 2 volume ≤ M) (h6 : eLpNorm u 6 volume ≤ M) :
    eLpNorm u 4 volume ≤ M := by
  apply (ENNReal.rpow_le_rpow_iff (by norm_num : 0 < (4 : ℝ))).1
  calc
    (eLpNorm u 4 volume) ^ (4 : ℝ) ≤
        ((eLpNorm u 2 volume) ^ (1 / 4 : ℝ) *
          (eLpNorm u 6 volume) ^ (3 / 4 : ℝ)) ^ (4 : ℝ) :=
      ENNReal.rpow_le_rpow (L4_interpolation_L2_L6 hu) (by norm_num)
    _ = eLpNorm u 2 volume * (eLpNorm u 6 volume) ^ (3 : ℝ) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : 0 ≤ (4 : ℝ)),
        ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
      norm_num
    _ ≤ M * M ^ (3 : ℝ) :=
      mul_le_mul' h2 (ENNReal.rpow_le_rpow h6 (by norm_num))
    _ = M ^ (4 : ℝ) := by
      simp [ENNReal.rpow_natCast, pow_succ, mul_comm]

private noncomputable def componentH1L4Constant : ℝ≥0 :=
  1 + coordinateNormConstant +
    C_Sobolev * coordinateNormConstant * (3 + spatialCutoffLipschitzConstant)

/-- An explicit conservative constant for the preserved vector H1 quantity.
It includes the coordinate norm comparison and the uniform cutoff estimate;
it is not asserted to be the sharp compact-support interpolation constant. -/
noncomputable def H1L4Constant : ℝ :=
  ((3 : ℝ≥0) * componentH1L4Constant : ℝ≥0)

/-- The extended-real vector L4 bound. Its finite RHS establishes actual L4
membership rather than exploiting `.toReal` sending infinity to zero.
All first-derivative finiteness hypotheses of the original interface are kept.
This is a written Lean proof; compilation has not been run. -/
theorem H1_embedding_L4_extended (v : TestVectorField)
    (hderiv : ∀ i j : Fin 3,
      Memℒp (partialDerivative v.toFun i j) 2 (volume : Measure R3)) :
    eLpNorm v.toFun 4 volume ≤ ENNReal.ofReal (H1L4Constant * H1Norm v.toFun) := by
  let H : ℝ≥0 := ⟨H1Norm v.toFun, Real.sqrt_nonneg _⟩
  have hvector : Memℒp v.toFun 2 (volume : Measure R3) := by
    have hsum : Memℒp (fun x => ∑ i : Fin 3, ‖v.toFun x i‖) 2 volume := by
      simpa using memℒp_finset_sum Finset.univ (fun i _ => (v.component_L2 i).norm)
    exact hsum.mono' v.smooth.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => euclidean_norm_le_sum_coordinates (v.toFun x))
  have hV2 : eLpNorm v.toFun 2 volume ≤ (H : ℝ≥0∞) := by
    calc
      eLpNorm v.toFun 2 volume =
          ENNReal.ofReal (eLpNorm v.toFun 2 volume).toReal :=
        (ENNReal.ofReal_toReal hvector.eLpNorm_ne_top).symm
      _ ≤ ENNReal.ofReal (H1Norm v.toFun) :=
        ENNReal.ofReal_le_ofReal (H1Norm_L2_le v.toFun)
      _ = (H : ℝ≥0∞) := by change ENNReal.ofReal (H : ℝ) = _; simp
  have hpartial : ∀ i j : Fin 3,
      eLpNorm (partialDerivative v.toFun i j) 2 volume ≤ (H : ℝ≥0∞) := by
    intro i j
    calc
      eLpNorm (partialDerivative v.toFun i j) 2 volume =
          ENNReal.ofReal (eLpNorm (partialDerivative v.toFun i j) 2 volume).toReal :=
        (ENNReal.ofReal_toReal (hderiv i j).eLpNorm_ne_top).symm
      _ ≤ ENNReal.ofReal (H1Norm v.toFun) :=
        ENNReal.ofReal_le_ofReal (H1Norm_partial_L2_le v.toFun i j)
      _ = (H : ℝ≥0∞) := by change ENNReal.ofReal (H : ℝ) = _; simp
  have hC2 : coordinateNormConstant ≤ componentH1L4Constant := by
    unfold componentH1L4Constant
    exact (le_add_of_nonneg_left (zero_le (1 : ℝ≥0))).trans
      (le_add_of_nonneg_right (zero_le _))
  have hC6 : C_Sobolev * coordinateNormConstant *
      (3 + spatialCutoffLipschitzConstant) ≤ componentH1L4Constant := by
    unfold componentH1L4Constant
    exact le_add_of_nonneg_left (zero_le _)
  have hcomponents : ∀ j : Fin 3, eLpNorm (fun x => v.toFun x j) 4 volume ≤
      ((componentH1L4Constant * H : ℝ≥0) : ℝ≥0∞) := by
    intro j
    have hs : ContDiff ℝ 1 (fun x => v.toFun x j) := by
      have hfun : (fun x => v.toFun x j) = (EuclideanSpace.proj j) ∘ v.toFun := by
        funext x
        exact (EuclideanSpace.proj_apply j (v.toFun x)).symm
      rw [hfun]
      exact (ContDiff.of_le (EuclideanSpace.proj j).contDiff le_top).comp
        (ContDiff.of_le v.smooth le_top)
    have hpoint : ∀ x, ‖v.toFun x j‖₊ ≤
        coordinateNormConstant * ‖v.toFun x‖₊ := by
      intro x
      apply NNReal.coe_le_coe.mp
      simp only [NNReal.coe_mul, coe_nnnorm]
      rw [← EuclideanSpace.proj_apply j (v.toFun x)]
      exact ((EuclideanSpace.proj j).le_opNorm (v.toFun x)).trans
        (mul_le_mul_of_nonneg_right (coordinate_projection_norm_le j)
          (norm_nonneg _))
    have hU2 : eLpNorm (fun x => v.toFun x j) 2 volume ≤
        (coordinateNormConstant : ℝ≥0∞) * (H : ℝ≥0∞) := by
      refine (eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
        (f := fun x => v.toFun x j) (g := v.toFun)
        (c := coordinateNormConstant)
        (Filter.Eventually.of_forall hpoint) 2).trans ?_
      rw [ENNReal.smul_def, smul_eq_mul]
      exact mul_le_mul_left' hV2 _
    have hU6 : eLpNorm (fun x => v.toFun x j) 6 volume ≤
        ((C_Sobolev * coordinateNormConstant *
          (3 + spatialCutoffLipschitzConstant) * H : ℝ≥0) : ℝ≥0∞) := by
      calc
        eLpNorm (fun x => v.toFun x j) 6 volume ≤
            (C_Sobolev : ℝ≥0∞) *
              (eLpNorm (fderiv ℝ (fun x => v.toFun x j)) 2 volume +
                (spatialCutoffLipschitzConstant : ℝ≥0∞) *
                  eLpNorm (fun x => v.toFun x j) 2 volume) :=
          H1_embedding_L6_noncompact hs
        _ ≤ (C_Sobolev : ℝ≥0∞) *
            ((3 : ℝ≥0∞) * (coordinateNormConstant : ℝ≥0∞) * (H : ℝ≥0∞) +
              (spatialCutoffLipschitzConstant : ℝ≥0∞) *
                ((coordinateNormConstant : ℝ≥0∞) * (H : ℝ≥0∞))) :=
          mul_le_mul_left'
            (add_le_add (component_fderiv_L2_bound v hderiv H hpartial j)
              (mul_le_mul_left' hU2 _)) _
        _ = _ := by
          simp only [ENNReal.coe_mul, ENNReal.coe_add, ENNReal.coe_ofNat]
          rw [mul_assoc (3 : ℝ≥0∞), ← add_mul,
            ← mul_assoc ((3 : ℝ≥0∞) + (spatialCutoffLipschitzConstant : ℝ≥0∞)),
            mul_comm ((3 : ℝ≥0∞) + (spatialCutoffLipschitzConstant : ℝ≥0∞))
              (coordinateNormConstant : ℝ≥0∞),
            ← mul_assoc (C_Sobolev : ℝ≥0∞), ← mul_assoc (C_Sobolev : ℝ≥0∞)]
    apply L4_bound_of_L2_L6 hs.continuous.aestronglyMeasurable
    · exact hU2.trans (by
        simpa only [ENNReal.coe_mul] using
          mul_le_mul_right' (ENNReal.coe_le_coe.2 hC2) (H : ℝ≥0∞))
    · exact hU6.trans (by
        exact ENNReal.coe_le_coe.2 (mul_le_mul_right' hC6 H))
  have hsum :
      eLpNorm (fun x => ∑ j : Fin 3, ‖v.toFun x j‖) 4 volume ≤
        ∑ j : Fin 3, eLpNorm (fun x => v.toFun x j) 4 volume := by
    simpa only [Finset.sum_fn, Finset.sum_apply, eLpNorm_norm] using
      (eLpNorm_sum_le (s := Finset.univ)
        (f := fun j : Fin 3 => fun x : R3 => ‖v.toFun x j‖)
        (fun j _ => (v.component_L2 j).aestronglyMeasurable.norm)
        (by norm_num : 1 ≤ (4 : ℝ≥0∞)))
  calc
    eLpNorm v.toFun 4 volume ≤ eLpNorm (fun x => ∑ j : Fin 3, ‖v.toFun x j‖) 4 volume :=
      eLpNorm_mono_ae_real (Filter.Eventually.of_forall fun x =>
        euclidean_norm_le_sum_coordinates (v.toFun x))
    _ ≤ ∑ j : Fin 3, eLpNorm (fun x => v.toFun x j) 4 volume := hsum
    _ ≤ ∑ _ : Fin 3, ((componentH1L4Constant * H : ℝ≥0) : ℝ≥0∞) :=
      Finset.sum_le_sum fun j _ => hcomponents j
    _ = (((3 : ℝ≥0) * componentH1L4Constant * H : ℝ≥0) : ℝ≥0∞) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, ENNReal.coe_mul, ENNReal.coe_ofNat, Nat.cast_ofNat, mul_assoc]
    _ = ENNReal.ofReal (H1L4Constant * H1Norm v.toFun) := by
      change (((3 : ℝ≥0) * componentH1L4Constant * H : ℝ≥0) : ℝ≥0∞) =
        ENNReal.ofReal (((3 : ℝ≥0) * componentH1L4Constant * H : ℝ≥0) : ℝ)
      simp only [ENNReal.ofReal_coe_nnreal]

/-- Actual L4 membership follows from the extended-real finite bound. -/
theorem H1_embedding_L4_mem (v : TestVectorField)
    (hderiv : ∀ i j : Fin 3,
      Memℒp (partialDerivative v.toFun i j) 2 (volume : Measure R3)) :
    Memℒp v.toFun 4 (volume : Measure R3) :=
  ⟨v.smooth.continuous.aestronglyMeasurable,
    (H1_embedding_L4_extended v hderiv).trans_lt ENNReal.ofReal_lt_top⟩

/-- The real norm bound, converted only after an extended-real finite bound. -/
theorem H1_embedding_L4_bound (v : TestVectorField)
    (hderiv : ∀ i j : Fin 3,
      Memℒp (partialDerivative v.toFun i j) 2 (volume : Measure R3)) :
    eLpNorm_L4 (fun x : R3 => ‖v.toFun x‖) ≤ H1L4Constant * H1Norm v.toFun := by
  have hnonneg : 0 ≤ H1L4Constant * H1Norm v.toFun :=
    mul_nonneg (NNReal.coe_nonneg ((3 : ℝ≥0) * componentH1L4Constant)) (Real.sqrt_nonneg _)
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (H1_embedding_L4_extended v hderiv)
  rw [ENNReal.toReal_ofReal hnonneg] at h
  simpa only [eLpNorm_L4, eLpNorm_norm] using h

/-- The formerly OPEN noncompact vector H1 → L4 statement, with its original
smoothness and finite coordinate-derivative interface preserved. Compact
cutoffs and Fatou are constructed above; no H1 mollifier-density hypothesis
is added. Compilation and a Lean kernel dependency audit remain unverified. -/
theorem H1_embedding_L4 :
  ∃ C : ℝ, ∀ v : TestVectorField,
    (∀ i j : Fin 3,
      Memℒp (partialDerivative v.toFun i j) 2 (volume : Measure R3)) →
    eLpNorm_L4 (fun x : R3 => ‖v.toFun x‖) ≤ C * H1Norm v.toFun := by
  exact ⟨H1L4Constant, H1_embedding_L4_bound⟩

/-- The 4-4-2 Holder inequality for scalar functions
on R3. Its exponents satisfy 1/4 + 1/4 + 1/2 = 1.
Mathlib v4.12.0 supplies eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm with
AEStronglyMeasurable hypotheses. The proof applies it first with
(p,q,r) = (2,4,4), then with (p,q,r) = (1,2,2).
The finiteness hypotheses are retained for the requested analytic interface;
the extended-real inequality itself does not need them. -/
theorem holder_4442 (f g h : R3 → ℝ)
    (hf : AEStronglyMeasurable f volume)
    (hg : AEStronglyMeasurable g volume)
    (hh : AEStronglyMeasurable h volume)
    (hf4 : eLpNorm f 4 volume ≠ ⊤)
    (hg4 : eLpNorm g 4 volume ≠ ⊤)
    (hh2 : eLpNorm h 2 volume ≠ ⊤) :
    eLpNorm (fun x => f x * g x * h x) 1 volume ≤
      eLpNorm f 4 volume * eLpNorm g 4 volume * eLpNorm h 2 volume := by
  -- Hölder: L4 × L4 → L2, then L2 × L2 → L1.
  have h_fg_L2 :
      eLpNorm (fun x => f x * g x) 2 volume ≤
        eLpNorm f 4 volume * eLpNorm g 4 volume := by
    refine eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm
      hf hg (fun a b : ℝ => a * b) ?_ ?_
    · exact Filter.Eventually.of_forall
        (fun x => le_of_eq (nnnorm_mul (f x) (g x)))
    · exact ennreal_holder_div_244
  calc
    eLpNorm (fun x => f x * g x * h x) 1 volume
        ≤ eLpNorm (fun x => f x * g x) 2 volume * eLpNorm h 2 volume := by
          refine eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm
            (hf.mul hg) hh (fun a b : ℝ => a * b) ?_ ?_
          · exact Filter.Eventually.of_forall
              (fun x => le_of_eq (nnnorm_mul (f x * g x) (h x)))
          · exact ennreal_holder_div_122
    _ ≤ eLpNorm f 4 volume * eLpNorm g 4 volume * eLpNorm h 2 volume :=
      mul_le_mul_right' h_fg_L2 _


/-- Coordinate derivative of a scalar, the same classical `deriv` as
`partialDerivative` on a component. -/
noncomputable def partialScalar (f : R3 → ℝ) (i : Fin 3) : R3 → ℝ :=
  fun x => deriv (fun t : ℝ => f (x + t • EuclideanSpace.single i 1)) 0

/-- Second coordinate derivative: differentiate component `j` in direction `i`,
then in direction `k`. -/
noncomputable def partialOrder2 (v : R3 → R3) (k i j : Fin 3) : R3 → ℝ :=
  partialScalar (partialDerivative v i j) k

/-- Third coordinate derivative. -/
noncomputable def partialOrder3 (v : R3 → R3) (a k i j : Fin 3) : R3 → ℝ :=
  partialScalar (partialOrder2 v k i j) a

/-- Fourth coordinate derivative. -/
noncomputable def partialOrder4 (v : R3 → R3) (b a k i j : Fin 3) : R3 → ℝ :=
  partialScalar (partialOrder3 v a k i j) b

/-- The squared L² energy inside the preserved square-root `H1Norm`. -/
noncomputable def gradL2Energy (v : R3 → R3) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    (eLpNorm (partialDerivative v i j) 2 (volume : Measure R3)).toReal ^ 2

noncomputable def H1Energy (v : R3 → R3) : ℝ :=
  (eLpNorm v 2 (volume : Measure R3)).toReal ^ 2 + gradL2Energy v

/-- Squared L² energies of ordered derivatives of length 2, 3, and 4.
Mixed partials are counted once per differentiation order. Every term is a
square of an extended-real L² norm converted by `.toReal`. -/
noncomputable def H4RestEnergy (v : R3 → R3) : ℝ :=
  (∑ j : Fin 3, ∑ i : Fin 3, ∑ k : Fin 3,
      (eLpNorm (partialOrder2 v k i j) 2 (volume : Measure R3)).toReal ^ 2) +
    (∑ j : Fin 3, ∑ i : Fin 3, ∑ k : Fin 3, ∑ a : Fin 3,
      (eLpNorm (partialOrder3 v a k i j) 2 (volume : Measure R3)).toReal ^ 2) +
    ∑ j : Fin 3, ∑ i : Fin 3, ∑ k : Fin 3, ∑ a : Fin 3, ∑ b : Fin 3,
      (eLpNorm (partialOrder4 v b a k i j) 2 (volume : Measure R3)).toReal ^ 2

/-- `‖u‖₂² + ∑_{1 ≤ |α| ≤ 4} ‖D^α u‖₂²`, with `|α| ≤ 1` exactly `H1Energy`
and `|α| ≥ 2` the ordered coordinate derivatives. `.toReal` sends an infinite
extended norm to zero, as it does for `H1Norm`. -/
noncomputable def H4Energy (v : R3 → R3) : ℝ :=
  H1Energy v + H4RestEnergy v

/-- Square-root H⁴ quantity. `H1Norm ≤ H4Norm` because `H1Energy` is the
`|α| ≤ 1` part of `H4Energy` and the remaining terms are nonnegative. -/
noncomputable def H4Norm (v : R3 → R3) : ℝ :=
  Real.sqrt (H4Energy v)

/-- Real L² norm. `.toReal` sends infinity to zero, so bounds that use it
require `Memℒp`. -/
noncomputable def L2Norm (v : R3 → R3) : ℝ :=
  (eLpNorm v 2 (volume : Measure R3)).toReal

/-- `‖∇v‖_L2 = sqrt(∑_{i,j} ‖∂_i v_j‖_L2²)`, the gradient part of `H1Norm`. -/
noncomputable def gradL2Norm (v : R3 → R3) : ℝ :=
  Real.sqrt (gradL2Energy v)

/-- Scalar L⁴ constant used inside the proof that first derivatives lie in L⁴.
It is not part of the public estimate: that estimate uses `H1L4Constant`. -/
private noncomputable def partialL4Constant : ℝ≥0 :=
  1 + C_Sobolev * (3 * coordinateNormConstant + spatialCutoffLipschitzConstant)

/-- Analytic constant for `|b(u,v,w)|`. Nine coordinate pairs, and both `u` and
`∇v` are estimated in L⁴ by the constant from `H1_embedding_L4_bound`. -/
noncomputable def C_trilinear : ℝ :=
  (9 : ℝ) * H1L4Constant * H1L4Constant

private theorem H1Energy_nonneg (v : R3 → R3) : 0 ≤ H1Energy v := by
  unfold H1Energy gradL2Energy
  exact add_nonneg (sq_nonneg _)
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)

private theorem H4RestEnergy_nonneg (v : R3 → R3) : 0 ≤ H4RestEnergy v := by
  unfold H4RestEnergy
  refine add_nonneg (add_nonneg ?_ ?_) ?_
  · exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => sq_nonneg _
  · exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  · exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
        Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem H1Norm_eq_sqrt_H1Energy (v : R3 → R3) :
    H1Norm v = Real.sqrt (H1Energy v) := by
  unfold H1Norm H1Energy gradL2Energy
  rfl

/-- `‖u‖_L2 ≤ H4Norm u`. The order-zero term of `H4Energy` is `‖u‖_L2²`. -/
theorem H4_controls_L2 (v : R3 → R3) :
    (eLpNorm v 2 (volume : Measure R3)).toReal ≤ H4Norm v :=
  (H1Norm_L2_le v).trans <| by
    rw [H1Norm_eq_sqrt_H1Energy, H4Norm]
    exact Real.sqrt_le_sqrt (le_add_of_nonneg_right (H4RestEnergy_nonneg v))

/-- `H1Norm ≤ H4Norm`. The H¹ sum is the `|α| ≤ 1` part of the H⁴ sum. -/
theorem H4_controls_H1 (v : R3 → R3) : H1Norm v ≤ H4Norm v := by
  rw [H1Norm_eq_sqrt_H1Energy, H4Norm]
  exact Real.sqrt_le_sqrt (le_add_of_nonneg_right (H4RestEnergy_nonneg v))

theorem gradL2Norm_le_H1Norm (v : R3 → R3) : gradL2Norm v ≤ H1Norm v := by
  rw [H1Norm_eq_sqrt_H1Energy]
  unfold gradL2Norm H1Energy
  exact Real.sqrt_le_sqrt (le_add_of_nonneg_left (sq_nonneg _))

/-- `‖∇u‖_L2 ≤ H4Norm u`, through `‖∇u‖_L2 ≤ H1Norm u ≤ H4Norm u`. -/
theorem H4_controls_grad_L2 (v : R3 → R3) : gradL2Norm v ≤ H4Norm v :=
  (gradL2Norm_le_H1Norm v).trans (H4_controls_H1 v)

/-- `‖u‖_L4 ≤ H1L4Constant * H4Norm u` for a smooth vector field whose first
coordinate derivatives lie in L². The constant is the one proved for
`H1Norm` in `H1_embedding_L4_bound`, not the compact-support factor `C_GN`:
that factor is not an upper bound for the noncompact estimate. -/
theorem H4_controls_L4 (v : TestVectorField)
    (hderiv : ∀ i j : Fin 3,
      Memℒp (partialDerivative v.toFun i j) 2 (volume : Measure R3)) :
    eLpNorm_L4 (fun x : R3 => ‖v.toFun x‖) ≤ H1L4Constant * H4Norm v.toFun := by
  have hC : 0 ≤ H1L4Constant := by
    unfold H1L4Constant
    exact NNReal.coe_nonneg _
  exact (H1_embedding_L4_bound v hderiv).trans
    (mul_le_mul_of_nonneg_left (H4_controls_H1 v.toFun) hC)

private theorem component_norm_le (z : R3) (j : Fin 3) : ‖z j‖ ≤ ‖z‖ := by
  have hsq : ‖z j‖ ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => ℝ) z]
    exact Finset.single_le_sum
      (f := fun i : Fin 3 => ‖z i‖ ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  have hsqrt := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at hsqrt

private theorem partialScalar_eq_fderiv {f : R3 → ℝ} (i : Fin 3) (x : R3)
    (hf : DifferentiableAt ℝ f x) :
    partialScalar f i x = fderiv ℝ f x (EuclideanSpace.single i 1) := by
  have hline : HasDerivAt
      (fun t : ℝ => x + t • EuclideanSpace.single i 1)
      (EuclideanSpace.single i 1) 0 := by
    simpa only [zero_add, one_smul] using
      (hasDerivAt_const (0 : ℝ) x).add
        ((hasDerivAt_id' (0 : ℝ)).smul_const (EuclideanSpace.single i 1))
  have h := hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline
    (by simp only [zero_smul, add_zero])
  simpa only [partialScalar, Function.comp_def] using h.deriv

private theorem partialScalar_contDiff {f : R3 → ℝ} (hf : ContDiff ℝ ⊤ f) (i : Fin 3) :
    ContDiff ℝ ⊤ (partialScalar f i) := by
  have hmn : (⊤ : ℕ∞) + 1 ≤ ⊤ := le_top
  have hpair : ContDiff ℝ ⊤
      (fun p : R3 × R3 => (fderiv ℝ f p.1 : R3 →L[ℝ] ℝ) p.2) :=
    hf.contDiff_fderiv_apply hmn
  have hproj : ContDiff ℝ ⊤ (fun x : R3 => (x, EuclideanSpace.single i (1 : ℝ))) :=
    contDiff_id.prod contDiff_const
  have heq : partialScalar f i =
      fun x => fderiv ℝ f x (EuclideanSpace.single i 1) := by
    funext x
    exact partialScalar_eq_fderiv i x
      (hf.differentiable (le_top : (1 : ℕ∞) ≤ ⊤)).differentiableAt
  rw [heq]
  exact hpair.comp hproj

private theorem component_contDiff (v : TestVectorField) (j : Fin 3) :
    ContDiff ℝ ⊤ (fun x => v.toFun x j) := by
  have hfun : (fun x => v.toFun x j) = (EuclideanSpace.proj j) ∘ v.toFun := by
    funext x
    exact (EuclideanSpace.proj_apply j (v.toFun x)).symm
  rw [hfun]
  exact (EuclideanSpace.proj j).contDiff.comp v.smooth

private theorem partialDerivative_contDiff (v : TestVectorField) (i j : Fin 3) :
    ContDiff ℝ ⊤ (partialDerivative v.toFun i j) := by
  have h : partialDerivative v.toFun i j =
      partialScalar (fun x => v.toFun x j) i := rfl
  rw [h]
  exact partialScalar_contDiff (component_contDiff v j) i

private theorem secondPartial_sq_le_rest (v : R3 → R3) (k i j : Fin 3) :
    (eLpNorm (partialOrder2 v k i j) 2 (volume : Measure R3)).toReal ^ 2 ≤
      H4RestEnergy v := by
  -- `H4RestEnergy` stores `∑ j, ∑ i, ∑ k`. Peel those indices in that order.
  have hk :
      (eLpNorm (partialOrder2 v k i j) 2 (volume : Measure R3)).toReal ^ 2 ≤
        ∑ k' : Fin 3,
          (eLpNorm (partialOrder2 v k' i j) 2 (volume : Measure R3)).toReal ^ 2 :=
    Finset.single_le_sum
      (f := fun k' : Fin 3 =>
        (eLpNorm (partialOrder2 v k' i j) 2 (volume : Measure R3)).toReal ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ k)
  have hi :
      (∑ k' : Fin 3,
          (eLpNorm (partialOrder2 v k' i j) 2 (volume : Measure R3)).toReal ^ 2) ≤
        ∑ i' : Fin 3, ∑ k' : Fin 3,
          (eLpNorm (partialOrder2 v k' i' j) 2 (volume : Measure R3)).toReal ^ 2 :=
    Finset.single_le_sum
      (f := fun i' : Fin 3 => ∑ k' : Fin 3,
        (eLpNorm (partialOrder2 v k' i' j) 2 (volume : Measure R3)).toReal ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  have hj :
      (∑ i' : Fin 3, ∑ k' : Fin 3,
          (eLpNorm (partialOrder2 v k' i' j) 2 (volume : Measure R3)).toReal ^ 2) ≤
        ∑ j' : Fin 3, ∑ i' : Fin 3, ∑ k' : Fin 3,
          (eLpNorm (partialOrder2 v k' i' j') 2 (volume : Measure R3)).toReal ^ 2 :=
    Finset.single_le_sum
      (f := fun j' : Fin 3 => ∑ i' : Fin 3, ∑ k' : Fin 3,
        (eLpNorm (partialOrder2 v k' i' j') 2 (volume : Measure R3)).toReal ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
      (Finset.mem_univ j)
  refine (hk.trans (hi.trans hj)).trans ?_
  unfold H4RestEnergy
  exact (le_add_of_nonneg_right
      (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
        Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)).trans
    (le_add_of_nonneg_right
      (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
        Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
          Finset.sum_nonneg fun _ _ => sq_nonneg _))

private theorem secondPartial_L2_real_le_H4 (v : R3 → R3) (k i j : Fin 3) :
    (eLpNorm (partialOrder2 v k i j) 2 (volume : Measure R3)).toReal ≤ H4Norm v := by
  rw [H4Norm]
  apply Real.le_sqrt_of_sq_le
  exact (secondPartial_sq_le_rest v k i j).trans
    (le_add_of_nonneg_left (H1Energy_nonneg v))

private theorem coordinateNormConstant_ge_one : (1 : ℝ≥0) ≤ coordinateNormConstant := by
  unfold coordinateNormConstant
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => zero_le _)

private theorem partialL4Constant_le_H1L4Constant :
    (partialL4Constant : ℝ) ≤ H1L4Constant := by
  have hcoord := coordinateNormConstant_ge_one
  have hLip : spatialCutoffLipschitzConstant ≤
      coordinateNormConstant * spatialCutoffLipschitzConstant := by
    have h := mul_le_mul_of_nonneg_right hcoord (zero_le spatialCutoffLipschitzConstant)
    simpa using h
  have hsum : 3 * coordinateNormConstant + spatialCutoffLipschitzConstant ≤
      coordinateNormConstant * (3 + spatialCutoffLipschitzConstant) := by
    have hmul : coordinateNormConstant * (3 + spatialCutoffLipschitzConstant) =
        3 * coordinateNormConstant + coordinateNormConstant * spatialCutoffLipschitzConstant := by
      rw [mul_add, mul_comm coordinateNormConstant (3 : ℝ≥0)]
    rw [hmul]
    exact add_le_add_left hLip _
  have hfac : C_Sobolev * (3 * coordinateNormConstant + spatialCutoffLipschitzConstant) ≤
      C_Sobolev * coordinateNormConstant * (3 + spatialCutoffLipschitzConstant) := by
    have h := mul_le_mul_of_nonneg_left hsum (zero_le C_Sobolev)
    -- `C * (coord * (3 + Lip)) = (C * coord) * (3 + Lip)`.
    simpa [mul_assoc] using h
  have hcomp : partialL4Constant ≤ componentH1L4Constant := by
    unfold partialL4Constant componentH1L4Constant
    calc
      1 + C_Sobolev * (3 * coordinateNormConstant + spatialCutoffLipschitzConstant)
          ≤ 1 + C_Sobolev * coordinateNormConstant * (3 + spatialCutoffLipschitzConstant) :=
        add_le_add_left hfac _
      _ ≤ 1 + coordinateNormConstant +
            C_Sobolev * coordinateNormConstant * (3 + spatialCutoffLipschitzConstant) :=
        add_le_add_right (le_add_of_nonneg_right (zero_le coordinateNormConstant)) _
  have hone : (1 : ℝ≥0) ≤ 3 := by norm_num
  have h3 : componentH1L4Constant ≤ (3 : ℝ≥0) * componentH1L4Constant := by
    simpa using mul_le_mul_of_nonneg_right hone (zero_le componentH1L4Constant)
  have hle : partialL4Constant ≤ (3 : ℝ≥0) * componentH1L4Constant := hcomp.trans h3
  have hcoe : (partialL4Constant : ℝ) ≤ (((3 : ℝ≥0) * componentH1L4Constant : ℝ≥0) : ℝ) :=
    NNReal.coe_le_coe.mpr hle
  simpa only [H1L4Constant] using hcoe

private theorem scalar_fderiv_L2_bound {f : R3 → ℝ} (hf : ContDiff ℝ ⊤ f)
    (hderiv : ∀ i : Fin 3, Memℒp (partialScalar f i) 2 (volume : Measure R3))
    (H : ℝ≥0∞)
    (hpartial : ∀ i : Fin 3, eLpNorm (partialScalar f i) 2 (volume : Measure R3) ≤ H) :
    eLpNorm (fderiv ℝ f) 2 (volume : Measure R3) ≤
      (3 : ℝ≥0∞) * (coordinateNormConstant : ℝ≥0∞) * H := by
  have hbound : ∀ x, ‖fderiv ℝ f x‖ ≤
      (coordinateNormConstant : ℝ) * ‖∑ i : Fin 3, ‖partialScalar f i x‖‖ := by
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)]
    have h := scalar_operator_norm_le_coordinates (fderiv ℝ f x)
    have heq : ∀ i : Fin 3,
        fderiv ℝ f x (EuclideanSpace.single i 1) = partialScalar f i x :=
      fun i => (partialScalar_eq_fderiv i x
        (hf.differentiable (le_top : (1 : ℕ∞) ≤ ⊤)).differentiableAt).symm
    simpa only [heq] using h
  have hsum : eLpNorm (fun x => ∑ i : Fin 3, ‖partialScalar f i x‖) 2 volume ≤
      ∑ i : Fin 3, eLpNorm (partialScalar f i) 2 volume := by
    simpa only [Finset.sum_fn, Finset.sum_apply, eLpNorm_norm] using
      (eLpNorm_sum_le (s := Finset.univ)
        (f := fun i : Fin 3 => fun x : R3 => ‖partialScalar f i x‖)
        (fun i _ => (hderiv i).aestronglyMeasurable.norm)
        (by norm_num : 1 ≤ (2 : ℝ≥0∞)))
  calc
    eLpNorm (fderiv ℝ f) 2 volume ≤
        ENNReal.ofReal (coordinateNormConstant : ℝ) *
          eLpNorm (fun x => ∑ i : Fin 3, ‖partialScalar f i x‖) 2 volume :=
      eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Filter.Eventually.of_forall hbound) _
    _ ≤ ENNReal.ofReal (coordinateNormConstant : ℝ) *
          ∑ i : Fin 3, eLpNorm (partialScalar f i) 2 volume :=
      mul_le_mul_left' hsum _
    _ ≤ ENNReal.ofReal (coordinateNormConstant : ℝ) * ∑ _ : Fin 3, H :=
      mul_le_mul_left' (Finset.sum_le_sum fun i _ => hpartial i) _
    _ = (3 : ℝ≥0∞) * (coordinateNormConstant : ℝ≥0∞) * H := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        ENNReal.ofReal_coe_nnreal]
      rw [mul_left_comm, mul_assoc, Nat.cast_ofNat]

private theorem partialDerivative_L4_extended (v : TestVectorField) (i j : Fin 3)
    (hv1 : Memℒp (partialDerivative v.toFun i j) 2 (volume : Measure R3))
    (hv2 : ∀ k : Fin 3,
      Memℒp (partialOrder2 v.toFun k i j) 2 (volume : Measure R3)) :
    eLpNorm (partialDerivative v.toFun i j) 4 (volume : Measure R3) ≤
      ((partialL4Constant * ⟨H4Norm v.toFun, Real.sqrt_nonneg _⟩ : ℝ≥0) : ℝ≥0∞) := by
  let f : R3 → ℝ := partialDerivative v.toFun i j
  let Hnn : ℝ≥0 := ⟨H4Norm v.toFun, Real.sqrt_nonneg _⟩
  have hfC : ContDiff ℝ ⊤ f := partialDerivative_contDiff v i j
  have h2real : (eLpNorm f 2 (volume : Measure R3)).toReal ≤ H4Norm v.toFun :=
    (H1Norm_partial_L2_le v.toFun i j).trans (H4_controls_H1 v.toFun)
  have h2 : eLpNorm f 2 volume ≤ (Hnn : ℝ≥0∞) := by
    calc
      eLpNorm f 2 volume = ENNReal.ofReal (eLpNorm f 2 volume).toReal :=
        (ENNReal.ofReal_toReal hv1.eLpNorm_ne_top).symm
      _ ≤ ENNReal.ofReal (H4Norm v.toFun) := ENNReal.ofReal_le_ofReal h2real
      _ = (Hnn : ℝ≥0∞) := by change ENNReal.ofReal (Hnn : ℝ) = _; simp
  have hsec : ∀ k : Fin 3, eLpNorm (partialScalar f k) 2 volume ≤ (Hnn : ℝ≥0∞) := by
    intro k
    have hreal := secondPartial_L2_real_le_H4 v.toFun k i j
    calc
      eLpNorm (partialScalar f k) 2 volume =
          ENNReal.ofReal (eLpNorm (partialOrder2 v.toFun k i j) 2 volume).toReal := by
        rw [show partialScalar f k = partialOrder2 v.toFun k i j from rfl,
          ENNReal.ofReal_toReal (hv2 k).eLpNorm_ne_top]
      _ ≤ ENNReal.ofReal (H4Norm v.toFun) := ENNReal.ofReal_le_ofReal hreal
      _ = (Hnn : ℝ≥0∞) := by change ENNReal.ofReal (Hnn : ℝ) = _; simp
  have hfderiv : eLpNorm (fderiv ℝ f) 2 volume ≤
      (3 : ℝ≥0∞) * (coordinateNormConstant : ℝ≥0∞) * (Hnn : ℝ≥0∞) :=
    scalar_fderiv_L2_bound hfC hv2 (Hnn : ℝ≥0∞) hsec
  have h6 : eLpNorm f 6 volume ≤
      ((C_Sobolev * (3 * coordinateNormConstant + spatialCutoffLipschitzConstant) *
          Hnn : ℝ≥0) : ℝ≥0∞) := by
    have hs1 : ContDiff ℝ 1 f := hfC.of_le (le_top : (1 : ℕ∞) ≤ ⊤)
    calc
      eLpNorm f 6 volume ≤ (C_Sobolev : ℝ≥0∞) *
          (eLpNorm (fderiv ℝ f) 2 volume +
            (spatialCutoffLipschitzConstant : ℝ≥0∞) * eLpNorm f 2 volume) :=
        H1_embedding_L6_noncompact hs1
      _ ≤ (C_Sobolev : ℝ≥0∞) *
          ((3 : ℝ≥0∞) * (coordinateNormConstant : ℝ≥0∞) * (Hnn : ℝ≥0∞) +
            (spatialCutoffLipschitzConstant : ℝ≥0∞) * (Hnn : ℝ≥0∞)) :=
        mul_le_mul_left' (add_le_add hfderiv (mul_le_mul_left' h2 _)) _
      _ = _ := by
        have hdist :
            (3 : ℝ≥0∞) * (coordinateNormConstant : ℝ≥0∞) * (Hnn : ℝ≥0∞) +
              (spatialCutoffLipschitzConstant : ℝ≥0∞) * (Hnn : ℝ≥0∞) =
            ((3 * coordinateNormConstant + spatialCutoffLipschitzConstant : ℝ≥0) : ℝ≥0∞) *
              (Hnn : ℝ≥0∞) := by
          simp only [ENNReal.coe_add, ENNReal.coe_mul, ENNReal.coe_ofNat, add_mul]
        rw [hdist, mul_assoc]
        simp only [ENNReal.coe_mul]
  have h2M : eLpNorm f 2 volume ≤ ((partialL4Constant * Hnn : ℝ≥0) : ℝ≥0∞) := by
    have hone : (1 : ℝ≥0) ≤ partialL4Constant := by
      unfold partialL4Constant
      exact le_add_of_nonneg_right (zero_le _)
    calc
      eLpNorm f 2 volume ≤ (Hnn : ℝ≥0∞) := h2
      _ = ((1 : ℝ≥0) : ℝ≥0∞) * (Hnn : ℝ≥0∞) := by simp
      _ ≤ (partialL4Constant : ℝ≥0∞) * (Hnn : ℝ≥0∞) :=
        mul_le_mul_right' (ENNReal.coe_le_coe.2 hone) _
      _ = ((partialL4Constant * Hnn : ℝ≥0) : ℝ≥0∞) := by simp [ENNReal.coe_mul]
  have h6M : eLpNorm f 6 volume ≤ ((partialL4Constant * Hnn : ℝ≥0) : ℝ≥0∞) := by
    have hfac : C_Sobolev * (3 * coordinateNormConstant + spatialCutoffLipschitzConstant) ≤
        partialL4Constant := by
      unfold partialL4Constant
      exact le_add_of_nonneg_left (zero_le _)
    exact h6.trans <| by
      simpa only [ENNReal.coe_mul] using
        mul_le_mul_right' (ENNReal.coe_le_coe.2 hfac) (Hnn : ℝ≥0∞)
  exact L4_bound_of_L2_L6 hfC.continuous.aestronglyMeasurable _ h2M h6M

private theorem partialDerivative_L4_ne_top (v : TestVectorField) (i j : Fin 3)
    (hv1 : Memℒp (partialDerivative v.toFun i j) 2 (volume : Measure R3))
    (hv2 : ∀ k : Fin 3,
      Memℒp (partialOrder2 v.toFun k i j) 2 (volume : Measure R3)) :
    eLpNorm (partialDerivative v.toFun i j) 4 (volume : Measure R3) ≠ ⊤ :=
  ne_of_lt <| (partialDerivative_L4_extended v i j hv1 hv2).trans_lt <|
    lt_top_iff_ne_top.mpr ENNReal.coe_ne_top

private theorem partialDerivative_L4_real_le (v : TestVectorField) (i j : Fin 3)
    (hv1 : Memℒp (partialDerivative v.toFun i j) 2 (volume : Measure R3))
    (hv2 : ∀ k : Fin 3,
      Memℒp (partialOrder2 v.toFun k i j) 2 (volume : Measure R3)) :
    (eLpNorm (partialDerivative v.toFun i j) 4 (volume : Measure R3)).toReal ≤
      H1L4Constant * H4Norm v.toFun := by
  have h4 := partialDerivative_L4_extended v i j hv1 hv2
  have hnonneg : 0 ≤ (partialL4Constant : ℝ) * H4Norm v.toFun :=
    mul_nonneg (NNReal.coe_nonneg _) (Real.sqrt_nonneg _)
  have hreal : (eLpNorm (partialDerivative v.toFun i j) 4 volume).toReal ≤
      (partialL4Constant : ℝ) * H4Norm v.toFun := by
    have hle : eLpNorm (partialDerivative v.toFun i j) 4 volume ≤
        ENNReal.ofReal ((partialL4Constant : ℝ) * H4Norm v.toFun) := by
      refine h4.trans (le_of_eq ?_)
      rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_mul]
      rfl
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    rwa [ENNReal.toReal_ofReal hnonneg] at h
  exact hreal.trans <|
    mul_le_mul_of_nonneg_right partialL4Constant_le_H1L4Constant (Real.sqrt_nonneg _)

private theorem component_L4_real_le (u : TestVectorField)
    (hu : ∀ i j : Fin 3,
      Memℒp (partialDerivative u.toFun i j) 2 (volume : Measure R3))
    (j : Fin 3) :
    (eLpNorm (fun x => u.toFun x j) 4 (volume : Measure R3)).toReal ≤
      H1L4Constant * H4Norm u.toFun := by
  have hC : 0 ≤ H1L4Constant := by
    unfold H1L4Constant
    exact NNReal.coe_nonneg _
  have hvec : eLpNorm u.toFun 4 volume ≤
      ENNReal.ofReal (H1L4Constant * H4Norm u.toFun) :=
    (H1_embedding_L4_extended u hu).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (H4_controls_H1 u.toFun) hC))
  have hmono : eLpNorm (fun x => u.toFun x j) 4 volume ≤ eLpNorm u.toFun 4 volume :=
    eLpNorm_mono fun x => component_norm_le (u.toFun x) j
  have hle : eLpNorm (fun x => u.toFun x j) 4 volume ≤
      ENNReal.ofReal (H1L4Constant * H4Norm u.toFun) :=
    hmono.trans hvec
  have hH : 0 ≤ H4Norm u.toFun := by
    rw [H4Norm]
    exact Real.sqrt_nonneg _
  have hnonneg : 0 ≤ H1L4Constant * H4Norm u.toFun :=
    mul_nonneg (by unfold H1L4Constant; exact NNReal.coe_nonneg _) hH
  have hto := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
  rwa [ENNReal.toReal_ofReal hnonneg] at hto

private theorem component_L2_real_le {w : R3 → R3}
    (hw : Memℒp w 2 (volume : Measure R3)) (j : Fin 3) :
    (eLpNorm (fun x => w x j) 2 (volume : Measure R3)).toReal ≤ L2Norm w := by
  have hmono : eLpNorm (fun x => w x j) 2 volume ≤ eLpNorm w 2 volume :=
    eLpNorm_mono fun x => component_norm_le (w x) j
  simpa [L2Norm] using ENNReal.toReal_mono hw.eLpNorm_ne_top hmono

private theorem product_integrable (u v : TestVectorField) (w : R3 → R3)
    (hu : ∀ i j : Fin 3,
      Memℒp (partialDerivative u.toFun i j) 2 (volume : Measure R3))
    (hv1 : ∀ i j : Fin 3,
      Memℒp (partialDerivative v.toFun i j) 2 (volume : Measure R3))
    (hv2 : ∀ k i j : Fin 3,
      Memℒp (partialOrder2 v.toFun k i j) 2 (volume : Measure R3))
    (hw : Memℒp w 2 (volume : Measure R3)) (i j : Fin 3) :
    Integrable (fun x => (u.toFun x) i * partialDerivative v.toFun i j x * (w x) j)
      (volume : Measure R3) := by
  let f : R3 → ℝ := fun x => u.toFun x i
  let g : R3 → ℝ := partialDerivative v.toFun i j
  let h : R3 → ℝ := fun x => w x j
  have hfmeas : AEStronglyMeasurable f volume :=
    ((EuclideanSpace.proj i).continuous.comp u.smooth.continuous).aestronglyMeasurable
  have hgmeas : AEStronglyMeasurable g volume :=
    (partialDerivative_contDiff v i j).continuous.aestronglyMeasurable
  have hhmeas : AEStronglyMeasurable h volume :=
    (EuclideanSpace.proj j).continuous.comp_aestronglyMeasurable hw.aestronglyMeasurable
  have hf4 : eLpNorm f 4 volume ≠ ⊤ :=
    ((H1_embedding_L4_mem u hu).of_le hfmeas
      (Filter.Eventually.of_forall fun x => component_norm_le (u.toFun x) i)).eLpNorm_ne_top
  have hg4 : eLpNorm g 4 volume ≠ ⊤ :=
    partialDerivative_L4_ne_top v i j (hv1 i j) (fun k => hv2 k i j)
  have hh2 : eLpNorm h 2 volume ≠ ⊤ :=
    (hw.of_le hhmeas
      (Filter.Eventually.of_forall fun x => component_norm_le (w x) j)).eLpNorm_ne_top
  have hholder := holder_4442 f g h hfmeas hgmeas hhmeas hf4 hg4 hh2
  have hmeas : AEStronglyMeasurable (fun x => f x * g x * h x) volume :=
    (hfmeas.mul hgmeas).mul hhmeas
  have hprod_ne : eLpNorm f 4 volume * eLpNorm g 4 volume * eLpNorm h 2 volume ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top hf4 hg4) hh2
  exact memℒp_one_iff_integrable.mp
    ⟨hmeas, hholder.trans_lt (lt_top_iff_ne_top.mpr hprod_ne)⟩

/-- Analytic bound for `b(u,v,w) = trilinearSmooth u v w = ∫ ((u·∇)v)·w`.
`holder_4442` is the exponent relation `1/4 + 1/4 + 1/2 = 1`, so the
integrand is estimated by `‖u‖_L4 * ‖∇v‖_L4 * ‖w‖_L2`. `H4_controls_L4`
bounds `u`. The same L⁴ estimate on each first derivative of `v` uses
`H1_embedding_L6_noncompact` and the second derivatives, which are terms of
`H4Norm`. `H4Norm` is real-valued, so finiteness is the `Memℒp` data rather
than a hypothesis `H4Norm < ∞`. No `L∞` embedding is assumed.
`H4_controls_trilinear` in `Wall266_TrilinearForm.lean` is not used and is
left unchanged. Compilation has not been run. -/
theorem trilinear_H4_bound (u v : TestVectorField) (w : R3 → R3)
    (hu : ∀ i j : Fin 3,
      Memℒp (partialDerivative u.toFun i j) 2 (volume : Measure R3))
    (hv1 : ∀ i j : Fin 3,
      Memℒp (partialDerivative v.toFun i j) 2 (volume : Measure R3))
    (hv2 : ∀ k i j : Fin 3,
      Memℒp (partialOrder2 v.toFun k i j) 2 (volume : Measure R3))
    (hw : Memℒp w 2 (volume : Measure R3)) :
    |trilinearSmooth u.toFun v.toFun w| ≤
      C_trilinear * H4Norm u.toFun * H4Norm v.toFun * L2Norm w := by
  let term : Fin 3 → Fin 3 → R3 → ℝ :=
    fun i j x => (u.toFun x) i * partialDerivative v.toFun i j x * (w x) j
  have hint : ∀ i j, Integrable (term i j) (volume : Measure R3) :=
    fun i j => product_integrable u v w hu hv1 hv2 hw i j
  have hpull : ∫ x, ∑ i : Fin 3, ∑ j : Fin 3, term i j x ∂(volume : Measure R3) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∫ x, term i j x ∂(volume : Measure R3) := by
    rw [integral_finset_sum (s := Finset.univ)
      (f := fun i x => ∑ j : Fin 3, term i j x)
      (fun i _ => integrable_finset_sum Finset.univ fun j _ => hint i j)]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact integral_finset_sum Finset.univ fun j _ => hint i j
  have hK : ∀ i j : Fin 3,
      |∫ x, term i j x ∂(volume : Measure R3)| ≤
        H1L4Constant * H4Norm u.toFun * (H1L4Constant * H4Norm v.toFun) * L2Norm w := by
    intro i j
    let f : R3 → ℝ := fun x => u.toFun x i
    let g : R3 → ℝ := partialDerivative v.toFun i j
    let h : R3 → ℝ := fun x => w x j
    have hfmeas : AEStronglyMeasurable f volume :=
      ((EuclideanSpace.proj i).continuous.comp u.smooth.continuous).aestronglyMeasurable
    have hgmeas : AEStronglyMeasurable g volume :=
      (partialDerivative_contDiff v i j).continuous.aestronglyMeasurable
    have hhmeas : AEStronglyMeasurable h volume :=
      (EuclideanSpace.proj j).continuous.comp_aestronglyMeasurable hw.aestronglyMeasurable
    have hf4 : eLpNorm f 4 volume ≠ ⊤ :=
      ((H1_embedding_L4_mem u hu).of_le hfmeas
        (Filter.Eventually.of_forall fun x => component_norm_le (u.toFun x) i)).eLpNorm_ne_top
    have hg4 : eLpNorm g 4 volume ≠ ⊤ :=
      partialDerivative_L4_ne_top v i j (hv1 i j) (fun k => hv2 k i j)
    have hh2 : eLpNorm h 2 volume ≠ ⊤ :=
      (hw.of_le hhmeas
        (Filter.Eventually.of_forall fun x => component_norm_le (w x) j)).eLpNorm_ne_top
    have hholder := holder_4442 f g h hfmeas hgmeas hhmeas hf4 hg4 hh2
    have hintabs : |∫ x, term i j x ∂(volume : Measure R3)| ≤
        ∫ x, |term i j x| ∂(volume : Measure R3) := by
      have h := norm_integral_le_integral_norm
        (μ := (volume : Measure R3)) (term i j)
      simpa only [Real.norm_eq_abs] using h
    have hmeas : AEStronglyMeasurable (fun x => f x * g x * h x) volume :=
      (hfmeas.mul hgmeas).mul hhmeas
    have hId : (fun x => |term i j x|) = (fun x => ‖f x * g x * h x‖) := by
      funext x
      rfl
    have hint_norm : ∫ x, |term i j x| ∂(volume : Measure R3) =
        (eLpNorm (fun x => f x * g x * h x) 1 volume).toReal := by
      rw [hId, integral_norm_eq_lintegral_nnnorm hmeas, eLpNorm_one_eq_lintegral_nnnorm]
    have hprod_ne : eLpNorm f 4 volume * eLpNorm g 4 volume * eLpNorm h 2 volume ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.mul_ne_top hf4 hg4) hh2
    have hto : (eLpNorm (fun x => f x * g x * h x) 1 volume).toReal ≤
        (eLpNorm f 4 volume).toReal * (eLpNorm g 4 volume).toReal *
          (eLpNorm h 2 volume).toReal := by
      have hle := ENNReal.toReal_mono hprod_ne hholder
      rwa [ENNReal.toReal_mul, ENNReal.toReal_mul] at hle
    have hu4 := component_L4_real_le u hu i
    have hv4 := partialDerivative_L4_real_le v i j (hv1 i j) (fun k => hv2 k i j)
    have hw2 := component_L2_real_le hw j
    have hC : 0 ≤ H1L4Constant := by
      unfold H1L4Constant
      exact NNReal.coe_nonneg _
    have hmul : (eLpNorm f 4 volume).toReal * (eLpNorm g 4 volume).toReal *
        (eLpNorm h 2 volume).toReal ≤
        (H1L4Constant * H4Norm u.toFun) * (H1L4Constant * H4Norm v.toFun) * L2Norm w := by
      have hfg := mul_le_mul hu4 hv4 ENNReal.toReal_nonneg (mul_nonneg hC (Real.sqrt_nonneg _))
      exact mul_le_mul hfg hw2 ENNReal.toReal_nonneg
        (mul_nonneg (mul_nonneg hC (Real.sqrt_nonneg _)) (mul_nonneg hC (Real.sqrt_nonneg _)))
    calc
      |∫ x, term i j x ∂(volume : Measure R3)| ≤ ∫ x, |term i j x| ∂(volume : Measure R3) :=
        hintabs
      _ = (eLpNorm (fun x => f x * g x * h x) 1 volume).toReal := hint_norm
      _ ≤ (eLpNorm f 4 volume).toReal * (eLpNorm g 4 volume).toReal *
            (eLpNorm h 2 volume).toReal := hto
      _ ≤ (H1L4Constant * H4Norm u.toFun) * (H1L4Constant * H4Norm v.toFun) * L2Norm w := hmul
      _ = H1L4Constant * H4Norm u.toFun * (H1L4Constant * H4Norm v.toFun) * L2Norm w := by ring
  have hsum : |∑ i : Fin 3, ∑ j : Fin 3, ∫ x, term i j x ∂(volume : Measure R3)| ≤
      ∑ i : Fin 3, ∑ j : Fin 3,
        H1L4Constant * H4Norm u.toFun * (H1L4Constant * H4Norm v.toFun) * L2Norm w := by
    rw [← Real.norm_eq_abs]
    refine (norm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum fun i _ => ?_
    refine (norm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum fun j _ => ?_
    rw [Real.norm_eq_abs]
    exact hK i j
  have hnine : ∑ i : Fin 3, ∑ j : Fin 3,
      H1L4Constant * H4Norm u.toFun * (H1L4Constant * H4Norm v.toFun) * L2Norm w =
      C_trilinear * H4Norm u.toFun * H4Norm v.toFun * L2Norm w := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, C_trilinear]
    ring
  have hid : trilinearSmooth u.toFun v.toFun w =
      ∫ x, ∑ i : Fin 3, ∑ j : Fin 3, term i j x ∂(volume : Measure R3) := by
    simp only [trilinearSmooth, term, partialDerivative]
  calc
    |trilinearSmooth u.toFun v.toFun w|
        = |∫ x, ∑ i : Fin 3, ∑ j : Fin 3, term i j x ∂(volume : Measure R3)| := by rw [hid]
    _ = |∑ i : Fin 3, ∑ j : Fin 3, ∫ x, term i j x ∂(volume : Measure R3)| := by rw [hpull]
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3,
          H1L4Constant * H4Norm u.toFun * (H1L4Constant * H4Norm v.toFun) * L2Norm w := hsum
    _ = C_trilinear * H4Norm u.toFun * H4Norm v.toFun * L2Norm w := hnine

end TheoremaAureum.Towers.NS.Wall266
