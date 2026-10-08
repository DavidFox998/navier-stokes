/-
Wall266 H4/L4 norm scaffolding.

This file introduces a genuine L4 quantity through Mathlib's eLpNorm and an
H1 quantity built from the vector L2 norm and the componentwise L2 norm of
the classical first derivatives. H4 derivatives are not defined here: the
placeholder is exactly the existing L2 norm and is explicitly not an H4 norm.

The noncompact vector-valued H1 embedding below is an OPEN proposition,
not an axiom, a supplied proof, or a theorem.
Written proofs of L2/L6 interpolation and compact-support Sobolev inequalities
use the pinned Mathlib APIs. A conditional Fatou passage states exactly the
approximation data still needed for the noncompact case; it does not construct
that data. Compilation of these additions has not been run.
The 4-4-2 Holder inequality uses Mathlib's extended-real Holder API.
This does not close the analytic trilinear-form bound.
-/

import Towers.NS.Wall266_TrilinearForm
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
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
    convert h using 1 <;> norm_num [Real.rpow_natCast]
  have h3 :
      eLpNorm (fun x => ‖u x‖ ^ (3 : ℕ)) 2 volume =
        (eLpNorm u 6 volume) ^ (3 : ℝ) := by
    have h := eLpNorm_norm_rpow (p := (2 : ℝ≥0∞))
      (μ := (volume : Measure R3)) u (by norm_num : 0 < (3 : ℝ))
    convert h using 1 <;> norm_num [Real.rpow_natCast]
  have hHolder :
      eLpNorm (fun x => ‖u x‖ * ‖u x‖ ^ (3 : ℕ)) 1 volume ≤
        eLpNorm (fun x => ‖u x‖) 2 volume *
          eLpNorm (fun x => ‖u x‖ ^ (3 : ℕ)) 2 volume := by
    refine eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm
      hu.norm (hu.norm.pow 3) (fun a b : ℝ => a * b) ?_ ?_
    · exact Filter.Eventually.of_forall
        (fun x => le_of_eq (nnnorm_mul (‖u x‖) (‖u x‖ ^ (3 : ℕ))))
    · norm_num
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
    constructor <;> norm_num
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
      ac_rfl

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
  have hFatou := eLpNorm_lim_le_liminf_eLpNorm (p := (6 : ℝ≥0∞))
    (fun n => (hs n).continuous.aestronglyMeasurable) u hpoint
  refine hFatou.trans ?_
  apply Filter.liminf_le_of_frequently_le'
  exact (Filter.Eventually.of_forall (fun n =>
    (H1_embedding_L6_Sobolev (hcs n) (hs n)).trans
      (mul_le_mul_left' (hderiv n) _))).frequently

end HilbertSobolevSteps

/-- OPEN PROPOSITION (not proved or assumed): the standard three-dimensional Sobolev embedding
H1 → L4, stated for smooth L2 vector fields with L2 first derivatives.
Path A no longer assumes compact support, so derivative L2 membership must
be explicit; smoothness and L2 membership alone do not provide it.
The vector L4 quantity uses the pointwise Euclidean norm. Interpolation and the
compact-support Sobolev estimate are written above. OPEN: construct the
noncompact cutoff/limit argument and compare the Frechet-derivative L2 norm
with the nine coordinate-derivative quantities in the existing `H1Norm`.
The previous density theorem is L2-only, not H1 density.
This definition only records the proposition. It supplies no witness or proof
and cannot be used as an embedding theorem. -/
def H1_embedding_L4_OPEN : Prop :=
  ∃ C : ℝ, ∀ v : TestVectorField,
    (∀ i j : Fin 3,
      Memℒp (partialDerivative v.toFun i j) 2 (volume : Measure R3)) →
    eLpNorm_L4 (fun x : R3 => ‖v.toFun x‖) ≤ C * H1Norm v.toFun

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
    · norm_num
  calc
    eLpNorm (fun x => f x * g x * h x) 1 volume
        ≤ eLpNorm (fun x => f x * g x) 2 volume * eLpNorm h 2 volume := by
          refine eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm
            (hf.mul hg) hh (fun a b : ℝ => a * b) ?_ ?_
          · exact Filter.Eventually.of_forall
              (fun x => le_of_eq (nnnorm_mul (f x * g x) (h x)))
          · norm_num
    _ ≤ eLpNorm f 4 volume * eLpNorm g 4 volume * eLpNorm h 2 volume :=
      mul_le_mul_right' h_fg_L2 _

end TheoremaAureum.Towers.NS.Wall266
