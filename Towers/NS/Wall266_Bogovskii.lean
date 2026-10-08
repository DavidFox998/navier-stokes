/-
Wall266_Bogovskii — Path B, an OPEN Bogovskii scaffold.

Formal status:
* The operator below is an integral formula, not a zero placeholder.
* A normalized smooth cutoff is an explicit input. Its existence has not
  been constructed here.
* The divergence/regularity statement and the uniform H1 estimate each
  have an explicit OPEN proof obligation.
* Nothing here closes L2DivFree_dense_smooth or any Phase104 obligation.

For a ball of radius R > 0, use a normalized cutoff omega_R supported
strictly inside that ball. In dimension three, the standard kernel is

  K_R(x,y) = (x-y) * integral_{1}^{infinity}
                         omega_R(y + r(x-y)) r^2 dr.

There is no additional |x-y|^{-3} factor with this radial variable.
That factor occurs in the alternative formula whose radial integral
starts at |x-y| and uses the unit direction (x-y)/|x-y|.

The standard bounds are L2(B f) <= C R L2(f) and
L2(gradient(B f)) <= C L2(f). Thus the full inhomogeneous H1 bound
below uses C(1+R). A uniform CR bound for full H1 on all R > 0 is
not the standard scaling.

Bochner integrals are total definitions. The missing proofs must justify
integrability, the singular diagonal, differentiation and cancellation;
the presence of an integral expression alone proves none of these.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

namespace TheoremaAureum.Towers.NS.Wall266Bogovskii

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- Euclidean three-space, rather than the supremum-norm function space. -/
abbrev R3 := EuclideanSpace ℝ (Fin 3)

/-- The open Euclidean ball centered at zero. -/
def ballR (R : ℝ) : Set R3 := Metric.ball (0 : R3) R

/-- Required normalized cutoff data. No zero cutoff is substituted for it.
OPEN infrastructure: construct such data from a smooth bump. -/
structure BogovskiiCutoff where
  toFun : R3 → ℝ
  smooth : ContDiff ℝ ⊤ toFun
  compact_support : HasCompactSupport toFun
  support_in_unit_ball : Function.support toFun ⊆ ballR 1
  nonnegative : ∀ x, 0 ≤ toFun x
  integral_one : (∫ x, toFun x ∂(volume : Measure R3)) = 1

/-- The dimension-three rescaling of the supplied unit-ball cutoff.
Its normalization and support properties for R > 0 still need formal proofs. -/
def bogovskii_cutoff (omega : BogovskiiCutoff) (R : ℝ) (x : R3) : ℝ :=
  (R ^ 3)⁻¹ * omega.toFun (R⁻¹ • x)

/-- The actual Bogovskii kernel. The singular diagonal and integrability
requirements belong to the OPEN analytic proofs below. -/
def BogovskiiKernel (omega : BogovskiiCutoff) (R : ℝ) (x y : R3) : R3 :=
  (∫ r in Set.Ioi (1 : ℝ),
    bogovskii_cutoff omega R (y + r • (x - y)) * r ^ 2) • (x - y)

/-- The integral operator. Scalar multiplication, not pointwise vector
multiplication, gives the vector-valued Bochner integrand. -/
def Bogovskii (omega : BogovskiiCutoff) (R : ℝ) (f : R3 → ℝ) : R3 → R3 :=
  fun x => ∫ y, f y • BogovskiiKernel omega R x y ∂(volume : Measure R3)

/-- Classical derivative of component j in coordinate direction i.
This is appropriate for the smooth output claimed in div_Bogovskii;
it is not a definition of a general weak derivative. -/
def coordinateDerivative (v : R3 → R3) (i j : Fin 3) : R3 → ℝ :=
  fun x => deriv
    (fun t : ℝ => (v (x + t • EuclideanSpace.single i 1)) j) 0

/-- Classical coordinate divergence. No nonexistent HasDivAt API is used. -/
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

/-- The inhomogeneous H1 quantity on fields satisfying H1Regular.
It is not asserted to be a norm on all arbitrary functions. -/
def H1Norm (v : R3 → R3) : ℝ :=
  Real.sqrt
    ((eLpNorm v 2 (volume : Measure R3)).toReal ^ 2 +
      ∑ i : Fin 3, ∑ j : Fin 3,
        (eLpNorm (coordinateDerivative v i j) 2
          (volume : Measure R3)).toReal ^ 2)

/-- OPEN: the integral formula produces a smooth compactly supported
right inverse of divergence for smooth, compactly supported, mean-zero data.
The support condition is on the open ball and R is strictly positive.
The missing kernel identity has a diagonal delta term and a cutoff
correction; the latter cancels using the mean-zero hypothesis. -/
theorem div_Bogovskii (omega : BogovskiiCutoff) (R : ℝ) (f : R3 → ℝ)
    (hR : 0 < R)
    (hf : ContDiff ℝ ⊤ f)
    (hf_compact : HasCompactSupport f)
    (h_mean : (∫ y, f y ∂(volume : Measure R3)) = 0)
    (h_supp : Function.support f ⊆ ballR R) :
    ContDiff ℝ ⊤ (Bogovskii omega R f) ∧
      HasCompactSupport (Bogovskii omega R f) ∧
      Function.support (Bogovskii omega R f) ⊆ ballR R ∧
      ∀ x, divClassical (Bogovskii omega R f) x = f x := by
  sorry -- OPEN: cutoff normalization, kernel cancellation, regularity and support.

/-- OPEN: a uniform H1 estimate for the fixed normalized cutoff.
C is chosen before R and f, so this is a genuine uniform estimate rather
than a constant chosen separately for each output. H1Regular is included
to prevent the real norm conversions from hiding infinite quantities.
The proof requires the L2 singular-integral estimate for the derivative
and the radius-scaled L2 estimate for the operator itself. -/
theorem H1_bound_Bogovskii (omega : BogovskiiCutoff) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (R : ℝ) (f : R3 → ℝ)
        (hR : 0 < R)
        (hf : ContDiff ℝ ⊤ f)
        (hf_compact : HasCompactSupport f)
        (h_mean : (∫ y, f y ∂(volume : Measure R3)) = 0)
        (h_supp : Function.support f ⊆ ballR R),
        H1Regular (Bogovskii omega R f) ∧
          H1Norm (Bogovskii omega R f) ≤ C * (1 + R) * L2Norm f := by
  sorry -- OPEN: Calderon-Zygmund derivative bound and the radius-scaled L2 bound.

-- Future density work: apply the operator to the mean-zero divergence
-- created by a smooth cutoff. The Phase104 smoothing/convergence obligations
-- and the application to L2DivFree_dense_smooth remain separate OPEN work.

end

end TheoremaAureum.Towers.NS.Wall266Bogovskii
