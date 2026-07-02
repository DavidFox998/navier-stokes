/-
================================================================
Towers / NS / H4_UniformBound
— Named open surface for the 120-cell L^∞ gradient integral bound.

HONEST SCOPE.  This file states the surface the user will prove:

  H4_GradLinfty_Bound (s : ℝ) : Prop

    For every H4-symmetric initial datum u₀ there exists C > 0 such
    that for every modeled weak NS solution u starting from u₀ and
    every time horizon T > 0:

      ∫₀^T GradLinftyNorm (u t) dt  ≤  C · ‖u₀‖

    where GradLinftyNorm is the Sobolev-norm surrogate for the
    physical-space L^∞ gradient ‖∇u(·,t)‖_{L^∞(ℝ³)}.

EVERYTHING IS A NAMED OPEN DEF — no `axiom`, no `sorry`.
The user will discharge H4_GradLinfty_Bound in a separate file
`H4_uniform_bound.lean` by importing this one.

Mathematical context (Beale–Kato–Majda 1984):
  If ∫₀^T ‖∇u(s)‖_{L^∞} ds < ∞ for all T, the BKM continuation
  criterion is satisfied uniformly, and the solution extends smoothly
  past every T > 0 — global regularity for H4-symmetric initial data.

H4 symmetry route:
  The icosahedral symmetry group I_h ≅ (W(H₄) |_{ℝ³}) of order 120
  is the symmetry group of the 600-cell {3,3,5}.  For u₀ invariant
  under I_h, the vorticity inherits the symmetry and the 120-cell
  spectral gap (connective constant 1+φ ≈ 2.618 < 6 = ℤ⁴ degree)
  is expected to supply the L^∞ gradient control absent in the
  general case.

WHAT IS NOT PROVED HERE:
  * IsH4Symmetric    — open; group action on Hdiv_free not formalized.
  * GradLinftyNorm   — Sobolev surrogate; physical-space L^∞ absent.
  * H4_GradLinfty_Bound — THE surface; proved by user.

WHAT IS PROVED:
  * H4_BKM_norm_bound — trivial combinator extracting the bound from
    H4_GradLinfty_Bound.  Classical trio, 0 cert axioms, 0 sorry.
  * H4_norm_le_initial — energy monotone norm bound for H4-symmetric
    weak solutions (from WeakNS.energy_le, 0 cert axioms).

Axiom footprint for proved theorems: {propext, Classical.choice, Quot.sound}.
================================================================
-/
import Towers.NS.WeakSolution
import Mathlib.MeasureTheory.Integral.IntervalIntegral

open MeasureTheory
open TheoremaAureum.Towers.NS.FunctionSpaces
open TheoremaAureum.Towers.NS.WeakSolution

namespace TheoremaAureum
namespace Towers
namespace NS
namespace H4UniformBound

variable {s : ℝ}

/-! ### H4 symmetry predicate — named open surface -/

/-- **OPEN SURFACE: IsH4Symmetric.**

    A divergence-free velocity field u₀ : Hdiv_free (s+2) is
    *H4-symmetric* if it is invariant under the icosahedral symmetry
    group I_h, the unique maximal finite subgroup of SO(3) of order 120.

    I_h is the 3D shadow of the W(H₄) Weyl group (order 14400): the
    600-cell {3,3,5} has 120 vertices on the unit 3-sphere; their
    projection to ℝ³ gives the symmetry group of the icosahedron.

    OPEN: the I_h group action on Hdiv_free (s+2) is not formalized in
    Mathlib v4.12.0.  This `def` is a named placeholder.
    The user refines this in H4_uniform_bound.lean. -/
def IsH4Symmetric (u₀ : Hdiv_free (s + 2)) : Prop :=
  True

/-! ### L^∞ gradient norm surrogate -/

/-- **Surrogate: GradLinftyNorm.**

    The physical-space Beale–Kato–Majda quantity is
      ‖∇u(·, t)‖_{L^∞(ℝ³)} = ess-sup_{x ∈ ℝ³} |∇u(x, t)|.

    In the Fourier model, Hdiv_free (s+2) encodes Hˢ⁺² Sobolev
    regularity.  The Sobolev embedding ∂ : Hˢ ↪ L^∞(ℝ³) holds for
    s > 5/2, so ‖∇u‖_{L^∞} ≲ ‖u‖_{H^{s+2}} for s > 1/2.
    This `def` uses the Sobolev norm ‖u‖ as the honest Fourier-model
    surrogate, pending the full Sobolev embedding API in Mathlib. -/
noncomputable def GradLinftyNorm (u : Hdiv_free (s + 2)) : ℝ := ‖u‖

/-! ### The 120-cell L^∞ integral bound — THE named open surface -/

/-- **OPEN SURFACE: H4_GradLinfty_Bound.**

    For every H4-symmetric initial datum u₀ : Hdiv_free (s+2), there
    exists a constant C > 0 (depending only on ‖u₀‖) such that for
    every modeled weak NS solution u with WeakNS u u₀ f and every
    time horizon T > 0:

        ∫₀^T GradLinftyNorm (u t) dt  ≤  C · ‖u₀‖.

    This is the Fourier-model formulation of the Beale–Kato–Majda
    L^∞ gradient time-integral bound for H4-symmetric data.

    OPEN: the user will prove this in H4_uniform_bound.lean using the
    120-cell spectral gap and the icosahedral symmetry reduction. -/
def H4_GradLinfty_Bound (s : ℝ) : Prop :=
  ∀ (u₀ : Hdiv_free (s + 2)),
  IsH4Symmetric u₀ →
  ∀ (f : ExternalForce s) (u : ℝ → Hdiv_free (s + 2)),
  WeakNS u u₀ f →
  ∃ C : ℝ, 0 < C ∧
    ∀ T : ℝ, 0 < T →
      ∫ t in (0 : ℝ)..T, GradLinftyNorm (u t) ≤ C * ‖u₀‖

/-! ### Proved combinators (classical trio, 0 cert axioms) -/

/-- **Energy monotone norm bound for H4-symmetric data.**

    For any modeled weak NS solution u with H4-symmetric initial datum
    u₀ and any t ≥ 0, ‖u t‖ ≤ ‖u₀‖.

    Proof: WeakNS.energy_le gives energy u t ≤ energy u 0 = ‖u₀‖²;
    sqrt-monotone closes ‖u t‖ ≤ ‖u₀‖.

    Axiom footprint: {propext, Classical.choice, Quot.sound}. -/
theorem H4_norm_le_initial
    (u₀ : Hdiv_free (s + 2)) (_h4 : IsH4Symmetric u₀)
    (f : ExternalForce s) (u : ℝ → Hdiv_free (s + 2))
    (hweak : WeakNS u u₀ f)
    (t : ℝ) (ht : 0 ≤ t) :
    ‖u t‖ ≤ ‖u₀‖ := by
  have h_ineq := hweak.energy_le t ht
  simp only [Energy.energy_def] at h_ineq
  have h_init : u 0 = u₀ := hweak.init
  rw [h_init] at h_ineq
  have h1 : Real.sqrt (‖u t‖ ^ 2) ≤ Real.sqrt (‖u₀‖ ^ 2) :=
    Real.sqrt_le_sqrt h_ineq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h1

/-- **Trivial combinator: extract the L^∞ integral bound.**

    Given H4_GradLinfty_Bound, pass through H4-symmetric initial data
    to obtain the concrete C and the pointwise inequality for each T.

    Axiom footprint: {propext, Classical.choice, Quot.sound}. -/
theorem H4_BKM_norm_bound
    (hbound : H4_GradLinfty_Bound s)
    (u₀ : Hdiv_free (s + 2)) (hu₀ : IsH4Symmetric u₀)
    (f : ExternalForce s) (u : ℝ → Hdiv_free (s + 2))
    (hweak : WeakNS u u₀ f) :
    ∃ C : ℝ, 0 < C ∧
      ∀ T : ℝ, 0 < T →
        ∫ t in (0 : ℝ)..T, GradLinftyNorm (u t) ≤ C * ‖u₀‖ :=
  hbound u₀ hu₀ f u hweak

/-! ### Open surface registry -/

/-- NS H4 open surface count: 1.
    Surface: H4_GradLinfty_Bound — to be proved in H4_uniform_bound.lean. -/
def ns_h4_open_surface_count : ℕ := 1

/-- Honest scope marker: IsH4Symmetric is a True-placeholder pending the
    I_h group-action formalization.  The user's H4_uniform_bound.lean
    should shadow or refine this definition before proving H4_GradLinfty_Bound. -/
def ns_h4_symmetry_is_placeholder : True := trivial

end H4UniformBound
end NS
end Towers
end TheoremaAureum
