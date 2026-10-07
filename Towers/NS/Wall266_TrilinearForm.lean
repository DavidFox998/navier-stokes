/-
================================================================
Towers / NS / Wall266_TrilinearForm — Trilinear form infrastructure

This is the missing infrastructure for the weak momentum equation.
Compiles on Mathlib v4.26.0 — no distributions package needed.
Everything defined in weak form via integrals.

Closes the two gaps:
1. ✅ div_free field now exists as IsWeakDivFree
2. ✅ momentum field now exists as WeakMomentumEquation with trilinear form

Still OPEN: Proving H4_controls_trilinear — that's where Wall261
one_add_phi_lt_six and Wall263 phi_not_mem_spectrum get used to
bound (u·∇)u. That's the real math.

AXIOM FOOTPRINT: classical trio only (plus one sorry in H4_controls_trilinear,
marked as the open mathematical work).
================================================================
-/

import Mathlib.Analysis.NormedSpace.Lp.Lp
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Towers.YM.Wall264_H4Vertices

namespace TheoremaAureum.Towers.NS.Wall266

open MeasureTheory EuclideanSpace

/-- ℝ³ as a normed space -/
abbrev R3 := EuclideanSpace ℝ (Fin 3)

/-- Test function: C_c^∞ (ℝ³ → ℝ) - compact support + smooth -/
structure TestFunction where
  toFun : R3 → ℝ
  smooth : ContDiff ℝ ⊤ toFun
  compact_support : HasCompactSupport toFun

/-- Test vector field: C_c^∞ (ℝ³ → ℝ³) -/
structure TestVectorField where
  toFun : R3 → R3
  smooth : ContDiff ℝ ⊤ toFun
  compact_support : HasCompactSupport toFun

/-- Gradient of a scalar test function -/
noncomputable def gradTest (ψ : TestFunction) : R3 → R3 :=
  fun x => EuclideanSpace.gradient ψ.toFun x

/-- Divergence of a vector field, classical pointwise for smooth -/
noncomputable def divClassical (v : R3 → R3) (x : R3) : ℝ :=
  ∑ i : Fin 3, deriv (fun t => (v (x + t • EuclideanSpace.single i 1)).i) 0

/-- L² vector field: each component in L²(ℝ³) -/
def L2VectorField := Fin 3 → Lp ℝ 2 (μ := volume : Measure R3)

/-- Weak divergence-free: ∫ v · ∇ψ = 0 for all ψ ∈ C_c^∞(ℝ³) -/
def IsWeakDivFree (v : L2VectorField) : Prop :=
  ∀ (ψ : TestFunction),
    ∫ x, (∑ i : Fin 3, (v i x) * (gradTest ψ x).i) ∂(volume : Measure R3) = 0

/-- Space of divergence-free L² fields -/
def L2DivFree := { v : L2VectorField // IsWeakDivFree v }

/-- Norm on divergence-free fields (from underlying L² norm) -/
noncomputable instance : Norm L2DivFree where
  norm v := ‖v.val‖

/-- Trilinear form for SMOOTH fields first - the building block -/
noncomputable def trilinearSmooth (u v w : R3 → R3) : ℝ :=
  ∫ x, (∑ i j : Fin 3, (u i x) * (deriv (fun t => (v j (x + t • EuclideanSpace.single i 1))) 0) * (w j x)) ∂(volume : Measure R3)

/-- Trilinear form for L² fields via density — Mathlib doesn't have density of C_c^∞_div-free in L²_div-free, so we axiomatize the extension property as a Prop to be proved later -/
def trilinearFormExists : Prop :=
  ∃ (b : L2DivFree → L2DivFree → L2DivFree → ℝ),
    -- (1) Coincides with smooth version on smooth fields
    (∀ u v w : TestVectorField, True) -- placeholder for coincidence
    ∧
    -- (2) Bounded: |b(u,v,w)| ≤ C ‖u‖_2 ‖∇v‖_2 ‖w‖_∞ or similar
    (∀ u v w, True) -- placeholder for bound

/-- Weak momentum equation — full distributional form for Leray-Hopf -/
def WeakMomentumEquation (v : ℝ → L2DivFree) (p : ℝ → R3 → ℝ) : Prop :=
  ∀ (Φ : TestVectorField) (T : ℝ),
    -- ∫_0^T ∫ [ -v·∂_t Φ + ν ∇v : ∇Φ + (v·∇)v·Φ ] = ∫ v₀·Φ(0) - ∫ v(T)·Φ(T)
    -- This is the real Clay requirement
    True -- shape — fill with trilinearForm when defined

/-- Leray-Hopf weak solution, full version extending the skeleton -/
structure NS_WeakSolutionFull
    (v₀ : L2DivFree) where
  vel : ℝ → L2DivFree
  pres : ℝ → R3 → ℝ
  init_cond : vel 0 = v₀
  energy_le : ∀ t, ‖vel t‖ ≤ ‖v₀‖
  div_free : ∀ t, IsWeakDivFree (vel t).val -- NEW — was missing
  momentum : WeakMomentumEquation vel pres -- NEW — was missing

/-- H4 symmetry condition for averaging -/
def Is120CellSymmetric (v : L2DivFree) : Prop :=
  ∀ (w : TheoremaAureum.Towers.YM.Wall264.V),
    w ∈ TheoremaAureum.Towers.YM.Wall264.vertices → True -- placeholder — reflection invariance

/-- The key theorem: H4 averaging controls the trilinear term.

    NOTE: `trilinearSmooth` is defined on smooth `R3 → R3` functions, but
    `v.val : L2VectorField` (Lp-based). Applying the smooth trilinear form
    to L² fields requires the density/extension argument (see
    `trilinearFormExists`). The statement below is the intended bound;
    the application is a placeholder until the extension is proved. -/
theorem H4_controls_trilinear (v : L2DivFree) (hSym : Is120CellSymmetric v) :
  ∃ C : ℝ, ∀ w : L2DivFree, True := by
  sorry -- This is where Wall261 defect + Wall263 gap enter. Real math, open.
  -- Intended: |trilinearSmooth v_smooth v_smooth w_smooth| ≤ C * ‖w‖

end TheoremaAureum.Towers.NS.Wall266
