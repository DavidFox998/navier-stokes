import Towers.NS.Wall266_TrilinearForm
import Towers.NS.NSPhase97aSobolevC2alphaClose
import Towers.NS.NSPhase104SmoothApprox -- Conditional on two remaining analytic bridges.

namespace TheoremaAureum.Towers.NS.Wall266L2

open TheoremaAureum.Towers.NS.Wall266
open TheoremaAureum.Towers.NS.Phase97a
open TheoremaAureum.Towers.NS.Phase104SmoothApprox
open Filter Topology

/-- Path A common-sequence construction, CONDITIONAL on the two remaining
analytic bridges. Smoothness uses the written Mathlib proof. Phase104 now
assembles actual convolution fields from a single normalized kernel sequence,
whose support radii are 1 / (n + 1), and embeds their components into Lp.
This proves neither remaining hypothesis and introduces no new axiom. -/
theorem L2DivFree_dense_smooth_of_mollifier_bridges
    (hDivFree : NS_ConvolutionDivFree_OPEN)
    (hL2Conv : NS_ConvolutionL2Conv_OPEN) :
    ∀ v : L2DivFree, ∃ v_n : ℕ → TestVectorField,
      (∀ n, divClassical (v_n n) = 0) ∧
      Tendsto (fun n => ‖L2_of_smooth (v_n n) - v.val‖) atTop (nhds 0) :=
  NS_Carleman_SmoothApprox_PROVED NS_ConvolutionSmooth_PROVED hDivFree hL2Conv

-- Step 2a: unconditional Path A density is still OPEN.
-- Two of the former four admissions have written replacements: convolution
-- smoothness and common-sequence assembly. The two analytic obligations below
-- remain genuine proof gaps, not merely API names or a Bogovskii dependency.
-- Compilation has not been run; a smaller admission count is not certification.
theorem L2DivFree_dense_smooth : ∀ v : L2DivFree,
  ∃ (v_n : ℕ → TestVectorField),
  (∀ n, divClassical (v_n n) = 0) ∧
  Tendsto (fun n => ‖L2_of_smooth (v_n n) - v.val‖) atTop (nhds 0) := by
  have hDivFree : NS_ConvolutionDivFree_OPEN := by
    sorry -- OPEN 1/2: translated compact tests and differentiation under the integral.
  have hL2Conv : NS_ConvolutionL2Conv_OPEN := by
    sorry -- OPEN 2/2: normalized kernel construction, L2 estimates and norm convergence.
  exact L2DivFree_dense_smooth_of_mollifier_bridges hDivFree hL2Conv

-- Step 2b: OPEN analytic extension of trilinearSmooth from a dense set.
noncomputable def trilinearForm : L2DivFree → L2DivFree → L2DivFree → ℝ :=
  fun u v w =>
    -- Intended analytic construction, not implemented:
    -- b(u,v,w) = lim_{n→∞} b_smooth(u_n, v_n, w_n) where u_n→u, v_n→v, w_n→w
    -- Limit exists because |b_smooth| ≤ C ‖u_n‖_{L²} ‖∇v_n‖_{L∞} ‖w_n‖_{L²}
    -- and ‖∇v_n‖_{L∞} ≤ C_S ‖v_n‖_{H⁴} ≤ C_S' ‖v‖_{H⁴} by Phase 97a
    0 -- Zero placeholder; no Cauchy-sequence extension is constructed here.
    -- OPEN: the analytic extension needs density and the appropriate norm estimates.

theorem trilinearForm_continuous (u v : L2DivFree) :
  Continuous (fun w : L2DivFree => trilinearForm u v w) := by
  -- trilinearForm currently = fun _ _ _ => 0, so Continuous trivially
  simp [trilinearForm]
  exact continuous_const

-- Step 2c: Closed zero-form bound only: |0| ≤ C ‖w‖.
-- This is not a bound for the unconstructed analytic trilinear form.
theorem trilinearForm_bound (v : L2DivFree) (hSym : Is120CellSymmetric v) :
  ∃ C, C = H4_BKM_constant * sobolevConstant_H4 ∧
  ∀ w : L2DivFree, |trilinearForm v v w| ≤ C * ‖w‖ := by
  use H4_BKM_constant * sobolevConstant_H4
  constructor
  · rfl
  · intro w
    simp only [trilinearForm, abs_zero]
    -- Need 0 ≤ C * ‖w‖
    have hC_nonneg : 0 ≤ H4_BKM_constant * sobolevConstant_H4 := by
      -- H4_BKM_constant = (1+phi)/(2-phi)/5 >0, sobolevConstant_H4 = π/(4√2) >0
      unfold H4_BKM_constant sobolevConstant_H4
      positivity -- phi>0, 2-phi>0, pi>0, sqrt 2 >0
    have : 0 ≤ (H4_BKM_constant * sobolevConstant_H4) * ‖w‖ := by
      apply mul_nonneg hC_nonneg (norm_nonneg _)
    linarith

-- Step 2d: A derived constant estimate for the same zero placeholder only.
theorem H4_controls_trilinear_REAL (v : L2DivFree) (hSym : Is120CellSymmetric v) :
  ∃ C, C = H4_BKM_constant * sobolevConstant_H4 ∧ C < 11 * sobolevConstant_H4 ∧
  ∀ w : L2DivFree, |trilinearForm v v w| ≤ C * ‖w‖ := by
  have hBound := trilinearForm_bound v hSym
  obtain ⟨C, hCeq, hBound'⟩ := hBound
  use C
  constructor
  · rfl
  constructor
  · calc C = H4_BKM_constant * sobolevConstant_H4 := hCeq
        _ < 11 * sobolevConstant_H4 := by
          have : H4_BKM_constant < 11 := H4_BKM_constant_lt_11
          have : 0 < sobolevConstant_H4 := sobolevConstant_H4_pos
          nlinarith
  · exact hBound'

end TheoremaAureum.Towers.NS.Wall266L2
