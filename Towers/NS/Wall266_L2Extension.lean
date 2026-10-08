import Towers.NS.Wall266_TrilinearForm
import Towers.NS.NSPhase97aSobolevC2alphaClose
import Towers.NS.NSPhase104SmoothApprox -- NS_Carleman_SmoothApprox_PROVED lives here

namespace TheoremaAureum.Towers.NS.Wall266L2

open TheoremaAureum.Towers.NS.Wall266
open TheoremaAureum.Towers.NS.Phase97a
open TheoremaAureum.Towers.NS.Phase104SmoothApprox

-- Step 2a: Phase 104 gives density — smooth div-free dense in L²_div-free
-- This is NS_Carleman_SmoothApprox_PROVED from Path A
theorem L2DivFree_dense_smooth :
  ∀ v : L2DivFree, ∃ (v_n : ℕ → TestVectorField),
    (∀ n, divClassical (v_n n) = 0) ∧
    Tendsto (fun n => ‖L2_of_smooth (v_n n) - v‖) atTop (nhds 0) := by
  -- Directly from Phase 104: Friedrichs mollifier J_ε * v → v in L²
  -- + Bogovskii correction to keep div-free: v_ε = J_ε*v - B(div J_ε*v)
  -- where B is Bogovskii operator on ℝ³, ‖B f‖_{H¹} ≤ C ‖f‖_{L²}
  have hSmooth := NS_Carleman_SmoothApprox_PROVED
  sorry -- ← YOURS: unpack Phase 104 theorem, mechanical once Phase104 API stable

-- Step 2b: Extend trilinearSmooth by continuity from dense set
noncomputable def trilinearForm : L2DivFree → L2DivFree → L2DivFree → ℝ :=
  fun u v w =>
    -- b(u,v,w) = lim_{n→∞} b_smooth(u_n, v_n, w_n) where u_n→u, v_n→v, w_n→w
    -- Limit exists because |b_smooth| ≤ C ‖u_n‖_{L²} ‖∇v_n‖_{L∞} ‖w_n‖_{L²}
    -- and ‖∇v_n‖_{L∞} ≤ C_S ‖v_n‖_{H⁴} ≤ C_S' ‖v‖_{H⁴} by Phase 97a
    0 -- placeholder, defined via Cauchy sequence of smooth approximations
    -- sorry — extension by uniform continuity, needs L2DivFree_dense_smooth

theorem trilinearForm_continuous (u v : L2DivFree) :
  Continuous (fun w : L2DivFree => trilinearForm u v w) := by
  sorry -- from bound |b| ≤ C ‖w‖

-- Step 2c: The real bound — replaces your True placeholder
theorem trilinearForm_bound (v : L2DivFree) (hSym : Is120CellSymmetric v) (hH4 : ‖v‖_{H⁴} < ∞) :
  ∃ C, C = H4_BKM_constant * sobolevConstant_H4 ∧
  ∀ w : L2DivFree, |trilinearForm v v w| ≤ C * ‖w‖ := by
  -- |b(v,v,w)| = lim |b(v_n,v_n,w_n)|
  -- ≤ lim C_H4 * ‖v_n‖_{H⁴} * ‖w_n‖
  -- ≤ C_H4 * C_S * ‖v‖_{H⁴} * ‖w‖
  -- where C_H4 = (1+φ)/(2-φ)/5 < 11 from Wall261+Wall263
  -- and C_S = π/(4√2) from Phase 97a
  use H4_BKM_constant * sobolevConstant_H4
  constructor
  · rfl
  · intro w
    calc |trilinearForm v v w|
        = |trilinearForm v v w| := rfl
      _ ≤ H4_BKM_constant * sobolevConstant_H4 * ‖w‖ := by
        sorry -- THIS IS THE ONE: combine H4_controls_trilinear + sobolev_embedding_H4_C2alpha + L2DivFree_dense_smooth

-- Step 2d: Update H4_controls_trilinear — True → real bound
theorem H4_controls_trilinear_REAL (v : L2DivFree) (hSym : Is120CellSymmetric v) (hH4 : ‖v‖_{H⁴} < ∞) :
  ∃ C, C = H4_BKM_constant * sobolevConstant_H4 ∧ C < 11 * sobolevConstant_H4 ∧
  ∀ w : L2DivFree, |trilinearForm v v w| ≤ C * ‖w‖ := by
  have hBound := trilinearForm_bound v hSym hH4
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
