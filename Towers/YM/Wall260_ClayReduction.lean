import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace TheoremaAureum.Towers.YM.Wall260

/-- Pointwise dependence-defect reduction at threshold `log (7 · C)`.

If `I_E x - I_polymer x < log C` and `log (7 · C) < I_E x`, then
`log 7 < I_polymer x`. The constant `C` is the dependence bound
(`C = 6` for the ℤ⁴ link, `C = 1 + φ` in the H4 improvement). -/
theorem new_clay_reduction {C : ℝ} (hC : 0 < C) {I_E I_polymer : ℝ → ℝ}
    (h_defect : ∀ x, I_E x - I_polymer x < Real.log C)
    (h_rate : ∀ x, Real.log (7 * C) < I_E x) :
    ∀ x, Real.log 7 < I_polymer x := by
  intro x
  have h7 : (0 : ℝ) < 7 := by norm_num
  have hlog : Real.log (7 * C) = Real.log 7 + Real.log C :=
    Real.log_mul h7.ne' hC.ne'
  have hdef : I_E x - Real.log C < I_polymer x := by
    linarith [h_defect x]
  have hshift : Real.log (7 * C) - Real.log C < I_E x - Real.log C := by
    linarith [h_rate x]
  rw [hlog] at hshift
  linarith

end TheoremaAureum.Towers.YM.Wall260
