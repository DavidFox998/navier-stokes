import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace TheoremaAureum.Towers.NS.Phase97a

/-- Recorded L² norm of the weight `(1 + |ξ|²)⁻²` on `ℝ³`, `π / (4 √2)`.

The Fourier embedding argument that would identify this constant with that
integral is not formalized here. `Wall266_L2Extension` only needs the positive
real constant. -/
noncomputable def sobolevConstant_H4 : ℝ :=
  Real.pi / (4 * Real.sqrt 2)

theorem sobolevConstant_H4_eq :
    sobolevConstant_H4 = Real.pi / (4 * Real.sqrt 2) := rfl

theorem sobolevConstant_H4_pos : 0 < sobolevConstant_H4 := by
  unfold sobolevConstant_H4
  exact div_pos Real.pi_pos (mul_pos (by norm_num) (Real.sqrt_pos.mpr (by norm_num)))

end TheoremaAureum.Towers.NS.Phase97a
