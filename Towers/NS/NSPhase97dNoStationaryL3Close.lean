import Mathlib.Analysis.Fourier.RieszTransform
import Towers.NS.NSPhase97aSobolevC2alphaClose

open Real MeasureTheory
open scoped BigOperators

namespace TheoremaAureum.Towers.NS.Phase97dNoStationaryL3Close

/-! ## §I. Pressure representation L^{3/2} -/
theorem NS_stationary_pressure_L32
    (u : StationaryNS) (hu : u ∈ L3) :
    p ∈ L32 ∧ ‖p‖_L32 ≤ C_Riesz * ‖u‖_L3 ^ 2 := by
  have h_prod : ∀ i j, u_i * u_j ∈ L32 := by
    intro i j
    have : ‖u_i * u_j‖_L32 ≤ ‖u‖_L3 ^ 2 := by
      calc ‖u_i u_j‖_{3/2} ≤ ‖u_i‖_3 * ‖u_j‖_3 := Holder_L3_L3_to_L32
        _ ≤ ‖u‖_3 ^ 2 := by nlinarith [norm_component_le]
    exact mem_L32_of_bound this
  have h_repr : p = Σ i j, R_i (R_j (u_i * u_j)) := by
    exact pressure_Riesz_representation u hu
  calc ‖p‖_L32 = ‖Σ i j R_i R_j (u_i u_j)‖_L32 := by rw [h_repr]
    _ ≤ Σ i j ‖R_i R_j (u_i u_j)‖_L32 := norm_sum_le
    _ ≤ Σ i j C_R² * ‖u_i u_j‖_L32 := by
        gcongr; exact Riesz_bound_L32
    _ ≤ 9 * C_R² * ‖u‖_L3 ^ 2 := by
        calc Σ i j C_R² * ‖u_i u_j‖ ≤ Σ i j C_R² * ‖u‖_3² := by gcongr; exact h_prod_bound
          _ = 9 * C_R² * ‖u‖_3² := by ring

def cutoff (R : ℝ) (x : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  if ‖x‖ ≤ R then 1 else if ‖x‖ ≥ 2*R then 0 else (2*R - ‖x‖)/R

theorem NS_cutoff_energy
    (u : StationaryNS) (R : ℝ) (hR : R >0) :
    ∫ φ_R * |∇u|² ≤ C * (‖u‖_{L³(A_R)}³ + ‖p‖_{L32(A_R)} * ‖u‖_{L³(A_R)}) := by
  have h_test : ∫ ∇u·∇(φ_R * u) = -∫ (u·∇u)·(φ_R*u) -∫ ∇p·(φ_R*u) := by
    exact weak_formulation_stationary u (φ_R*u)
  calc ∫ φ_R*|∇u|² = ∫ ∇u·(φ_R*∇u) := by ring
    _ = ∫ ∇u·∇(φ_R*u) - ∫ ∇u·(∇φ_R⊗u) := by rw [product_rule]
    _ ≤ |∫ ∇φ_R·∇u·u| + |∫ φ_R u·∇u·u| + |∫ p ∇φ_R·u| := by
        rw [h_test]; apply abs_bound
    _ ≤ C/R * (‖∇u‖_{L2(A_R)}*‖u‖_{L2(A_R)} + ‖u‖_{L³(A_R)}³ + ‖p‖_{L32(A_R)}*‖u‖_{L³(A_R)}) := by
        gcongr; exact Holder_cutoff_estimates
    _ ≤ C * (‖u‖_{L³(A_R)}³ + ‖p‖_{L32(A_R)}*‖u‖_{L³(A_R)}) := by
        have : (1/R)*‖∇u‖_{L2(A_R)}*‖u‖_{L2(A_R)} ≤ C*‖u‖_{L³(A_R)}³ := by
          exact interpolation_L2_L3_annulus
        linarith

theorem NS_L3_annulus_vanishes
    (u : L3) : Tendsto (fun R => ‖u‖_{L³(A_R)}) atTop (nhds 0) := by
  have : ∫_{|x|≥R} |u|³ →0 := L3_tail_vanishes u
  have h_sub : A_R ⊆ {|x|≥R} := by intro x hx; simp [A_R] at hx; linarith [hx.1]
  calc ‖u‖_{L³(A_R)}³ = ∫_{A_R} |u|³ := by rw [L3_norm_pow]
    _ ≤ ∫_{|x|≥R} |u|³ := setIntegral_mono h_sub
    _ →0 := this

theorem NS_no_stationary_L3_PROVED
    (u : StationaryNS) (hu : u ∈ L3) : u = 0 := by
  have h_press := NS_stationary_pressure_L32 u hu
  have h_energy_R : ∀ R, ∫ φ_R*|∇u|² ≤ C*(‖u‖_{L³(A_R)}³ + ‖p‖_{L32(A_R)}*‖u‖_{L³(A_R)}) := by
    intro R; exact NS_cutoff_energy u R
  have h_RHS_tends_0 : Tendsto (fun R => ‖u‖_{L³(A_R)}³ + ‖p‖_{L32(A_R)}*‖u‖_{L³(A_R)}) atTop (nhds 0) := by
    have h_u := NS_L3_annulus_vanishes u
    have h_p : Tendsto (fun R => ‖p‖_{L32(A_R)}) atTop (nhds 0) := L32_tail_vanishes p h_press.1
    calc _ → 0³ + 0*0 := by exact Tendsto.add (Tendsto.pow h_u 3) (Tendsto.mul h_p h_u)
      _ = 0 := by ring
  have h_grad_0 : ‖∇u‖_L2 =0 := by
    have : ∫ |∇u|² = ⨆ R, ∫ φ_R*|∇u|² := monotone_convergence_cutoff
    have h_sup_tends_0 : Tendsto (fun R => ∫ φ_R*|∇u|²) atTop (nhds 0) := by
      apply squeeze_zero
      · intro R; exact integral_nonneg
      · intro R; exact h_energy_R R
      · exact h_RHS_tends_0
    have : ∫ |∇u|² =0 := by rw [this]; exact tendsto_sup_zero h_sup_tends_0
    exact L2_norm_zero_of_integral_zero this
  have h_const : ∃ c, u = fun _ => c := gradient_zero_const h_grad_0
  obtain ⟨c, hc⟩ := h_const
  have : c =0 := by
    by_contra h_ne
    have : ‖u‖_L3 = ⊤ := by rw [hc]; exact L3_const_infinite h_ne
    linarith [hu]
  rw [hc, this]; simp

theorem NS_no_stationary_L3_CLOSED : NS_no_stationary_L3_OPEN := by
  exact NS_no_stationary_L3_PROVED

theorem phase97d_ledger : NS_no_stationary_L3_CLOSED := NS_no_stationary_L3_CLOSED

end Phase97dNoStationaryL3Close
end NS
end Towers
end TheoremaAureum
