/-
================================================================
Towers / NS / NSStokesAdjoint  —  NS Tower 540, Phase 7A

**Self-adjointness of the Stokes operator in the Fourier model.**

The Stokes operator A = -PΔ (the `‖ξ‖²` Fourier multiplier on div-free
fields) is symmetric for the Sobolev inner product: `⟪A u, ι v⟫_s = ⟪ι u, A v⟫_s`,
where `ι = embed` is the order-lowering inclusion `Hˢ⁺² ↪ Hˢ`.

This closes the `integration_by_parts` NAMED surface from `Energy.lean`.

### Why this is true

On the Fourier side the Stokes operator applies the REAL scalar
`stokesSymbol ξ = ‖ξ‖²` componentwise. For a real scalar `r : ℝ`:
  `⟨r·a, b⟩_ℂ³ = conj(r) · ⟨a, b⟩_ℂ³ = r · ⟨a, b⟩_ℂ³ = ⟨a, r·b⟩_ℂ³`
(since `conj(r) = r` for real `r`). Integrating over `ξ` w.r.t. `μ_s`
gives the claimed identity.

### What is proved (classical trio, 0 sorry)

  * `inner_Hdiv_eq` — inner product on `Hdiv_free s` equals the ambient
    `Lp Val 2 (mu s)` inner product (definitional equality).
  * `stokes_op_adjoint` — `⟪A u, ι v⟫_s = ⟪ι u, A v⟫_s`.
  * `integration_by_parts_proved` — closes `Energy.integration_by_parts`.

### Honest scope

  * Proves ONLY the self-adjointness of the Fourier multiplier operator.
    This justifies the `integration_by_parts` identity in the Fourier model;
    it does NOT prove an NS existence or regularity result.
  * NS tower stays `Status: Open`. Surface #1/#2 stay OPEN. No Clay claim.
================================================================
-/

import Towers.NS.Energy
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory
open scoped BigOperators ENNReal
open TheoremaAureum.Towers.NS.FunctionSpaces
open TheoremaAureum.Towers.NS.Stokes
open TheoremaAureum.Towers.NS.Energy

namespace TheoremaAureum
namespace Towers
namespace NS
namespace StokesAdjoint

variable {s : ℝ}

/-- The inner product on `Hdiv_free s = ↥(divFreeSubmodule s)` is the
    restriction of the ambient `Lp Val 2 (mu s)` inner product. For any
    submodule `K` of a Hilbert space `H`, the subtype inner product is
    defined as `inner x y := inner (x : H) (y : H)` (definitional). -/
theorem inner_Hdiv_eq (x y : Hdiv_free s) :
    @inner ℂ (Hdiv_free s) _ x y =
    @inner ℂ (Lp Val 2 (mu s)) _ (x : Lp Val 2 (mu s)) (y : Lp Val 2 (mu s)) :=
  rfl

/-- **Stokes operator self-adjointness (Phase 7A, trio-clean).**
    The Fourier-side Stokes operator `A = stokes_op s` is symmetric:
    `⟪A u, ι v⟫_s = ⟪ι u, A v⟫_s` where `ι = embed h` (the continuous
    order-lowering inclusion `Hˢ⁺² ↪ Hˢ`).

    Proof: the `Lp Val 2 (mu s)` inner product is an integral of pointwise
    inner products (`L2.inner_def`). The Stokes operator acts by multiplying
    Fourier components by the REAL symbol `stokesSymbol ξ = ‖ξ‖²`. For a
    real scalar `r`, `inner (r • a) b = conj r * inner a b = r * inner a b =
    inner a (r • b)` (`inner_smul_left` + `Complex.conj_ofReal`). Applying
    `integral_congr_ae` gives the claimed identity.

    `#print axioms stokes_op_adjoint` = classical trio only. -/
theorem stokes_op_adjoint (u v : Hdiv_free (s + 2)) :
    @inner ℂ (Hdiv_free s) _ (stokes_op s u) (@embed _ _ (by linarith) v) =
    @inner ℂ (Hdiv_free s) _ (@embed _ _ (by linarith) u) (stokes_op s v) := by
  -- Reduce to the ambient Lp Val 2 (mu s) inner product (definitionally equal)
  rw [inner_Hdiv_eq, inner_Hdiv_eq]
  -- Expand both sides using L2.inner_def: ⟪f, g⟫ = ∫ ⟨f ξ, g ξ⟩ dμ_s
  rw [L2.inner_def, L2.inner_def]
  -- Show integrals are equal by an a.e. pointwise argument
  apply integral_congr_ae
  -- Obtain a.e. representatives via coeFn lemmas:
  --   stokes_op s u ~ stokesSymbol • û   (coeFn_stokes_mult)
  --   embed h v     ~ v̂                   (coeFn_inclLp)
  have hAu : ((stokes_op s u : Hdiv_free s) : Lp Val 2 (mu s)) =ᵐ[mu s]
      fun ξ => stokesSymbol ξ • (u : Lp Val 2 (mu (s + 2))) ξ := by
    have h1 := coeFn_stokes_mult s (u : Lp Val 2 (mu (s + 2)))
    filter_upwards [h1] with ξ hξ
    simp only [stokes_op, ContinuousLinearMap.codRestrict_apply,
      ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
    exact hξ
  have hEv : ((@embed _ _ (by linarith : s ≤ s + 2) v : Hdiv_free s) : Lp Val 2 (mu s)) =ᵐ[mu s]
      (v : Lp Val 2 (mu (s + 2))) :=
    coeFn_inclLp _ _
  have hEu : ((@embed _ _ (by linarith : s ≤ s + 2) u : Hdiv_free s) : Lp Val 2 (mu s)) =ᵐ[mu s]
      (u : Lp Val 2 (mu (s + 2))) :=
    coeFn_inclLp _ _
  have hAv : ((stokes_op s v : Hdiv_free s) : Lp Val 2 (mu s)) =ᵐ[mu s]
      fun ξ => stokesSymbol ξ • (v : Lp Val 2 (mu (s + 2))) ξ := by
    have h1 := coeFn_stokes_mult s (v : Lp Val 2 (mu (s + 2)))
    filter_upwards [h1] with ξ hξ
    simp only [stokes_op, ContinuousLinearMap.codRestrict_apply,
      ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
    exact hξ
  filter_upwards [hAu, hEv, hEu, hAv] with ξ hau hev heu hav
  -- Rewrite pointwise using a.e. representatives
  rw [hau, hev, heu, hav]
  -- inner_smul_left: ⟨r • a, b⟩ = conj(r) * ⟨a, b⟩
  -- inner_smul_right: ⟨a, r • b⟩ = r * ⟨a, b⟩
  -- For real r: conj(r) = r, so both sides equal r * ⟨a, b⟩
  rw [inner_smul_left, inner_smul_right]
  congr 1
  -- stokesSymbol ξ = ↑(‖ξ‖² : ℝ) is real: starRingEnd ℂ (↑r) = ↑r
  simp [stokesSymbol, map_ofNat, Complex.conj_ofReal]

/-- **Closes the `Energy.integration_by_parts` surface (Phase 7A).**
    The Stokes operator is self-adjoint in the Fourier model, so the
    integration-by-parts identity `⟪A u, ι v⟫ = ⟪ι u, A v⟫` holds.
    This is a GENUINE result (not a named placeholder): the proof is
    complete, classical trio, 0 sorry.

    Combined with `Energy.energy_inequality`, this establishes that the
    Leray–Hopf energy balance `hbal` is a consequence of the genuine
    model structure (not an unproved axiom). -/
theorem integration_by_parts_proved :
    @Energy.integration_by_parts s :=
  stokes_op_adjoint

end StokesAdjoint
end NS
end Towers
end TheoremaAureum
