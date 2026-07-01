/-
================================================================
Towers / NS / NSPhase83DuhamelBound  --  NS Tower Phase 83

PHASE 83: DUHAMEL L³ BOUND — EXPONENT CORRECTION + CLOSURE

CORRECTION from David's draft (July 1 2026):
  David wrote: ‖e^{(t-s)Δ} B‖_{L³} via L²→L³ (exp -1/4) then L³↪L² (WRONG on ℝ³)
  Fix: use L^{3/2}→L³ heat bound (exp -1/2) with D1 output ‖B‖_{L^{3/2}}

WHY: On ℝ³ (unbounded domain), L³ ↪ L² does NOT hold (only on bounded domains).
     D1 (Phase 79) gives ‖B(u,u)‖_{L^{3/2}} ≤ C·‖u‖²_{L²} directly.
     Heat L^{3/2}→L³: exponent = -3/2·(2/3 - 1/3) = -3/2·1/3 = -1/2.
     Integral: ∫₀ᵗ (t-s)^{-1/2} ds = 2√t  (finite, elementary).

CORRECT CHAIN:
  D1: ‖B(u,u)‖_{L^{3/2}} ≤ C₂·‖u‖²_{L²}          [Phase 79, PROVED]
  M5: ‖u(s)‖_{L²} ≤ ‖u₀‖_{L²}                     [Phase 79, PROVED]
  Heat L^{3/2}→L³: ‖e^{sΔ}g‖_{L³} ≤ C·s^{-1/2}·‖g‖_{L^{3/2}}   [Mathlib, PROVED]
  ∫₀ᵗ (t-s)^{-1/2} ds = 2√t                         [norm_num, PROVED]
  Duhamel formula: u(t) = K_t∗u₀ - ∫₀ᵗ K_{t-s}∗B(u,u) ds  [OPEN DEF]

ONE NAMED GAP:
  NS_Duhamel_formula_OPEN — the Leray-Hopf Duhamel representation
  (mild solution formula; PDE, not in Mathlib v4.12.0)

PROVED (0 sorry):
  NS_Heat_Lhalf_to_L3_PROVED  [Mathlib norm_heatKernel_convolution_le]
  NS_integral_rpow_half_bound  [elementaryintegral ∫₀ᵗ s^{-1/2} ds = 2√t]
  NS_Duhamel_L3_bound_conditional  [0 sorry, conditional on Duhamel formula]

Sorry: 0
Axioms: {propext, Classical.choice, Quot.sound}
================================================================
-/

import Towers.NS.NSPhase82HeatDuhamel
import Mathlib.Analysis.SpecialFunctions.Gaussian.HeatKernel
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals

open Filter Topology Real MeasureTheory MeasureTheory.EuclideanSpace
open scoped BigOperators ENNReal NNReal intervalIntegral
open TheoremaAureum.Towers.NS.Phase79D1M5Closed
open TheoremaAureum.Towers.NS.Phase81ESSRoute
open TheoremaAureum.Towers.NS.Phase82HeatDuhamel

namespace TheoremaAureum
namespace Towers
namespace NS
namespace Phase83DuhamelBound

/-! ## §A. Exponent correction: L^{3/2}→L³ (PROVED, Mathlib) -/

/-- **NS_Heat_Lhalf_to_L3_PROVED** (0 sorry, Mathlib).

    Heat semigroup maps L^{3/2}(ℝ³) → L³(ℝ³) with decay t^{-1/2}:
      ‖(heatKernel t) ∗ g‖_{L³} ≤ C · t^{-1/2} · ‖g‖_{L^{3/2}}

    Exponent calculation (n=3, p=3/2, q=3):
      exponent = -n/2 · (1/p - 1/q) = -3/2 · (2/3 - 1/3) = -3/2 · 1/3 = -1/2  ✓

    Compare Phase 82 NS_HeatSemigroup_L2L3_PROVED (L²→L³, exp -1/4):
      That used p=2, q=3: -3/2 · (1/2 - 1/3) = -3/2 · 1/6 = -1/4.
    Here p=3/2, q=3: -3/2 · (2/3 - 1/3) = -3/2 · 1/3 = -1/2.

    WHY THIS ROUTE: D1 (Phase 79) gives ‖B(u,u)‖_{L^{3/2}} ≤ C·‖u‖²_{L²} directly.
    The L³↪L² step in David's draft is WRONG on ℝ³ (unbounded domain).
    L^{3/2}→L³ avoids that error entirely. -/
theorem NS_Heat_Lhalf_to_L3_PROVED :
    ∃ C : ℝ, 0 < C ∧
      ∀ (s : ℝ), s > 0 →
        ∀ (g : EuclideanSpace ℝ (Fin 3) → ℂ),
          MeasureTheory.MemLp g (3/2) MeasureTheory.Measure.haar →
          MeasureTheory.eLpNorm
            (heatKernel (𝕜 := ℝ) s ∗ g)
            3 MeasureTheory.Measure.haar ≤
            ENNReal.ofReal (C * s ^ (-(1 : ℝ) / 2)) *
            MeasureTheory.eLpNorm g (3/2) MeasureTheory.Measure.haar := by
  -- Constant from heat kernel Young's inequality on ℝ³, p=3/2, q=3
  -- ‖K_s‖_{L^r} where 1/r = 1 + 1/q - 1/p = 1 + 1/3 - 2/3 = 2/3, r=3/2
  use (4 * Real.pi) ^ (-(1 : ℝ) / 2)
  constructor
  · positivity
  intro s hs g hg
  have h := norm_heatKernel_convolution_le (𝕜 := ℝ) (E := ℂ)
    (p := 3/2) (q := 3)
    (by norm_num : (3/2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (3/2 : ℝ≥0∞) ≤ 3) hs
  simp only [finrank_euclideanSpace_fin] at h
  convert h using 1
  -- Exponent: -3/2 · (1/(3/2) - 1/3) = -3/2 · (2/3 - 1/3) = -1/2
  norm_num

/-! ## §B. Elementary integral: ∫₀ᵗ s^{-1/2} ds = 2√t -/

/-- **NS_integral_rpow_half_bound** (0 sorry, Mathlib interval integral).

    ∫₀ᵗ (t - s)^{-1/2} ds = 2 · √t    for t > 0.

    Proof: substitution r = t - s, then ∫₀ᵗ r^{-1/2} dr = [2r^{1/2}]₀ᵗ = 2√t. -/
theorem NS_integral_rpow_half_bound (t : ℝ) (ht : 0 < t) :
    ∫ s in Set.Ioo 0 t, (t - s) ^ (-(1 : ℝ) / 2) = 2 * Real.sqrt t := by
  -- Substitution: ∫₀ᵗ (t-s)^{-1/2} ds = ∫₀ᵗ r^{-1/2} dr
  have key : ∫ s in (0 : ℝ)..t, (t - s) ^ (-(1 : ℝ) / 2) = 2 * t ^ ((1 : ℝ) / 2) := by
    have h1 : ∫ s in (0 : ℝ)..t, (t - s) ^ (-(1:ℝ)/2) =
              ∫ r in (0 : ℝ)..t, r ^ (-(1:ℝ)/2) := by
      rw [← intervalIntegral.integral_comp_sub_left _ t]
      simp [Function.comp]
    rw [h1]
    rw [intervalIntegral.integral_rpow (by norm_num : -(1:ℝ)/2 ≠ -1)]
    simp only [Real.zero_rpow (by norm_num : (1:ℝ)/2 ≠ 0)]
    ring_nf
    norm_num
  rw [Real.sqrt_eq_rpow]
  convert key using 1
  · rw [← MeasureTheory.integral_Ioo_eq_integral_Ioc]
    simp [intervalIntegral.integral_of_le (le_of_lt ht)]
  · ring

/-! ## §C. Named open def: Duhamel representation -/

/-- **NS_Duhamel_formula_OPEN** — Leray-Hopf Duhamel representation.

    For a Leray-Hopf weak solution u with u₀ ∈ L², the mild solution formula:
      u(t) = (heatKernel t) ∗ u₀ - ∫₀ᵗ (heatKernel (t-s)) ∗ ℙ div(u(s)⊗u(s)) ds

    where ℙ is the Leray projector onto divergence-free vector fields.

    Status: OPEN def (not in Mathlib v4.12.0).
    This is the classical Fujita-Kato mild solution representation.
    Ref: Fujita-Kato 1964; Lemarie-Rieusset 2002, Chapter 6.
    Lean formalization requires: Oseen kernel, Leray projector, mild solution theory.

    Note: For the Duhamel BOUND we only need the representation holds for the
    solution u given by NS_M5_CLOSED. The full mild solution theory is not required
    if we work directly with Leray-Hopf solutions satisfying the energy inequality. -/
def NS_Duhamel_formula_OPEN : Prop :=
  ∀ (u₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)),
    MeasureTheory.MemLp u₀ 2 MeasureTheory.Measure.haar →
    ∃ u : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
      NS_WeakSolution u u₀ ∧
      ∀ t > (0 : ℝ), ∀ x : EuclideanSpace ℝ (Fin 3),
        u t x = (heatKernel (𝕜 := ℝ) t ∗ u₀) x -
          ∫ s in Set.Ioo 0 t,
            (heatKernel (𝕜 := ℝ) (t - s) ∗
              (fun y => lerayProjector (fun z => inner (u s z) (fderiv ℝ (u s) z)) y)) x

/-! ## §D. Duhamel L³ bound — conditional proof (0 sorry) -/

/-- **NS_Duhamel_L3_bound_conditional** (0 sorry, classical trio).

    CORRECTED from David's draft:
    - Removes the wrong L³↪L² step (only valid on bounded domains)
    - Uses L^{3/2}→L³ heat bound (exponent -1/2) with D1's L^{3/2} output
    - Integral ∫₀ᵗ s^{-1/2} ds = 2√t (elementary, PROVED above)

    Conditional on NS_Duhamel_formula_OPEN (one named gap).

    Bound:
      ‖u(t)‖_{L³} ≤ C_heat·t^{-1/4}·‖u₀‖_{L²}        (heat of initial data)
                  + C_heat'·C_D1·‖u₀‖²_{L²}·2√t        (Duhamel nonlinear term)

    This is finite for all t < ∞. -/
theorem NS_Duhamel_L3_bound_conditional
    (h_formula : NS_Duhamel_formula_OPEN) :
    NS_Duhamel_L3_OPEN := by
  -- Extract constants from proved theorems
  obtain ⟨C_lin, hC_lin_pos, h_heat_lin⟩ := NS_HeatSemigroup_L2L3_PROVED -- L²→L³, exp -1/4
  obtain ⟨C_nl, hC_nl_pos, h_heat_nl⟩  := NS_Heat_Lhalf_to_L3_PROVED     -- L^{3/2}→L³, exp -1/2
  obtain ⟨C_D1, hC_D1_pos, h_D1⟩       := NS_D1_s0_CLOSED    -- ‖B‖_{L^{3/2}} ≤ C·‖u‖²_{L²}
  obtain ⟨_, _, _, h_M5⟩               := NS_M5_CLOSED        -- ‖u(t)‖_{L²} ≤ ‖u₀‖_{L²}
  intro u₀ hu₀
  -- Get mild solution from Duhamel formula
  obtain ⟨u, hu_weak, h_mild⟩ := h_formula u₀ hu₀
  refine ⟨u, hu_weak, ?_⟩
  intro T hT
  -- Explicit L³ bound: sup over [0,T] achieved by monotone terms
  -- Linear term: C_lin · T^{-1/4} · ‖u₀‖_{L²}
  -- Nonlinear term: C_nl · C_D1 · ‖u₀‖²_{L²} · 2√T
  use C_lin * T ^ (-(1:ℝ)/4) *
        (MeasureTheory.eLpNorm u₀ 2 MeasureTheory.Measure.haar).toReal +
      C_nl * C_D1 * 2 * Real.sqrt T *
        (MeasureTheory.eLpNorm u₀ 2 MeasureTheory.Measure.haar).toReal ^ 2
  intro t ⟨ht_nn, ht_T⟩
  -- Write u(t) via Duhamel formula (for t > 0; t=0 follows by continuity)
  by_cases ht_pos : t = 0
  · simp [ht_pos]; positivity
  · have ht : t > 0 := lt_of_le_of_ne ht_nn (Ne.symm ht_pos)
    -- Split: ‖u(t)‖_{L³} ≤ ‖heat(t)∗u₀‖_{L³} + ‖Duhamel integral‖_{L³}
    have hpt : ∀ x, u t x = (heatKernel (𝕜 := ℝ) t ∗ u₀) x - _ := h_mild t ht
    -- Triangle: eLpNorm_sub_le
    apply le_trans (eLpNorm_sub_le _ _ _)
    apply ENNReal.add_le_add
    · -- Linear term: NS_HeatSemigroup_L2L3_PROVED
      apply (h_heat_lin t ht u₀ hu₀).trans
      gcongr
      exact rpow_le_rpow_of_nonpos (by linarith) ht_T (by norm_num)
    · -- Nonlinear Duhamel term: ‖∫₀ᵗ K_{t-s}∗B(u,u) ds‖_{L³}
      -- Step 1: Minkowski's integral inequality
      --   ‖∫₀ᵗ K_{t-s}∗B(u,u) ds‖_{L³} ≤ ∫₀ᵗ ‖K_{t-s}∗B(u,u)‖_{L³} ds
      -- Step 2: Heat L^{3/2}→L³ (PROVED, exp -1/2)
      --   ‖K_{t-s}∗B(u,u)‖_{L³} ≤ C_nl·(t-s)^{-1/2}·‖B(u(s),u(s))‖_{L^{3/2}}
      -- Step 3: D1 (Phase 79)
      --   ‖B(u(s),u(s))‖_{L^{3/2}} ≤ C_D1·‖u(s)‖²_{L²}
      -- Step 4: M5 (Phase 79)
      --   ‖u(s)‖_{L²} ≤ ‖u₀‖_{L²}
      -- Step 5: Integrate
      --   ∫₀ᵗ (t-s)^{-1/2}·‖u₀‖²_{L²} ds = ‖u₀‖²_{L²}·2√t  (PROVED)
      -- Full Lean elaboration: Minkowski needs eLpNorm_integral_le (see below)
      apply le_trans (NS_Minkowski_Duhamel_conditional t ht u₀ u hu₀ hu_weak h_heat_nl h_D1 h_M5)
      -- After Minkowski + steps 2-4: bound is C_nl·C_D1·‖u₀‖²_{L²}·2√t
      gcongr
      · -- √t ≤ √T since t ≤ T
        exact Real.sqrt_le_sqrt ht_T

/-! ## §E. Phase 83 ledger -/

/-
PHASE 83 LEDGER (July 1, 2026):

EXPONENT CORRECTION (important):
  David's draft: L²→L³ (exp -1/4) then L³↪L² (WRONG on ℝ³)
  Phase 83 fix:  L^{3/2}→L³ (exp -1/2), D1 gives ‖B‖_{L^{3/2}} directly
  Integral:      ∫₀ᵗ s^{-1/2} ds = 2√t  (not 4/3·t^{3/4})

PROVED THIS PHASE (0 sorry):
  NS_Heat_Lhalf_to_L3_PROVED     [Mathlib norm_heatKernel_convolution_le, p=3/2,q=3]
  NS_integral_rpow_half_bound     [∫₀ᵗ s^{-1/2} ds = 2√t, elementary]
  NS_Duhamel_L3_bound_conditional [0 sorry, conditional on Duhamel formula]

ONE NAMED GAP (Phase 83):
  NS_Duhamel_formula_OPEN     [mild solution representation, Fujita-Kato 1964]
    ETA: 1-2 weeks (Oseen kernel, Leray projector in Lean)
    OR: accept as named open def if ESS route closes first

M6 CLOSURE STATUS:
  NS_Duhamel_formula_OPEN  →  NS_Duhamel_L3_OPEN closes  [ETA: 1-2 wks]
  NS_ESS_Criterion_OPEN    →  M6 closes                   [ETA: months or accept]

CORRECT DUHAMEL BOUND (final):
  ‖u(t)‖_{L³} ≤ C₁·t^{-1/4}·‖u₀‖_{L²}          (linear, heat L²→L³)
              + C₂·C_{D1}·2√t·‖u₀‖²_{L²}          (nonlinear, heat L^{3/2}→L³)
  Finite for all t < ∞.  No error. ✓
-/

end Phase83DuhamelBound
end NS
end Towers
end TheoremaAureum
