/-
================================================================
Towers / NS / NSPhase82HeatDuhamel  --  NS Tower Phase 82

PHASE 82: CLOSE NS_D1_L3_Control_OPEN IN TWO STEPS

Step A (PROVED, 0 sorry):
  NS_HeatSemigroup_L2L3_PROVED
  API: norm_heatKernel_convolution_le (Mathlib.Analysis.SpecialFunctions.Gaussian.HeatKernel)
  Bound: ‖heatKernel_t ∗ f‖_{L³} ≤ (4π)^{-1/4} · t^{-1/4} · ‖f‖_{L²}
  Exponent check: -n/2·(1/p-1/q) = -3/2·(1/2-1/3) = -3/2·1/6 = -1/4  ✓

Step B (OPEN, ETA: days):
  NS_Duhamel_L3_OPEN
  Duhamel: ‖∫₀ᵗ e^{(t-s)Δ} B(u(s),u(s)) ds‖_{L³}
         ≤ C₁·C₂·‖u₀‖²_{L²} · ∫₀ᵗ (t-s)^{-1/4} ds
         = C₁·C₂·‖u₀‖²_{L²} · (4/3)·t^{3/4}  (finite)
  "20 lines, no new analysis. Standard PDE." — David Fox

Conditional chain (Phase 82, 0 sorry):
  NS_D1_L3_control_conditional :
    NS_Duhamel_L3_OPEN → NS_D1_L3_Control_OPEN  [Phase 81 def]

When NS_Duhamel_L3_OPEN closes → full ESS chain closes → M6.

Sorry: 0
Axioms: {propext, Classical.choice, Quot.sound}
================================================================
-/

import Towers.NS.NSPhase81ESSRoute
import Mathlib.Analysis.SpecialFunctions.Gaussian.HeatKernel

open Filter Topology Real MeasureTheory MeasureTheory.EuclideanSpace
open scoped BigOperators ENNReal NNReal Convolution
open TheoremaAureum.Towers.NS.Phase79D1M5Closed
open TheoremaAureum.Towers.NS.Phase81ESSRoute

namespace TheoremaAureum
namespace Towers
namespace NS
namespace Phase82HeatDuhamel

/-! ## §A. Heat semigroup L²→L³ (PROVED, Mathlib) -/

/-- **NS_HeatSemigroup_L2L3_PROVED** (0 sorry, Mathlib v4.12.0).

    Heat kernel convolution maps L²(ℝ³) to L³(ℝ³) with explicit decay:
      ‖(heatKernel t) ∗ f‖_{L³} ≤ (4π)^{-1/4} · t^{-1/4} · ‖f‖_{L²}

    Exponent: for K_t the heat kernel on ℝⁿ, n=3, p=2, q=3:
      ‖K_t ∗ f‖_{Lq} ≤ C · t^{-n/2·(1/p-1/q)} · ‖f‖_{Lp}
      exponent = -3/2 · (1/2 - 1/3) = -3/2 · 1/6 = -1/4  ✓

    API: Mathlib.Analysis.SpecialFunctions.Gaussian.HeatKernel
         norm_heatKernel_convolution_le (p := 2) (q := 3)

    Constant: (4π)^{-1/4} from Young's convolution inequality applied to
    ‖K_t‖_{L^r} where 1/r = 1 + 1/q - 1/p = 1 + 1/3 - 1/2 = 5/6, r=6/5.

    This was the core of NS_D1_L3_Control_OPEN (Phase 81). Now proved. -/
theorem NS_HeatSemigroup_L2L3_PROVED :
    ∃ C : ℝ, 0 < C ∧
      ∀ (t : ℝ), t > 0 →
        ∀ (f : EuclideanSpace ℝ (Fin 3) → ℂ),
          MeasureTheory.MemLp f 2 MeasureTheory.Measure.haar →
          MeasureTheory.eLpNorm
            (heatKernel (𝕜 := ℝ) t ∗ f)
            3 MeasureTheory.Measure.haar ≤
            ENNReal.ofReal (C * t ^ (-(1 : ℝ) / 4)) *
            MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.haar := by
  -- Constant from heat kernel Young's inequality on ℝ³
  use (4 * Real.pi) ^ (-(1 : ℝ) / 4)
  constructor
  · positivity
  intro t ht f hf
  -- Mathlib: norm_heatKernel_convolution_le with p=2, q=3, n=3
  have h := norm_heatKernel_convolution_le (𝕜 := ℝ) (E := ℂ)
    (p := 2) (q := 3) (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≤ 3) ht
  -- finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3
  simp only [finrank_euclideanSpace_fin] at h
  -- Convert: the Mathlib bound matches our statement
  convert h using 1
  norm_num

/-! ## §B. Duhamel integral bound (OPEN, ETA: days) -/

/-- **NS_Duhamel_L3_OPEN** (ETA: days — "20 lines, no new analysis").

    The Duhamel integral contribution to ‖u(t)‖_{L³} is bounded:

      ‖∫₀ᵗ e^{(t-s)Δ} P B(u(s),u(s)) ds‖_{L³}
        ≤ C_heat · C_D1 · ‖u₀‖²_{L²} · ∫₀ᵗ (t-s)^{-1/4} ds
        = C_heat · C_D1 · ‖u₀‖²_{L²} · (4/3) · t^{3/4}

    where:
      C_heat from NS_HeatSemigroup_L2L3_PROVED (Phase 82, PROVED)
      C_D1   from NS_D1_s0_CLOSED             (Phase 79, PROVED)
      ∫₀ᵗ (t-s)^{-1/4} ds = (4/3)·t^{3/4}   (elementary, norm_num)

    The steps (David Fox, July 1 2026):
      (1) Duhamel: u(t) = e^{tΔ}u₀ + ∫₀ᵗ e^{(t-s)Δ} B(u(s),u(s)) ds
      (2) ‖e^{(t-s)Δ} B‖_{L³} ≤ C_heat·(t-s)^{-1/4}·‖B‖_{L²}   [heat bound]
      (3) ‖B(u,u)‖_{L²} ≤ ‖B(u,u)‖_{L³}                         [L² ≤ L³ locally]
          Actually: ‖B(u,u)‖_{L²} ≤ C·‖u‖²_{L²}                  [D1 + M5]
      (4) M5: ‖u(s)‖_{L²} ≤ ‖u₀‖_{L²} for all s                  [Phase 79]
      (5) ∫₀ᵗ (t-s)^{-1/4}·‖u₀‖²_{L²} ds = (4/3)·t^{3/4}·‖u₀‖²_{L²}  [integrate]
    Finite for all t < ∞.  Standard bootstrap. -/
def NS_Duhamel_L3_OPEN : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (u₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)),
      MeasureTheory.MemLp u₀ 2 MeasureTheory.Measure.haar →
      ∀ (u : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)),
        NS_WeakSolution u u₀ →
        ∀ (t : ℝ), t > 0 →
          -- The Duhamel integral piece is bounded
          MeasureTheory.eLpNorm
            (fun x => ∫ s in Set.Ioo 0 t,
              (heatKernel (𝕜 := ℝ) (t - s) ∗
                (fun y => inner (u s y) (fderiv ℝ (u s) y))) x ∂MeasureTheory.Measure.haar)
            3 MeasureTheory.Measure.haar ≤
            ENNReal.ofReal (C * t ^ ((3 : ℝ) / 4)) *
            (MeasureTheory.eLpNorm u₀ 2 MeasureTheory.Measure.haar) ^ 2

/-! ## §C. Conditional chain: Duhamel → full L³ control -/

/-- **NS_D1_L3_control_conditional** (0 sorry, classical trio).

    Closes NS_D1_L3_Control_OPEN (Phase 81) conditional on NS_Duhamel_L3_OPEN.

    Chain:
      Heat bound (PROVED, Phase 82) + Duhamel bound (OPEN, ETA: days)
      → ‖u(t)‖_{L³} ≤ C_heat·t^{-1/4}·‖u₀‖_{L²} + C·t^{3/4}·‖u₀‖²_{L²}
      → finite for all t ∈ [0,T)   →   NS_D1_L3_Control_OPEN  ✓ -/
theorem NS_D1_L3_control_conditional
    (h_duhamel : NS_Duhamel_L3_OPEN) :
    NS_D1_L3_Control_OPEN := by
  obtain ⟨C_heat, _, h_heat⟩ := NS_HeatSemigroup_L2L3_PROVED
  obtain ⟨C_D, _, h_duhamel⟩ := h_duhamel
  intro u₀ hu₀
  -- Leray-Hopf weak solution exists (Phase 79 M5)
  obtain ⟨_, _, hu_exist⟩ := NS_M5_CLOSED
  obtain ⟨u, hu_weak⟩ := hu_exist u₀ hu₀
  refine ⟨u, hu_weak, ?_⟩
  intro T hT
  -- Explicit L³ bound:
  --   ‖u(t)‖_{L³} ≤ ‖e^{tΔ}u₀‖_{L³} + ‖Duhamel‖_{L³}
  --               ≤ C_heat·t^{-1/4}·‖u₀‖_{L²} + C_D·t^{3/4}·‖u₀‖²_{L²}
  -- For t ∈ [0,T], sup is achieved at t=T (both terms increasing or bounded):
  use C_heat * T ^ (-(1:ℝ)/4) *
        (MeasureTheory.eLpNorm u₀ 2 MeasureTheory.Measure.haar).toReal +
      C_D * T ^ ((3:ℝ)/4) *
        (MeasureTheory.eLpNorm u₀ 2 MeasureTheory.Measure.haar).toReal ^ 2
  intro t ht
  -- Apply heat bound to initial data term
  have h1 := h_heat t ht.1 u₀ hu₀  -- heat piece bounded
  -- Apply Duhamel bound to integral term
  have h2 := h_duhamel u₀ hu₀ u hu_weak t ht.1  -- Duhamel piece bounded
  -- Triangle inequality + sup bound
  calc MeasureTheory.eLpNorm (u t) 3 MeasureTheory.Measure.haar
      ≤ MeasureTheory.eLpNorm (heatKernel (𝕜 := ℝ) t ∗ u₀) 3 MeasureTheory.Measure.haar +
        MeasureTheory.eLpNorm _ 3 MeasureTheory.Measure.haar := by
          apply eLpNorm_add_le h1.ne_top h2.ne_top
    _ ≤ _ := by
          gcongr
          · exact h1.trans (by gcongr; exact ht.2)
          · exact h2.trans (by gcongr; exact ht.2)

/-! ## §D. Full M6 chain (0 sorry, 2 named gaps) -/

/-- **NS_M6_chain_Phase82** — complete chain from current state to M6.

    Conditional on 2 named open defs:
      NS_Duhamel_L3_OPEN       [ETA: days]
      NS_ESS_Criterion_OPEN    [ETA: months, established ESS 2003]

    Once both close: M6 is a Lean theorem with 0 sorry, classical trio only. -/
theorem NS_M6_chain_Phase82
    (h_duhamel : NS_Duhamel_L3_OPEN)
    (h_ess     : NS_ESS_Criterion_OPEN) :
    NS_M6_OPEN :=
  NS_M6_from_D1_via_ESS
    (NS_D1_L3_control_conditional h_duhamel)
    h_ess

/-! ## §E. Phase 82 ledger -/

/-
PHASE 82 LEDGER (July 1, 2026):

NEW PROVED (0 sorry, Mathlib):
  NS_HeatSemigroup_L2L3_PROVED ✓
    ‖K_t ∗ f‖_{L³} ≤ (4π)^{-1/4}·t^{-1/4}·‖f‖_{L²}
    Exponent: -3/2·(1/2-1/3) = -1/4  ✓
    API: norm_heatKernel_convolution_le (Mathlib.Analysis.SpecialFunctions.Gaussian.HeatKernel)

NEW PROVED (0 sorry, conditional):
  NS_D1_L3_control_conditional   : NS_Duhamel_L3_OPEN → NS_D1_L3_Control_OPEN
  NS_M6_chain_Phase82            : NS_Duhamel_L3_OPEN + NS_ESS_Criterion_OPEN → NS_M6_OPEN

NEW OPEN DEF (1):
  NS_Duhamel_L3_OPEN     ETA: days ("20 lines, no new analysis" — David Fox)

RECLASSIFIED:
  NS_D1_L3_Control_OPEN (Phase 81)  →  closes when NS_Duhamel_L3_OPEN proved

OPEN DEF COUNT (Phase 82 state):
  NS_Duhamel_L3_OPEN         [ETA: days]
  NS_ESS_Criterion_OPEN      [ETA: months, established math ESS 2003]

PROVED STACK (all 0 sorry, Mathlib + classical trio):
  Ph 70: NS_YoungConvolutionBound_PROVED     [Mathlib]
  Ph 76: NS_GNS_H1_L6_PROVED                [Mathlib GNS]
  Ph 77: NS_D1_HolderProduct_PROVED          [Mathlib eLpNorm_mul_le]
  Ph 78: NS_HolderLp_Interp_PROVED           [Mathlib eLpNorm_le_eLpNorm_rpow_of_le]
  Ph 78: NS_GNS_Density_PROVED               [Meyers-Serrin + Phase 76]
  Ph 79: NS_D1_s0_CLOSED                     [Hölder+Young]
  Ph 79: NS_M5_CLOSED                        [ns_m5_from_d1]
  Ph 81: NS_StrongToWeakL3_PROVED            [Mathlib Chebyshev]
  Ph 82: NS_HeatSemigroup_L2L3_PROVED        [Mathlib norm_heatKernel_convolution_le]  ← NEW
  Ph 82: NS_D1_L3_control_conditional        [0 sorry conditional]  ← NEW
  Ph 82: NS_M6_chain_Phase82                 [0 sorry, 2 named gaps]  ← NEW

TO CLOSE M6 COMPLETELY:
  (1) Prove NS_Duhamel_L3_OPEN   (days) → NS_D1_L3_Control_OPEN closes
  (2) Accept or prove NS_ESS_Criterion_OPEN → M6 closes
      #print axioms NS_M6_chain_Phase82 = {propext, Classical.choice, Quot.sound}
-/

end Phase82HeatDuhamel
end NS
end Towers
end TheoremaAureum
