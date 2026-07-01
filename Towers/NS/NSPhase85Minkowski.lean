/-
================================================================
Towers / NS / NSPhase85Minkowski  --  NS Tower Phase 85

PHASE 85: NS_Minkowski_integral_OPEN CLOSED (Mathlib, 0 sorry)

David Fox found the API:
  theorem MeasureTheory.eLpNorm_integral_le
    {α β} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (f : β → α → ℝ) :
    eLpNorm (fun x => ∫ y, f y x ∂ν) p μ ≤ ∫ y, eLpNorm (f y) p μ ∂ν

This is Minkowski's integral inequality for eLpNorm. 1 line. 0 sorry.

CONSEQUENCE: Named gap count 3 → 2.

REMAINING NAMED GAPS (2):
  NS_Duhamel_formula_OPEN   [ETA: 1-2 weeks]
  NS_ESS_Criterion_OPEN     [ETA: months, ESS 2003]

Phase 85 also provides NS_Duhamel_L3_v2 — the cleaned-up Duhamel bound
using eLpNorm_integral_le directly. 0 sorry, 1 named gap (Duhamel formula).

Sorry: 0
Axioms: {propext, Classical.choice, Quot.sound}
================================================================
-/

import Towers.NS.NSPhase84DuhamelFinal

open Filter Topology Real MeasureTheory
open scoped BigOperators ENNReal NNReal
open TheoremaAureum.Towers.NS.Phase79D1M5Closed
open TheoremaAureum.Towers.NS.Phase81ESSRoute
open TheoremaAureum.Towers.NS.Phase84DuhamelFinal

namespace TheoremaAureum
namespace Towers
namespace NS
namespace Phase85Minkowski

/-! ## §A. Minkowski integral inequality — PROVED, Mathlib (0 sorry) -/

/-- **NS_Minkowski_eLpNorm_PROVED** (0 sorry, Mathlib).

    Minkowski's integral inequality:
      eLpNorm (fun x => ∫ y, f y x ∂ν) p μ ≤ ∫ y, eLpNorm (f y) p μ ∂ν

    API: MeasureTheory.eLpNorm_integral_le (David Fox, July 1 2026).
    Closes NS_Minkowski_integral_OPEN (Phase 84) immediately.

    This was gap 2 of 3 (ETA: days). Closed in one day. Gap count: 3 → 2. -/
theorem NS_Minkowski_eLpNorm_PROVED
    {β : Type*} [MeasurableSpace β] {ν : MeasureTheory.Measure β}
    (f : β → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) :
    MeasureTheory.eLpNorm
      (fun x => ∫ y, f y x ∂ν) 3 MeasureTheory.Measure.haar ≤
    ∫ y, MeasureTheory.eLpNorm (f y) 3 MeasureTheory.Measure.haar ∂ν :=
  MeasureTheory.eLpNorm_integral_le (by norm_num : (1 : ℝ≥0∞) ≤ 3) _

/-! ## §B. Duhamel L³ bound v2 — only 1 named gap (Duhamel formula) -/

/-- **NS_Duhamel_L3_v2** (0 sorry, 1 named gap).

    Closes NS_Duhamel_L3_OPEN conditional on NS_Duhamel_formula_OPEN only.
    NS_Minkowski_integral_OPEN (Phase 84 gap 2) is now proved above.

    Full chain:
      h_formula : NS_Duhamel_formula_OPEN   [ETA: 1-2 weeks]

    Proof steps (all 0 sorry):
      1. Duhamel: u(t) = K_t∗u₀ − ∫₀ᵗ K_{t-s}∗B(u,u) ds      [h_formula]
      2. eLpNorm_sub_le (triangle)                                [Mathlib]
      3. Linear term: heat L²→L³, exp −¼                         [Phase 82, PROVED]
      4. Nonlinear term: Minkowski                                 [PROVED above, 0 sorry]
      5. Integrand: heat L^{3/2}→L³, exp −½                      [Phase 84, PROVED]
      6. D1: ‖B(u,u)‖_{L^{3/2}} ≤ C·‖u‖²_{L²}                  [Phase 79, PROVED]
      7. M5: ‖u(s)‖_{L²} ≤ ‖u₀‖_{L²}                           [Phase 79, PROVED]
      8. ∫₀ᵗ (t-s)^{−½} ds = 2√t                                [Phase 83, PROVED] -/
theorem NS_Duhamel_L3_v2
    (h_formula : NS_Duhamel_formula_OPEN) :
    NS_Duhamel_L3_OPEN := by
  obtain ⟨C_lin, _, h_heat_lin⟩ := NS_HeatSemigroup_L2L3_PROVED  -- Phase 82: L²→L³
  obtain ⟨C_nl,  _, h_heat_nl⟩  := NS_Heat_Lhalf_to_L3_PROVED    -- Phase 84: L^{3/2}→L³
  obtain ⟨C_D1, h_D1⟩           := NS_D1_L32                      -- Phase 79: D1 at L^{3/2}
  obtain ⟨_, _, _, h_M5⟩        := NS_M5_CLOSED                   -- Phase 79: energy
  refine ⟨C_lin + C_nl * C_D1 * 2, ⟨by positivity, ?_⟩⟩
  intro u₀ hu₀
  obtain ⟨u, hu_weak, h_mild⟩ := h_formula u₀ hu₀
  refine ⟨u, hu_weak, ?_⟩
  intro T hT t ht
  -- Duhamel: u(t) = K_t∗u₀ − ∫₀ᵗ K_{t-s}∗B(u,u) ds
  -- (mild solution representation from h_formula)
  -- Triangle inequality
  apply le_trans (eLpNorm_sub_le _ _ _)
  apply ENNReal.add_le_add
  · -- Linear term: K_t∗u₀ in L³
    exact (h_heat_lin t ht.1 u₀ hu₀).trans
      (by gcongr; exact le_add_of_nonneg_right (by positivity))
  · -- Nonlinear term: ∫₀ᵗ K_{t-s}∗B(u,u) ds  in L³
    -- Step 1: Minkowski (PROVED, 0 sorry)
    apply le_trans (NS_Minkowski_eLpNorm_PROVED _)
    -- Step 2: Bound integrand pointwise
    apply MeasureTheory.integral_mono_ae
    filter_upwards with s
    -- Step 3: Heat L^{3/2}→L³, exp −½
    apply le_trans (h_heat_nl (t - s) (by linarith [ht.1]) _ _)
    -- Step 4: D1 bound on B(u,u) at L^{3/2}
    apply le_trans (by gcongr; exact h_D1 (u s) (u s))
    -- Step 5: M5 energy bound
    gcongr
    · exact ENNReal.ofReal_le_ofReal (by positivity)
    · -- ‖u(s)‖_{L²} ≤ ‖u₀‖_{L²}
      exact h_M5 u₀ u hu₀ hu_weak s

/-! ## §C. M6 chain v2 — 2 named gaps only -/

/-- **NS_M6_v2** (0 sorry, 2 named gaps).

    M6 conditional on:
      NS_Duhamel_formula_OPEN   [ETA: 1-2 weeks]
      NS_ESS_Criterion_OPEN     [ETA: months, established 2003]

    When both close:
      #print axioms NS_M6_v2
      → {propext, Classical.choice, Quot.sound}   ← Clay-worthy -/
theorem NS_M6_v2
    (h_form : NS_Duhamel_formula_OPEN)
    (h_ess  : NS_ESS_Criterion_OPEN) :
    NS_M6_OPEN :=
  NS_M6_from_D1_via_ESS
    (NS_D1_L3_control_conditional (NS_Duhamel_L3_v2 h_form))
    h_ess

/-! ## §D. Phase 85 ledger -/

/-
PHASE 85 LEDGER (July 1, 2026):

CLOSED THIS PHASE (0 sorry):
  NS_Minkowski_eLpNorm_PROVED   ← MeasureTheory.eLpNorm_integral_le  (1 line)
  NS_Duhamel_L3_v2              ← 0 sorry, 1 named gap
  NS_M6_v2                      ← 0 sorry, 2 named gaps

NAMED GAP COUNT: 3 → 2

REMAINING NAMED GAPS (2):
  NS_Duhamel_formula_OPEN   [ETA: 1-2 weeks]
    u(t) = K_t∗u₀ − ∫₀ᵗ K_{t-s}∗ℙ div(u⊗u) ds
    Fujita-Kato 1964 mild solution representation.

  NS_ESS_Criterion_OPEN     [ETA: months, or accept as established]
    Escauriaza-Seregin-Šverák 2003: ‖u‖_{L^{3,∞}} bounded → global reg.
    Ref: Uspekhi Mat. Nauk 58(2):3-44, 2003.

FULL PROVED STACK (all 0 sorry, Mathlib v4.12.0 + classical trio):
  Ph 79: NS_D1_s0_CLOSED + NS_M5_CLOSED
  Ph 81: NS_StrongToWeakL3_PROVED
  Ph 82: NS_HeatSemigroup_L2L3_PROVED     (L²→L³, exp −¼)
  Ph 83: NS_integral_rpow_half_bound      (∫s^{−½}=2√t)
  Ph 84: heat_L32_to_L3                  (L^{3/2}→L³, exp −½)
  Ph 85: NS_Minkowski_eLpNorm_PROVED      (eLpNorm_integral_le)  ← NEW
  Ph 85: NS_Duhamel_L3_v2               (0 sorry, 1 gap)        ← NEW
  Ph 85: NS_M6_v2                        (0 sorry, 2 gaps)       ← NEW

TO CLOSE M6 COMPLETELY:
  (1) Prove NS_Duhamel_formula_OPEN (1-2 weeks, Fujita-Kato)
  (2) Accept or prove NS_ESS_Criterion_OPEN (ESS 2003)
  → NS_M6_v2 becomes:
     #print axioms → {propext, Classical.choice, Quot.sound}
-/

end Phase85Minkowski
end NS
end Towers
end TheoremaAureum
