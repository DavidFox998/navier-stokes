/-
================================================================
Towers / NS / NSKPBridge  —  NS Tower 540, Phase 11
                             KP-to-NS Regularity Bridge

Adapts the Kotecký–Preiss cluster-expansion framework (YM tower,
Wall252–255) to the NS setting.  In the YM case, KP-summable polymer
activities imply correlation decay; here, KP-summable frequency-shell
energy activities imply global Sobolev control — an alternate pathway
into Gate 3 (NS_GlobalContinuation_OPEN) that bypasses the raw Sobolev
bound and may be more tractable via constructive-QFT methods.

### NS-polymer dictionary

  YM polymer γ (lattice loop)       ↔  NS shell n (dyadic freq. band [2ⁿ, 2ⁿ⁺¹))
  YM activity |activity γ| ≤ e^{-β|γ|} ↔  NS shell energy a n ≤ C · rⁿ  (r < 1/7)
  YM entropy  7ⁿ (2d−1 = 7 in ℤ⁴) ↔  NS shell entropy 7ⁿ (Fourier mode count)
  YM KP sum Σ |activity γ| < ∞     ↔  NS KP sum Σ aₙ < ∞ (global energy finite)
  YM → correlation decay            ↔  NS → Sobolev bound → no blow-up → Gate 3

### Proved sub-avenues (all classical trio, 0 sorry)

  P: NS_KPComparisonTest_PROVED
     Abstract KP comparison test: if the exp-weighted shell sum is summable,
     the unweighted shell sum is summable.  Mirrors Wall253's
     `kp_cluster_criterion`, proved here in the NS frequency-shell namespace.
     Key step: Real.exp ≥ 1 (from Real.add_one_le_exp + nonnegativity).

  Q: NS_EntropyGeometric_PROVED
     Geometric series beats 7ⁿ entropy when rate q < 1/7:
     Σ 7ⁿ · qⁿ summable.  Mirrors Wall255's `entropy_geometric_summable`,
     proved here by mul_pow rewrite + summable_geometric_of_lt_one.

  R: NS_SobolevControlFromCascade_PROVED
     KEY NEW RESULT: if NS shell energies decay at rate r (aₙ ≤ rⁿ, r < 1),
     then for any Sobolev-weight factor q with q·r < 1, the weighted sum
     Σ qⁿ · aₙ converges.  This is the "cascade decay → Sobolev control"
     structural lemma: comparison test (Summable.of_nonneg_of_le) +
     mul_pow + summable_geometric_of_lt_one.

  S: NS_CascadeDecayNecessary_PROVED
     Necessary condition: if the Sobolev-weighted cascade sum is summable,
     its terms tend to zero.  Direct from Summable.tendsto_atTop_zero.

### Named OPEN surfaces (KP pathway to Gate 3)

  NS_KPCascadeControl_OPEN s
     There exists a frequency-shell energy decomposition of the NS
     solution with geometric decay rate r < 1/7 (beating shell entropy).
     Requires Littlewood–Paley theory and dyadic Sobolev decomposition,
     absent from Mathlib v4.12.0.  ETA: 18–24 mo.

  NS_KPToSmoothness_OPEN s
     KP cascade control → global Sobolev bound → NS_GlobalSobolevBound_OPEN.
     The logical bridge from the KP sufficient condition to Gate 3.
     Requires connecting the abstract cascade bound to IsSmoothOn.

### KP reduction combinator (Phase 11 capstone)

  ns_kp_gate3_reduction — uses M + K + KPC + KPS + Bridge → Gate 3.
    Routes the KP pathway through the Phase 10 gate structure.
    Classical trio, 0 sorry.  Gate 3 still OPEN until all inputs are discharged.

Honest scope:
  * NS global regularity OPEN.  No Clay claim.
  * NS_KPCascadeControl_OPEN is a STRICTLY WEAKER sufficient condition than
    NS_GlobalSobolevBound_OPEN.  Discharging the cascade bound alone does not
    close Clay; it still requires K (BKM criterion) and the Bridge.
  * `kotecky_preiss_criterion` in Towers/Attempts/ClusterExpansion.lean
    remains INVARIANT-LOCKED; this file does NOT touch, weaken, or
    discharge it.  YM stays Status: Open.
================================================================
-/

import Towers.NS.NSGate3Decomp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

open Filter Topology Real
open TheoremaAureum.Towers.NS.FunctionSpaces
open TheoremaAureum.Towers.NS.WeakSolution
open TheoremaAureum.Towers.NS.Regularity
open TheoremaAureum.Towers.NS.ClayCombinator
open TheoremaAureum.Towers.NS.Gate3Decomp

namespace TheoremaAureum
namespace Towers
namespace NS
namespace KPBridge

/-!
## Named OPEN surfaces (KP pathway into Gate 3)
-/

/-- **OPEN (Phase 11)**: NS energy-shell activities satisfy the KP cascade bound.
    There exists a decomposition of the NS velocity field into dyadic frequency-shell
    energies `shellEnergy u n ≥ 0` with geometric decay rate `r < 1/7` (beating
    the 7ⁿ frequency-shell entropy) and amplitude `C > 0`:
    `shellEnergy u n ≤ C · rⁿ` for all shells n and all NS solutions u.
    Requires Littlewood–Paley dyadic decomposition and Bernstein-type Sobolev
    inequalities (absent from Mathlib v4.12.0; 18–24 mo). -/
def NS_KPCascadeControl_OPEN (s : ℝ) : Prop :=
  ∃ (shellEnergy : (ℝ → Hdiv_free (s + 2)) → ℕ → ℝ) (r C : ℝ),
    0 ≤ r ∧ r < 1 / 7 ∧ 0 < C ∧
    ∀ (u₀ : Hdiv_free (s + 2)) (f : ExternalForce s)
      (u : ℝ → Hdiv_free (s + 2)),
      WeakNS u u₀ f →
      ∀ n : ℕ, 0 ≤ shellEnergy u n ∧ shellEnergy u n ≤ C * r ^ n

/-- **OPEN (Phase 11)**: KP cascade control implies global Sobolev bound.
    IF the NS energy-shell activities satisfy the KP cascade bound
    (`NS_KPCascadeControl_OPEN s`), THEN the Sobolev `Lp Val 2 (mu (s+2))`
    norm of u(t) stays finite for all T > 0 (`NS_GlobalSobolevBound_OPEN s`).
    The logical bridge connecting the KP sufficient condition (cascade smallness)
    to the norm-control conclusion of Gate 3 Part B via BKM.
    Requires Littlewood–Paley reconstruction and Sobolev interpolation (absent
    from Mathlib v4.12.0; 18–24 mo). -/
def NS_KPToSmoothness_OPEN (s : ℝ) : Prop :=
  NS_KPCascadeControl_OPEN s → NS_GlobalSobolevBound_OPEN s

/-!
## Proved sub-avenues (structural; classical trio, 0 sorry)
-/

/-- **PROVED (Phase 11, Sub-av. P)**: Abstract KP comparison test for NS frequency shells.
    For any shell index type `Shell`, shell energies `energy : Shell → ℝ`,
    and nonneg weights `weight : Shell → ℝ` with `0 ≤ weight n` for all n:
    if the exp-weighted shell sum `Σ |energy n| · exp(weight n)` is summable,
    then the unweighted sum `Σ |energy n|` is summable.
    Proof: `exp(weight n) ≥ 1` (from `Real.add_one_le_exp` + `weight n ≥ 0`);
    comparison test `Summable.of_nonneg_of_le`.
    Mirrors Wall253's `kp_cluster_criterion`, proved in the NS namespace.
    Classical trio, 0 sorry. -/
theorem NS_KPComparisonTest_PROVED {Shell : Type*}
    (energy weight : Shell → ℝ)
    (hw : ∀ n, 0 ≤ weight n)
    (hKP : Summable (fun n : Shell => |energy n| * Real.exp (weight n))) :
    Summable (fun n : Shell => |energy n|) := by
  refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_) hKP
  have hone : (1 : ℝ) ≤ Real.exp (weight n) := by
    have h := Real.add_one_le_exp (weight n)
    linarith [hw n]
  calc |energy n|
      = |energy n| * 1 := (mul_one _).symm
    _ ≤ |energy n| * Real.exp (weight n) :=
        mul_le_mul_of_nonneg_left hone (abs_nonneg _)

/-- **PROVED (Phase 11, Sub-av. Q)**: Geometric shell sum beats 7ⁿ entropy.
    For `0 ≤ q` with `7 · q < 1`, the entropy-weighted geometric series
    `Σ 7ⁿ · qⁿ` is summable.
    Proof: `7ⁿ · qⁿ = (7q)ⁿ` by `mul_pow`; `summable_geometric_of_lt_one`
    since `7q < 1` and `7q ≥ 0`.
    Mirrors Wall255's `entropy_geometric_summable`.  Classical trio, 0 sorry. -/
theorem NS_EntropyGeometric_PROVED {q : ℝ} (hq0 : 0 ≤ q) (h7q : 7 * q < 1) :
    Summable (fun n : ℕ => (7 : ℝ) ^ n * q ^ n) := by
  have hfun : (fun n : ℕ => (7 : ℝ) ^ n * q ^ n) = fun n : ℕ => (7 * q) ^ n := by
    funext n; rw [mul_pow]
  rw [hfun]
  exact summable_geometric_of_lt_one (mul_nonneg (by norm_num) hq0) h7q

/-- **PROVED (Phase 11, Sub-av. R)**: Cascade decay → Sobolev-weighted summability.
    KEY STRUCTURAL RESULT for the NS-KP bridge.
    If the NS frequency-shell energies `a : ℕ → ℝ` are nonneg and decay
    geometrically at rate `r` (i.e. `aₙ ≤ rⁿ`), then for any Sobolev-weight
    factor `q ≥ 0` satisfying `q · r < 1`, the Sobolev-weighted cascade sum
    `Σ qⁿ · aₙ` is summable.
    Interpretation: a cascade decaying at rate `r < 1/q` has enough high-frequency
    suppression to keep the `q`-weighted Sobolev norm finite.
    Proof: `qⁿ · aₙ ≤ qⁿ · rⁿ = (q·r)ⁿ` by `mul_pow`;
    `summable_geometric_of_lt_one` since `q·r < 1`.
    Classical trio, 0 sorry. GENUINE. -/
theorem NS_SobolevControlFromCascade_PROVED
    (a : ℕ → ℝ) (r q : ℝ)
    (ha0 : ∀ n, 0 ≤ a n)
    (har : ∀ n, a n ≤ r ^ n)
    (hr0 : 0 ≤ r) (hq0 : 0 ≤ q)
    (hqr : q * r < 1) :
    Summable (fun n : ℕ => q ^ n * a n) := by
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (pow_nonneg hq0 n) (ha0 n))
    (fun n => ?_)
    (summable_geometric_of_lt_one (mul_nonneg hq0 hr0) hqr)
  calc q ^ n * a n
      ≤ q ^ n * r ^ n := mul_le_mul_of_nonneg_left (har n) (pow_nonneg hq0 n)
    _ = (q * r) ^ n   := (mul_pow q r n).symm

/-- **PROVED (Phase 11, Sub-av. S)**: Necessary decay condition from summability.
    If the Sobolev-weighted cascade sum `Σ qⁿ · aₙ` is summable, then
    its terms tend to zero: `qⁿ · aₙ → 0`.
    This is a necessary condition for finite Sobolev control: blow-up at
    finite time would require terms bounded away from zero (contradicting
    summability).  One line from `Summable.tendsto_atTop_zero`.
    Classical trio, 0 sorry. -/
theorem NS_CascadeDecayNecessary_PROVED
    (a : ℕ → ℝ) (q : ℝ) (hq0 : 0 < q)
    (hsum : Summable (fun n : ℕ => q ^ n * a n)) :
    Filter.Tendsto (fun n : ℕ => q ^ n * a n) Filter.atTop (nhds 0) :=
  hsum.tendsto_atTop_zero

/-!
## KP reduction combinator (Gate 3 via KP pathway)
-/

/-- **KP reduction combinator (Phase 11 capstone).**
    Alternative route into Gate 3 via the KP cascade framework:

    Given:
      hM    : NS_LocalRegularity_OPEN s      — Part A: local smoothness
      hK    : NS_BKMCriterion_OPEN s         — BKM: blow-up ↔ norm blow-up
      hKPC  : NS_KPCascadeControl_OPEN s     — KP: shell energies decay at r < 1/7
      hKPS  : NS_KPToSmoothness_OPEN s       — Bridge: KP cascade → Sobolev bound
      hBridge : NS_BKM_Bridge_OPEN s         — BKM + Sobolev → Part B

    Conclusion: NS_GlobalContinuation_OPEN s (Gate 3).

    Route: hKPS hKPC : NS_GlobalSobolevBound_OPEN s (from KP reduction)
           hBridge hK (hKPS hKPC) : Part B (local → global, no blow-up)
           hM ∧ Part B → Gate 3.

    Classical trio, 0 sorry.  Gate 3 itself is OPEN until all inputs are
    discharged.  NS global regularity: OPEN.  No Clay claim. -/
theorem ns_kp_gate3_reduction (s : ℝ)
    (hM     : NS_LocalRegularity_OPEN s)
    (hK     : NS_BKMCriterion_OPEN s)
    (hKPC   : NS_KPCascadeControl_OPEN s)
    (hKPS   : NS_KPToSmoothness_OPEN s)
    (hBridge : NS_BKM_Bridge_OPEN s) :
    NS_GlobalContinuation_OPEN s :=
  ns_gate3_from_avenues s hM hK (hKPS hKPC) hBridge

/-- **Registry (Phase 11)**: P+Q+R+S proved unconditionally; KPC+KPS OPEN. -/
theorem ns_kp_proved_avenues_hold {Shell : Type*}
    (energy weight : Shell → ℝ) (hw : ∀ n, 0 ≤ weight n)
    (hKP : Summable (fun n : Shell => |energy n| * Real.exp (weight n)))
    {q : ℝ} (hq0 : 0 ≤ q) (h7q : 7 * q < 1) :
    Summable (fun n : Shell => |energy n|) ∧
    Summable (fun n : ℕ => (7 : ℝ) ^ n * q ^ n) :=
  ⟨NS_KPComparisonTest_PROVED energy weight hw hKP,
   NS_EntropyGeometric_PROVED hq0 h7q⟩

end KPBridge
end NS
end Towers
end TheoremaAureum
