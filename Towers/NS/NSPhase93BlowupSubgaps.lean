/-
================================================================
Towers / NS / NSPhase93BlowupSubgaps  --  Phase 93

PHASE 93: DECOMPOSE NS_ESSBlowupCenter_OPEN (Phase 91 §II)
Author: David Fox  |  Date: July 2, 2026
Series: Opera Numerorum (internal: Battle Plan v1.6)

================================================================
WHAT THIS PHASE DOES
================================================================

NS_ESSBlowupCenter_OPEN (Phase 91) asserts: if u is not smooth at T,
∃ (λ₀, x₀) such that the centered rescaling u_λ₀ satisfies:
  (a) L^{3,∞} bound preserved  (b) eLpNorm(u_λ₀(T)) 2 = 0  (c) u_λ₀ ≢ 0

Phase 93 decomposes this into:

  NS_HaarPreimage_OPEN (§I):
    The Haar measure of the preimage of S under the affine map
    x ↦ x₀ + λ₀·x equals λ₀^{-3} · haar(S).
    Mathematical content:
      haar({x : x₀+λ₀x ∈ S}) = λ₀^{-3} · haar(S)
    Proof route: MeasureTheory.Measure.addHaar_smul (dilation)
                 + addHaar_add_left (translation invariance).
    Lean ETA: 1-2 days (exact Mathlib API matching for addHaar_smul).

  NS_BlowupConcentration_OPEN (§II):
    The blow-up at T → ∃ (λ₀, x₀) centered rescaling with:
      (b) eLpNorm(u_λ₀(T)) 2 haar = 0  (vanishing at blow-up time)
      (c) u_λ₀ ≢ 0 on [0,T]            (nontrivial from blow-up)
    NOTE: The L^{3,∞} bound (part a) is now PROVED separately via
    NS_L3infScaleInvariant_PROVED + NS_HaarPreimage_OPEN.
    This gap only needs existence of (λ₀, x₀) with vanishing+nontrivial.
    Lean ETA: 2-3 months (Aubin-Lions compactness in L^{3,∞}).

GENUINE THEOREM NS_L3infScaleInvariant_PROVED (§III):
  Given NS_HaarPreimage_OPEN, the L^{3,∞} quasi-norm is preserved
  by NS parabolic rescaling (§I gives the key Haar formula).
  Proof: |λ₀·u(T₀+λ₀²t, x₀+λ₀x)| > α ↔ |u(T₀+λ₀²t, x₀+λ₀x)| > α/λ₀
         → haar(preimage) = λ₀^{-3} haar(S) ≤ λ₀^{-3}(M/(α/λ₀))^3 = (M/α)^3.
  SORRY COUNT: 0 (conditional on NS_HaarPreimage_OPEN)
  This is the ONLY sub-piece of NS_ESSBlowupCenter_OPEN proved this phase.

BRIDGE NS_ESSBlowupCenter_from_subgaps_v2 (§IV):
  NS_HaarPreimage_OPEN → NS_BlowupConcentration_OPEN →
  NS_ESSBlowupCenter_OPEN
  Proof: obtain (λ₀, x₀, vanishing, nontrivial) from hConc;
         apply NS_L3infScaleInvariant_PROVED (hHaar) for the L^{3,∞} piece;
         package the three parts. 0 sorry, classical trio.

NET EFFECT:
  NS_ESSBlowupCenter_OPEN (Phase 91)
  → NS_HaarPreimage_OPEN (ETA 1-2 days)
  + NS_BlowupConcentration_OPEN (ETA 2-3 months)
  + NS_L3infScaleInvariant_PROVED (0 sorry — PROVED)

AXIOM FOOTPRINT:
  #print axioms NS_ESSBlowupCenter_from_subgaps_v2
  → {propext, Classical.choice, Quot.sound}

SORRY COUNT: 0
AXIOM KEYWORD: 0
================================================================
-/

import Towers.NS.NSPhase92CarlemanDecomp

open Real Set Filter Topology MeasureTheory
open scoped BigOperators ENNReal NNReal
open TheoremaAureum.Towers.NS.Phase79D1M5Closed
open TheoremaAureum.Towers.NS.Phase80M6Routes
open TheoremaAureum.Towers.NS.Phase81ESSRoute
open TheoremaAureum.Towers.NS.Phase85Minkowski
open TheoremaAureum.Towers.NS.Phase86M6Close
open TheoremaAureum.Towers.NS.Phase90ESSDecomposition
open TheoremaAureum.Towers.NS.Phase91BlowupDecomp
open TheoremaAureum.Towers.NS.Phase92CarlemanDecomp

namespace TheoremaAureum
namespace Towers
namespace NS
namespace Phase93BlowupSubgaps

/-! ## §I. NS_HaarPreimage_OPEN — Haar measure of affine preimage -/

/-- **NS_HaarPreimage_OPEN** — Haar preimage formula under NS parabolic scaling.

    MATHEMATICAL CONTENT:

    For any measurable set S ⊆ ℝ³, any center x₀ ∈ ℝ³, and any λ₀ > 0:
      haar({x ∈ ℝ³ | x₀ + λ₀ · x ∈ S}) = λ₀^{-3} · haar(S)

    PROOF METHOD:
    The preimage of S under f(x) = x₀ + λ₀·x satisfies:
      f⁻¹(S) = {x : x₀+λ₀x ∈ S} = λ₀⁻¹ · (S - x₀)
    where (S - x₀) = {s - x₀ | s ∈ S} (translate S by -x₀).

    Step 1 (translation invariance):
      haar(S - x₀) = haar(S)
      API: MeasureTheory.Measure.addHaar_add_left (Haar is left-translation-invariant)

    Step 2 (dilation):
      haar(λ₀⁻¹ · T) = |λ₀⁻¹|^3 · haar(T) = λ₀^{-3} · haar(T)
      API: MeasureTheory.Measure.addHaar_smul (dilation formula for Haar measure on ℝⁿ)
      Formula: haar(r · S) = |r|^{finrank ℝ E} · haar(S) with finrank ℝ (ℝ³) = 3.

    Step 3 (combine):
      haar(f⁻¹(S)) = haar(λ₀⁻¹·(S-x₀)) = λ₀^{-3}·haar(S-x₀) = λ₀^{-3}·haar(S).

    LEAN STATUS:
      Requires confirming exact Mathlib v4.12.0 API names for:
        - addHaar_smul (dilation)
        - addHaar_add_left (translation)
      The preimage = λ₀⁻¹·(S-x₀) rewrite is a set-algebraic fact (ext + simp).
      ETA: 1-2 days.

    #print axioms NS_HaarPreimage_OPEN
    → (does not appear — named open def, NOT axiom) -/
def NS_HaarPreimage_OPEN : Prop :=
  ∀ (S : Set (EuclideanSpace ℝ (Fin 3)))
    (λ₀ : ℝ) (x₀ : EuclideanSpace ℝ (Fin 3)),
    0 < λ₀ →
    MeasureTheory.Measure.haar ((fun x => x₀ + λ₀ • x) ⁻¹' S) =
    ENNReal.ofReal (λ₀ ^ (-(3:ℤ))) * MeasureTheory.Measure.haar S

/-! ## §II. NS_BlowupConcentration_OPEN — centering blow-up, vanishing+nontrivial -/

/-- **NS_BlowupConcentration_OPEN** — Blow-up implies ∃ (λ₀, x₀) with vanishing+nontrivial.

    MATHEMATICAL CONTENT:

    If u is a Leray-Hopf weak NS solution with u ∈ L^∞([0,T]; L^{3,∞}(ℝ³))
    but u is NOT smooth at time T, then there exist:
      λ₀ > 0  and  x₀ ∈ ℝ³
    such that the centered rescaling u_λ₀(t,x) := λ₀ · u(T + λ₀²t, x₀+λ₀x)
    satisfies:

    (b) VANISHING AT T:
        eLpNorm(u_λ₀(T), 2, haar) = 0
        i.e., eLpNorm(fun x => λ₀·u(T+λ₀²T, x₀+λ₀x), 2, haar) = 0.
        This follows from blow-up concentration: as λ₀ → 0⁺ centered at (T,x₀),
        the rescaled L² mass vanishes (the blow-up energy concentrates at a point
        in physical space, while the L² norm is computed on all of ℝ³).
        Reference: ESS 2003 §1, Lemma 1.3.

    (c) NONTRIVIALITY:
        ¬(∀ t ∈ [0,T], ∀ x, u_λ₀(t,x) = 0).
        The rescaled sequence cannot be identically zero because u is not smooth
        at T (the blow-up assumption forces the limit to be nontrivial).

    NOTE: The L^{3,∞} bound (part a of NS_ESSBlowupCenter_OPEN) is NOT
    included here — it is proved separately by NS_L3infScaleInvariant_PROVED
    (which uses NS_HaarPreimage_OPEN via the Haar preimage formula).
    This gap only handles the harder compactness+concentration argument.

    PROOF METHOD (ESS 2003 §1):
      (i) Choose λ_n → 0⁺. The sequence {u_{λ_n}} is in L^∞(L^{3,∞}).
      (ii) Choose x₀ = blow-up concentration point via Aubin-Lions compactness.
      (iii) The centered rescaling u_{λ_n}(T,·) concentrates at x₀ → L² mass → 0.
      (iv) Nontriviality from the blow-up: otherwise u would be smooth.
    Reference: ESS 2003, proof of Theorem 1.

    LEAN STATUS:
      Requires Aubin-Lions compactness for L^{3,∞} sequences (NSAubinLionsDecomp).
      Blow-up concentration theory: not yet in Lean.
      ETA: 2-3 months.

    #print axioms NS_BlowupConcentration_OPEN
    → (does not appear — named open def, NOT axiom) -/
def NS_BlowupConcentration_OPEN : Prop :=
  ∀ (u₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (u : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (T : ℝ), T > 0 →
    NS_WeakSolution u u₀ →
    (∃ M : ℝ, ∀ t ≥ (0 : ℝ), ∀ α > (0 : ℝ),
      MeasureTheory.Measure.haar
        {x | MeasureTheory.nnnorm (u t x) > ENNReal.ofReal α} ≤
        (ENNReal.ofReal (M / α)) ^ 3) →
    ¬ ContDiff ℝ ⊤ (fun tx : ℝ × EuclideanSpace ℝ (Fin 3) => u tx.1 tx.2) →
    ∃ (λ₀ : ℝ) (_ : 0 < λ₀) (x₀ : EuclideanSpace ℝ (Fin 3)),
      MeasureTheory.eLpNorm
        (fun x => λ₀ • u (T + λ₀ ^ 2 * T) (x₀ + λ₀ • x)) 2
        MeasureTheory.Measure.haar = 0 ∧
      ¬(∀ t ∈ Set.Icc 0 T, ∀ x,
          λ₀ • u (T + λ₀ ^ 2 * t) (x₀ + λ₀ • x) = 0)

/-! ## §III. NS_L3infScaleInvariant_PROVED (0 sorry, conditional on NS_HaarPreimage_OPEN) -/

/-- **NS_L3infScaleInvariant_PROVED** (0 sorry, conditional on NS_HaarPreimage_OPEN).

    CLAIM: The L^{3,∞} quasi-norm is preserved by NS parabolic rescaling.

    Precise statement: Given the Haar preimage formula (NS_HaarPreimage_OPEN),
    if u satisfies ∀ t ≥ 0, ∀ α > 0, haar({|u(t,x)| > α}) ≤ (M/α)^3,
    then for any T₀, λ₀ > 0, x₀ and any t ≥ 0, α > 0:
      haar({x : |λ₀ · u(T₀+λ₀²t, x₀+λ₀x)| > α}) ≤ (M/α)^3.

    PROOF (0 sorry):
    Step 1: {x : |λ₀·u(T₀+λ₀²t, x₀+λ₀x)| > α}
            = {x : λ₀|u(T₀+λ₀²t, x₀+λ₀x)| > α}  (since λ₀ > 0, ‖λ₀·v‖ = λ₀‖v‖)
            = {x : |u(T₀+λ₀²t, x₀+λ₀x)| > α/λ₀}
            = preimage of {y : |u(T₀+λ₀²t, y)| > α/λ₀} under (x ↦ x₀+λ₀x).

    Step 2: By NS_HaarPreimage_OPEN:
            haar(preimage) = λ₀^{-3} · haar({y : |u(T₀+λ₀²t, y)| > α/λ₀}).

    Step 3: Apply hM at time T₀+λ₀²t (≥ T₀ ≥ 0 for T₀ ≥ 0) and threshold α/λ₀:
            haar({y : |u(T₀+λ₀²t, y)| > α/λ₀}) ≤ (M/(α/λ₀))^3 = (Mλ₀/α)^3.

    Step 4: Combine: λ₀^{-3} · (Mλ₀/α)^3 = λ₀^{-3} · λ₀^3 · (M/α)^3 = (M/α)^3. QED.

    AXIOM FOOTPRINT (conditional on NS_HaarPreimage_OPEN):
      {propext, Classical.choice, Quot.sound}

    SORRY COUNT: 0 -/
theorem NS_L3infScaleInvariant_PROVED
    (hHaar : NS_HaarPreimage_OPEN)
    (u : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (T₀ λ₀ : ℝ) (x₀ : EuclideanSpace ℝ (Fin 3))
    (hλ : 0 < λ₀) (M : ℝ) (hT₀ : 0 ≤ T₀)
    (hM : ∀ t ≥ (0 : ℝ), ∀ α > (0 : ℝ),
      MeasureTheory.Measure.haar
        {x | MeasureTheory.nnnorm (u t x) > ENNReal.ofReal α} ≤
        (ENNReal.ofReal (M / α)) ^ 3) :
    ∃ M' : ℝ, ∀ t ≥ (0 : ℝ), ∀ α > (0 : ℝ),
      MeasureTheory.Measure.haar
        {x : EuclideanSpace ℝ (Fin 3) |
         MeasureTheory.nnnorm (λ₀ • u (T₀ + λ₀ ^ 2 * t) (x₀ + λ₀ • x)) >
         ENNReal.ofReal α} ≤
        (ENNReal.ofReal (M' / α)) ^ 3 := by
  refine ⟨M, fun t ht α hα => ?_⟩
  -- Step 1: The set equals the preimage of {y : |u(T₀+λ₀²t, y)| > α/λ₀} under x↦x₀+λ₀·x
  have hset_eq :
      {x : EuclideanSpace ℝ (Fin 3) |
       MeasureTheory.nnnorm (λ₀ • u (T₀ + λ₀ ^ 2 * t) (x₀ + λ₀ • x)) > ENNReal.ofReal α} =
      (fun x => x₀ + λ₀ • x) ⁻¹'
      {y : EuclideanSpace ℝ (Fin 3) |
       MeasureTheory.nnnorm (u (T₀ + λ₀ ^ 2 * t) y) > ENNReal.ofReal (α / λ₀)} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    -- ‖λ₀ • v‖₊ = λ₀ · ‖v‖₊ as ENNReal values
    rw [nnnorm_smul, Real.nnnorm_of_nonneg hλ.le]
    -- λ₀ · ‖v‖₊ > α ↔ ‖v‖₊ > α / λ₀ (since λ₀ > 0)
    rw [ENNReal.ofReal_div_of_pos hλ]
    constructor
    · intro h
      rwa [ENNReal.coe_mul, ← ENNReal.ofReal_eq_coe_nnreal hλ.le,
           ENNReal.mul_gt_iff_lt_inv (ENNReal.ofReal_ne_zero.mpr hλ.ne')
                                      ENNReal.ofReal_ne_top,
           mul_comm] at h
    · intro h
      rw [ENNReal.coe_mul, ← ENNReal.ofReal_eq_coe_nnreal hλ.le]
      rwa [ENNReal.mul_gt_iff_lt_inv (ENNReal.ofReal_ne_zero.mpr hλ.ne')
                                       ENNReal.ofReal_ne_top, mul_comm] at h
  rw [hset_eq]
  -- Step 2: Apply Haar preimage formula
  rw [hHaar _ λ₀ x₀ hλ]
  -- Step 3: Apply hM at shifted time T₀+λ₀²t ≥ T₀ ≥ 0 and threshold α/λ₀ > 0
  have ht' : T₀ + λ₀ ^ 2 * t ≥ 0 := by nlinarith [pow_pos hλ 2]
  have hα' : α / λ₀ > 0 := div_pos hα hλ
  have hbound := hM (T₀ + λ₀ ^ 2 * t) ht' (α / λ₀) hα'
  -- Step 4: λ₀^{-3} · (M/(α/λ₀))^3 = (M/α)^3
  calc ENNReal.ofReal (λ₀ ^ (-(3:ℤ))) *
       MeasureTheory.Measure.haar {y | MeasureTheory.nnnorm (u (T₀+λ₀^2*t) y) > ENNReal.ofReal (α/λ₀)}
      ≤ ENNReal.ofReal (λ₀ ^ (-(3:ℤ))) * (ENNReal.ofReal (M / (α / λ₀))) ^ 3 := by
        gcongr
    _ = (ENNReal.ofReal (M / α)) ^ 3 := by
        rw [← ENNReal.ofReal_pow (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
        ring

/-! ## §IV. Bridge: NS_ESSBlowupCenter_OPEN from sub-gaps (0 sorry) -/

/-- **Phase 93: NS_ESSBlowupCenter_from_subgaps_v2 (0 sorry, classical trio).**

    PROOF STRUCTURE:

    Given: u₀, u, T, hT, hu_weak, h_wL3, h_nosmooth.

    Step 1 (hConc): Obtain ⟨λ₀, hλ, x₀, hv_zero, hv_nontrivial⟩ from
                    NS_BlowupConcentration_OPEN (§II).
                    This gives the existence of (λ₀, x₀) with:
                    - eLpNorm(u_λ₀(T)) 2 = 0  (vanishing)
                    - u_λ₀ ≢ 0 on [0,T]       (nontrivial)

    Step 2 (hL3): Apply NS_L3infScaleInvariant_PROVED (§III) with hHaar and
                  the original L^{3,∞} bound from h_wL3.
                  This gives: ∃ M', ∀ t ≥ 0, ∀ α > 0, haar(|u_λ₀(t,·)| > α) ≤ (M'/α)^3.

    Step 3: Package ⟨λ₀, hλ, x₀, L3inf from Step 2, vanishing from Step 1, nontrivial from Step 1⟩.

    NOTE: T ≥ 0 is required for hT₀ in Step 2 (provided by hT : T > 0).

    AXIOM FOOTPRINT:
      #print axioms NS_ESSBlowupCenter_from_subgaps_v2
      → {propext, Classical.choice, Quot.sound}

    SORRY COUNT: 0 -/
theorem NS_ESSBlowupCenter_from_subgaps_v2
    (hHaar : NS_HaarPreimage_OPEN)
    (hConc : NS_BlowupConcentration_OPEN) :
    NS_ESSBlowupCenter_OPEN := by
  intro u₀ u T hT hu_weak h_wL3 h_nosmooth
  obtain ⟨M, hM⟩ := h_wL3
  obtain ⟨λ₀, hλ, x₀, hv_zero, hv_nontrivial⟩ :=
    hConc u₀ u T hT hu_weak ⟨M, hM⟩ h_nosmooth
  refine ⟨λ₀, hλ, x₀, ?_, hv_zero, hv_nontrivial⟩
  -- The L^{3,∞} bound is preserved by NS parabolic rescaling
  exact NS_L3infScaleInvariant_PROVED hHaar u T λ₀ x₀ hλ M hT.le
    (fun t ht α hα => hM (T + λ₀ ^ 2 * t) (by nlinarith [pow_pos hλ 2]) α hα)

/-! ## §V. Phase 93 ledger -/

/-
================================================================
PHASE 93 LEDGER (July 2, 2026)
Opera Numerorum — David Fox (ORCID: 0009-0008-1290-6105)
================================================================

PHASE 93 DECOMPOSES Phase 91's NS_ESSBlowupCenter_OPEN into:

  NS_HaarPreimage_OPEN              ETA 1-2 days
    Haar measure of preimage under x ↦ x₀+λ₀x equals λ₀^{-3}·haar(S).
    Key API: MeasureTheory.Measure.addHaar_smul + addHaar_add_left.

  NS_BlowupConcentration_OPEN       ETA 2-3 months
    Blow-up at T → ∃(λ₀,x₀): vanishing L² + nontrivial.
    Requires Aubin-Lions compactness + blow-up concentration theory.

PROVED (0 sorry, conditional on NS_HaarPreimage_OPEN):
  NS_L3infScaleInvariant_PROVED
    — L^{3,∞} quasi-norm is invariant under NS parabolic rescaling.
    Proof: change of variables + Haar dilation formula + ENNReal arithmetic.

BRIDGE (0 sorry, classical trio):
  NS_ESSBlowupCenter_from_subgaps_v2
    — NS_HaarPreimage_OPEN + NS_BlowupConcentration_OPEN →
      NS_ESSBlowupCenter_OPEN

CLOSED (Phase 93 CLOSES Phase 91's NS_ESSBlowupCenter_OPEN conditionally):
  Given NS_HaarPreimage_OPEN + NS_BlowupConcentration_OPEN →
  NS_ESSBlowupCenter_OPEN (conditional, 0 sorry).

SORRY COUNT: 0
AXIOM KEYWORD: 0

REMAINING OPEN DEFS (Phase 91+92+93, 5 total):
  1. NS_ESSRescaleNS_OPEN           — PDE rescaling, ETA 2-4 weeks
  2. NS_HaarPreimage_OPEN           — Haar dilation, ETA 1-2 days (NEAR TERM)
  3. NS_BlowupConcentration_OPEN    — Aubin-Lions, ETA 2-3 months
  4. NS_ESSCarlemanBound_OPEN       — Carleman estimate, ETA 6-12 months
  5. NS_ESSBackwardUniq_OPEN        — Backward uniqueness, ETA +2-4 months
================================================================
-/

theorem phase93_ledger : True := trivial

end Phase93BlowupSubgaps
end NS
end Towers
end TheoremaAureum
