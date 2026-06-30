/-
  NSCorrSemigroupContinuity.lean  --  Phase 32: NS Tower, navier-stokes repo
  Author: David Fox  |  Date: May 21, 2026
  Series: Opera Numerorum (internal: Battle Plan v1.6)

  PHASE 32: Close NS_WeakInitCont_Degenerate_OPEN via orbit closure + C_0-semigroup continuity.

  MATHEMATICAL STRATEGY:
    The NS Tower already knows (Phase 22):
      NS_CorrSemigroupGenerator_PROVED : NS_CorrSemigroupGenerator_OPEN s  (Gap A proved)
    and (Phase 23):
      NS_AdjointIntegralConst_OPEN: given B.1 + Gap A, u t = corrSemigroup s t u_0.
    and (Phase 29):
      corrSemigroup_at_zero: corrSemigroup s 0 u_0 = u_0.

    Phase 32 proves (0 sorry, given NS_CorrSemigroupLipAtZero_OPEN):
      C_0-semigroup property: corrSemigroup s t u_0 -> u_0 as t -> 0+.
    Then: inner(u t, psi) -> inner(u_0, psi) by inner product continuity + orbit ID.

    SYMBOL LIPSCHITZ AT BASE 0 (proved unconditionally):
      corrSemSym_lipschitz_nonneg xi 0 t at (t_arg=0, tau_arg=t) gives:
        |corrSemSym t xi - corrSemSym 0 xi| <= 1/4 * |t - 0| = 1/4 * t
      with corrSemSym(0, xi) = 1 [corrSemigroupSymbol_at_zero]:
        |corrSemSym t xi - 1| <= 1/4 * t.

  PROVED (0 sorry, classical trio):
    corrSemigroupSymbol_sub_one_le   -- |corrSemSym t xi - 1| <= 1/4 * t  (t >= 0)
    corrSemigroup_tendsto_id_atZero  -- corrSem s t u_0 -> u_0 (given hlip)
    ns_weakInitCont_from_orbit       -- NS_WeakInitCont_OPEN from B.1+B.3+hlip (0 sorry)
    ns_weakInitCont_degenerate_from_orbit  -- NS_WeakInitCont_Degenerate_OPEN (same)
    NS_AdjointPackage_PartB_from_orbit     -- NS_AdjointPackage_PartB_OPEN (same)

  NAMED OPEN DEF (1 new, REPLACES NS_WeakInitCont_Degenerate_OPEN):
    NS_CorrSemigroupLipAtZero_OPEN
      ||corrSemigroup s t u_0 - u_0|| <= 1/4 * t * ||u_0||  (t >= 0)
      ETA: ~1 week. Phase 26 pattern (corrSemigroup_coe_eq_lin + eLpNorm_mono_ae).
      NOT new mathematics. NOT a Clay problem.

  NET EFFECT ON NAMED OPEN DEFS:
    ELIMINATED: NS_WeakInitCont_Degenerate_OPEN  (~2 weeks, depended on MaxReg)
    ADDED:      NS_CorrSemigroupLipAtZero_OPEN   (~1 week, pure Lp API, NO MaxReg)
    NET: shorter path, MaxReg dependency removed for the degenerate case.

  IMPORT NOTE: NSParametricDiff imported for NS_CorrSemigroupGenerator_PROVED (Phase 22).
    NSParametricDiff is Phase 22; no import cycles (precedes NSDerivSemigroup/NSBochnerDiff).

  CERT AXIOMS: classical trio only. NS Clay Surface #1: LOCKED OPEN. No Clay claim.
-/

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Analysis.InnerProductSpace.Basic

import Towers.NS.NSWeakInitContClose
import Towers.NS.NSParametricDiff

namespace TheoremaAureum.Towers.NS.CorrSemigroupContinuity

open Real Set Filter Topology MeasureTheory
open scoped BigOperators ENNReal NNReal
open TheoremaAureum.Towers.NS.FunctionSpaces
open TheoremaAureum.Towers.NS.SemigroupDef
open TheoremaAureum.Towers.NS.WeakSolution
open TheoremaAureum.Towers.NS.Stokes
open TheoremaAureum.Towers.NS.DerivSemigroup
open TheoremaAureum.Towers.NS.BochnerDiff
open TheoremaAureum.Towers.NS.AdjointPackageClose
open TheoremaAureum.Towers.NS.AdjointPackagePartBClose
open TheoremaAureum.Towers.NS.WeakInitContClose
open TheoremaAureum.Towers.NS.ParametricDiff
open NSTower

variable {s : ℝ}

/-! ## I. Symbol at t=0 equals 1 -/

/-- corrSemigroupSymbol 0 xi = 1 for all xi : Freq.
    Proof: exp(-stokesRate xi * 0) = exp(0) = 1.
    #print axioms corrSemigroupSymbol_at_zero = classical trio. -/
private lemma corrSemigroupSymbol_at_zero (xi : Freq) :
    corrSemigroupSymbol 0 xi = 1 := by
  simp only [corrSemigroupSymbol, mul_zero, neg_zero, zero_div,
             Real.exp_zero, Complex.ofReal_one]

/-! ## II. Symbol Lipschitz distance from 1 at t=0 -/

/-- **Phase 32: |corrSemSym t xi - 1| <= 1/4 * t for t >= 0.**

    PROOF:
      corrSemSym_lipschitz_nonneg xi 0 t (le_refl 0) ht
        : ||corrSemSym t xi - corrSemSym 0 xi|| <= 1/4 * |t - 0|
      corrSemigroupSymbol_at_zero: corrSemSym 0 xi = 1.
      |t - 0| = t  (since t >= 0).
    Combining: ||corrSemSym t xi - 1|| <= 1/4 * t.

    #print axioms corrSemigroupSymbol_sub_one_le = classical trio. -/
lemma corrSemigroupSymbol_sub_one_le (xi : Freq) (t : ℝ) (ht : 0 ≤ t) :
    ‖corrSemigroupSymbol t xi - 1‖ ≤ 1 / 4 * t := by
  -- corrSemSym_lipschitz_nonneg: (t_arg=0, tau_arg=t)
  -- gives ||corrSemSym t xi - corrSemSym 0 xi|| <= 1/4 * |t - 0|
  have h := corrSemSym_lipschitz_nonneg xi 0 t (le_refl 0) ht
  rw [corrSemigroupSymbol_at_zero] at h
  simp only [sub_zero, abs_of_nonneg ht] at h
  linarith

/-! ## III. Named open def: Lp norm plumbing for corrSemigroup at t=0 -/

/-- **[NAMED OPEN DEF] NS_CorrSemigroupLipAtZero_OPEN (Phase 32).**

    STATEMENT: ||corrSemigroup s t ht u_0 - u_0||_{Hdiv_free(s+2)} <= 1/4 * t * ||u_0||
    for t >= 0.

    MATHEMATICAL CONTENT:
      corrSemigroupSymbol_sub_one_le (proved above): |corrSemSym(t, xi) - 1| <= 1/4 * t.
      corrSemigroup acts as Fourier multiplier by corrSemSym(t, ·) on Lp(mu(s+2)).
      corrSemigroup_at_zero (Phase 29): corrSemigroup s 0 u_0 = u_0.
      Therefore:
        ||corrSemigroup s t u_0 - u_0||_{Lp}
          = ||(corrSemSym(t,·) - 1) * u_0_hat||_{L^2(mu)}
          <= (1/4 * t) * ||u_0_hat||_{L^2(mu)}
          = (1/4 * t) * ||u_0||.

    WHY OPEN IN LEAN (~1 week, NOT new math):
      Phase 26 (NSLpErrorPlumbing.lean) proved NS_LpErrorNormPlumbing_OPEN by:
        (1) Submodule.norm_coe: ||.||_Hdiv = ||.||_Hsv
        (2) corrSemigroup_coe_eq_lin: coerce corrSemigroup to corrSemigroupLin
        (3) Lp.norm_def: ||.||_Lp = (eLpNorm . 2 mu).toReal
        (4) eLpNorm_congr_ae: pointwise ae equality
        (5) eLpNorm_mono_ae + nnnorm_smul: bound by corrSemigroupSymbol_sub_one_le
      Identical API. ETA: ~1 week. NOT a Clay problem. -/
def NS_CorrSemigroupLipAtZero_OPEN (s : ℝ) : Prop :=
  ∀ (t : ℝ) (ht : 0 ≤ t) (u₀ : Hdiv_free (s + 2)),
    ‖corrSemigroup s t ht u₀ - u₀‖ ≤ 1 / 4 * t * ‖u₀‖

/-! ## IV. C_0-semigroup strong continuity at t=0 -/

/-- **Phase 32: corrSemigroup s (max 0 t) u₀ -> u₀ as t -> 0+ (C_0-semigroup property).**

    PROOF (0 sorry, given hlip : NS_CorrSemigroupLipAtZero_OPEN s):
      For any epsilon > 0, choose delta = epsilon / (1/4 * ||u₀|| + 1) > 0.
      For t in Ioi 0 with t < delta:
        ||corrSemigroup s t u₀ - u₀|| <= 1/4 * t * ||u₀|| <= t*(1/4*||u₀||+1) < epsilon.
      (The max 0 t = t for t > 0 by max_eq_right.)

    #print axioms corrSemigroup_tendsto_id_atZero = classical trio (given hlip). -/
theorem corrSemigroup_tendsto_id_atZero
    (hlip : NS_CorrSemigroupLipAtZero_OPEN s)
    (u₀ : Hdiv_free (s + 2)) :
    Filter.Tendsto (fun t => corrSemigroup s (max 0 t) (le_max_left 0 t) u₀)
                   (nhdsWithin 0 (Set.Ioi 0))
                   (nhds u₀) := by
  rw [Metric.tendsto_nhdsWithin_iff]
  intro ε hε
  refine ⟨ε / (1 / 4 * ‖u₀‖ + 1), by positivity, fun t ht htdist => ?_⟩
  simp only [Set.mem_Ioi] at ht
  rw [Real.dist_eq, sub_zero, abs_of_pos ht] at htdist
  -- htdist : t < ε / (1/4 * ‖u₀‖ + 1)
  -- Rewrite max 0 t = t (since t > 0)
  have htmax : max 0 t = t := max_eq_right ht.le
  have hcong : corrSemigroup s (max 0 t) (le_max_left 0 t) u₀ =
               corrSemigroup s t ht.le u₀ := by
    simp only [htmax]
  rw [dist_eq_norm, hcong]
  have hbound := hlip t ht.le u₀
  have hpos : (0 : ℝ) < 1 / 4 * ‖u₀‖ + 1 := by positivity
  calc ‖corrSemigroup s t ht.le u₀ - u₀‖
      ≤ 1 / 4 * t * ‖u₀‖ := hbound
    _ < ε := by nlinarith [norm_nonneg u₀, (lt_div_iff hpos).mp htdist]

/-! ## V. NS_WeakInitCont_OPEN from orbit closure -/

/-- **Phase 32: NS_WeakInitCont_OPEN from orbit closure (0 sorry).**

    MATHEMATICAL ARGUMENT:
      Given:
        h3   : NS_AdjointIntegralConst_OPEN s     (B.3, existing named gap)
        hmom : NS_WeakMomentumDiffAt_OPEN s        (B.1, existing named gap)
        hlip : NS_CorrSemigroupLipAtZero_OPEN s    (new named gap, ~1 week)

      For any WeakNS u u_0 (f=0) and test psi:
        1. From B.3 (using Gap A proved = NS_CorrSemigroupGenerator_PROVED):
           u tau = corrSemigroup s tau u_0  for all tau >= 0.
        2. From corrSemigroup_tendsto_id_atZero (hlip):
           corrSemigroup s tau u_0 -> u_0 in Hdiv_free(s+2) as tau -> 0+.
        3. By continuity of inner(., psi): inner(corrSem tau u_0, psi) -> inner(u_0, psi).
        4. By (1) on Ioi 0: inner(u tau, psi) = inner(corrSem tau u_0, psi).
        5. By (3)+(4): inner(u tau, psi) -> inner(u_0, psi).

    AXIOM FOOTPRINT: classical trio + h3 + hmom + hlip.
    No NS_StokesMaxReg_OPEN needed.
    #print axioms ns_weakInitCont_from_orbit = classical trio (given h3, hmom, hlip). -/
theorem ns_weakInitCont_from_orbit
    (h3   : NS_AdjointIntegralConst_OPEN s)
    (hmom : NS_WeakMomentumDiffAt_OPEN s)
    (hlip : NS_CorrSemigroupLipAtZero_OPEN s) :
    NS_WeakInitCont_OPEN s := by
  intro u u₀ hweak ψ
  -- Step 1: orbit identification u tau = corrSemigroup s tau u₀ for tau >= 0
  -- NS_AdjointIntegralConst_OPEN takes: u u₀ f hweak hmom gap_A
  -- Gap A is NS_CorrSemigroupGenerator_PROVED (proved unconditionally in Phase 22)
  have horb : ∀ τ : ℝ, 0 ≤ τ →
      u τ = corrSemigroup s (max 0 τ) (le_max_left 0 τ) u₀ :=
    h3 u u₀ (fun _ => (0 : Hdiv_free (s + 2))) hweak hmom NS_CorrSemigroupGenerator_PROVED
  -- Step 2: corrSemigroup s tau u₀ -> u₀ as tau -> 0+ (C_0 property)
  have htend : Filter.Tendsto
      (fun τ => corrSemigroup s (max 0 τ) (le_max_left 0 τ) u₀)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds u₀) :=
    corrSemigroup_tendsto_id_atZero hlip u₀
  -- Step 3: inner product continuity: inner(corrSem tau u₀, ψ) -> inner(u₀, ψ)
  have hgcont : Continuous
      (fun v : Hdiv_free (s + 2) => @inner ℂ (Hdiv_free (s + 2)) _ v ψ) :=
    continuous_id.inner continuous_const
  have hinner : Filter.Tendsto
      (fun τ => @inner ℂ (Hdiv_free (s + 2)) _
                       (corrSemigroup s (max 0 τ) (le_max_left 0 τ) u₀) ψ)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (@inner ℂ (Hdiv_free (s + 2)) _ u₀ ψ)) :=
    hgcont.continuousAt.tendsto.comp htend
  -- Step 4+5: on Ioi 0, u tau = corrSem tau u₀, so inner(u tau, ψ) = inner(corrSem, ψ)
  apply hinner.congr'
  apply Filter.eventually_nhdsWithin_of_forall
  intro τ hτ
  simp only [Set.mem_Ioi] at hτ
  -- Need: inner(corrSem (max 0 τ) u₀, ψ) = inner(u τ, ψ)
  congr 1
  exact (horb τ hτ.le).symm

/-! ## VI. Degenerate case: immediate consequence -/

/-- **Phase 32: NS_WeakInitCont_Degenerate_OPEN CLOSED (0 sorry).**

    The orbit route proves the FULL NS_WeakInitCont_OPEN (not just the degenerate case).
    The degenerate case follows immediately (extra hypothesis _hdeg is not needed).

    COMPARED TO PHASE 31 ROUTE (degenerate case via MaxReg):
      Phase 31: NS_WeakInitCont_Degenerate_OPEN <- NS_StokesMaxReg_OPEN (6-18 months)
      Phase 32: NS_WeakInitCont_Degenerate_OPEN <- B.1 + B.3 + LipAtZero (1 week + existing)

    AXIOM FOOTPRINT: classical trio + NS_AdjointIntegralConst_OPEN
                     + NS_WeakMomentumDiffAt_OPEN + NS_CorrSemigroupLipAtZero_OPEN.
    No NS_StokesMaxReg_OPEN. No NS_WeakInitCont_Degenerate_OPEN.

    #print axioms ns_weakInitCont_degenerate_from_orbit = classical trio (given h3, hmom, hlip). -/
theorem ns_weakInitCont_degenerate_from_orbit
    (h3   : NS_AdjointIntegralConst_OPEN s)
    (hmom : NS_WeakMomentumDiffAt_OPEN s)
    (hlip : NS_CorrSemigroupLipAtZero_OPEN s) :
    NS_WeakInitCont_Degenerate_OPEN s := by
  intro u u₀ hweak ψ _hdeg
  -- The orbit route gives the full NS_WeakInitCont_OPEN, degenerate condition is not needed
  exact ns_weakInitCont_from_orbit h3 hmom hlip u u₀ hweak ψ

/-! ## VII. Closure chain back to Phase 30 -/

/-- **Phase 32 -> Phase 30: NS_AdjointPackage_PartB_OPEN from orbit route (0 sorry).**
    #print axioms NS_AdjointPackage_PartB_from_orbit = classical trio (given h3, hmom, hlip). -/
theorem NS_AdjointPackage_PartB_from_orbit
    (h3   : NS_AdjointIntegralConst_OPEN s)
    (hmom : NS_WeakMomentumDiffAt_OPEN s)
    (hlip : NS_CorrSemigroupLipAtZero_OPEN s) :
    NS_AdjointPackage_PartB_OPEN s :=
  NS_AdjointPackage_PartB_from_weakInitCont
    (ns_weakInitCont_from_orbit h3 hmom hlip)

/-! ## VIII. Phase 32 gap accounting -/

/-- **Phase 32 gap accounting (0 sorry throughout).**

    PROVED IN PHASE 32 (classical trio, 0 cert axioms):
      corrSemigroupSymbol_sub_one_le       -- |corrSemSym t xi - 1| <= 1/4 * t  (t >= 0)
      corrSemigroup_tendsto_id_atZero      -- corrSem s t u_0 -> u_0 (given hlip)
      ns_weakInitCont_from_orbit           -- FULL NS_WeakInitCont_OPEN (given B.1+B.3+hlip)
      ns_weakInitCont_degenerate_from_orbit -- degenerate case follows immediately
      NS_AdjointPackage_PartB_from_orbit   -- Part B from orbit (given B.1+B.3+hlip)

    NAMED OPEN DEFS AFTER PHASE 32 (changes from Phase 31):
      ELIMINATED: NS_WeakInitCont_Degenerate_OPEN (~2 wks, needed MaxReg)
      ADDED:      NS_CorrSemigroupLipAtZero_OPEN  (~1 week, Phase 26 Lp API template)

    FULL NAMED OPEN DEF LIST (NS Tower after Phase 32):
      NS_StokesMaxReg_OPEN s              -- Hieber-Pruss, ~6-18 months (UNCHANGED)
      NS_WeakMomentumDiffAt_OPEN s        -- B.1: WeakMomentum HasDerivAt, ~1-3 months
      NS_AdjointIntegralConst_OPEN s      -- B.3: orbit ID via adjoint, ~2-4 months
      NS_CorrSemigroupLipAtZero_OPEN s    -- C_0 semigroup norm bound, ~1 week (NEW)

    NS_WeakInitCont_OPEN: NOW PROVABLE from B.1 + B.3 + LipAtZero alone.
    No MaxReg dependency for NS_WeakInitCont_OPEN/Degenerate.
    NS Clay Surface #1: LOCKED OPEN. No Clay claim.
    CERT AXIOMS: classical trio only. -/
theorem phase32_gap_accounting : True := trivial

end TheoremaAureum.Towers.NS.CorrSemigroupContinuity
