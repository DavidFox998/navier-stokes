/-
  NSPhase42ZeroForcing.lean  --  Phase 42: NS Tower, navier-stokes repo
  Author: David Fox  |  Date: May 21, 2026
  Series: Opera Numerorum (internal: Battle Plan v1.6)

  PHASE 42: Zero-Forcing Orbit Closure.

  For WeakNS solutions with f = 0 (zero external forcing):
    u t = corrSemigroup s (max 0 t) (le_max_left 0 t) u0   for all t >= 0.

  This closes NS_AdjointIntegralConst_OPEN for the zero-forcing case WITHOUT
  requiring NS_ForcingOrbitZero_OPEN (the Duhamel hypothesis). The key
  simplification: inner(0, v) = 0 by inner_zero_left.

  ARCHITECTURE (recap from Phases 39-41):
    Phase 39 proved NS_ScalarLeibnizAdjoint_PROVED conditional on 5 named defs.
    Phase 40 closed: NS_AdjointInnerDerivMap_PROVED, NS_AdjointSymmetry_PROVED.
    Phase 41 closed: NS_BackwardDerivMap_PROVED, NS_FuncIContOn_PROVED.
    Remaining open: NS_ForcingOrbitZero_OPEN (Duhamel principle, general f).

    For f = 0: forcing term inner(f tau, corrSem(T-tau) phi)
                           = inner(0, ...) = 0  by inner_zero_left.
    This closes the gap without Duhamel theory.

  PROVED (0 sorry, 0 cert axioms, classical trio only):

    NS_ScalarLeibnizDerivZero_ZF_PROVED
      HasDerivAt I 0 tau for I(tau) = inner(u tau, corrSem(T-tau) phi), f = 0.
      Proof: mirrors Phase 39, replacing hfz with inner_zero_left.

    NS_ScalarLeibnizAdjoint_ZF_PROVED
      inner(u T, corrSem 0 phi) = inner(u 0, corrSem T phi) for f = 0 WeakNS.
      Proof: MVT on I (derivative = 0 everywhere, I continuous on [[0,T]]).
      sub_eq_zero.mp closes the Complex equality (linarith fails on C).

    NS_AdjointIntegralConst_ZF_PROVED
      u t = corrSemigroup s (max 0 t) (le_max_left 0 t) u0 for f = 0 WeakNS.
      Proof: mirrors ns_adjointIntegral_from_sub (Phase 36).
      t = 0: exact hweak.init (NOT .symm; conclusion is u 0 = u0).
      t > 0: inner_eq_of_inner_eq_all + Adjoint_ZF + CorrSemigroupSelfAdj_PROVED.

  REMAINING NAMED OPEN DEFS (NS Tower after Phase 42):
    NS_ForcingOrbitZero_OPEN s       -- general f: Duhamel principle needed
    NS_CorrSemigroupFourierEq_OPEN s -- deepest Phase 17 gap (WeakInitCont chain)
    NS_StokesMaxReg_OPEN s           -- Hieber-Pruss 2018 (independent chain)

  NOTE: NS_AdjointIntegralConst_OPEN is closed for f = 0 here.
  The general-f case remains open (NS_ForcingOrbitZero_OPEN).

  CERT AXIOMS: classical trio only.
  NS Clay Surface #1: LOCKED OPEN.  No Clay Millennium Prize claim.
-/

import Towers.NS.NSPhase41ThreeGaps
import Towers.NS.NSCorrSemigroupSelfAdj

namespace TheoremaAureum.Towers.NS.Phase42ZeroForcing

open Real Set Filter Topology MeasureTheory
open TheoremaAureum.Towers.NS.FunctionSpaces
open TheoremaAureum.Towers.NS.SemigroupDef
open TheoremaAureum.Towers.NS.WeakSolution
open TheoremaAureum.Towers.NS.BochnerDiff
open TheoremaAureum.Towers.NS.GeneratorClose
open TheoremaAureum.Towers.NS.DerivSemigroup
open TheoremaAureum.Towers.NS.AdjointSymmetry
open TheoremaAureum.Towers.NS.Phase40AdjClose
open TheoremaAureum.Towers.NS.ScalarLeibnizAdjoint
open TheoremaAureum.Towers.NS.Phase41ThreeGaps
open TheoremaAureum.Towers.NS.AdjointIntegralClose
open TheoremaAureum.Towers.NS.CorrSemigroupSelfAdj
open NSTower

variable {s : ℝ}

/-! ## I. DerivZero_ZF: I'(tau) = 0 for f = 0 WeakNS solutions -/

/-- **Phase 42: HasDerivAt I 0 for f = 0 WeakNS (0 sorry, classical trio).**

    For u a WeakNS solution with hf : all tau, f tau = 0:
      I(tau) := inner(u tau, corrSem(max 0 (T-tau)) phi)
    satisfies HasDerivAt I 0 at every tau in (0, T).

    PROOF (mirrors NS_ScalarLeibnizDerivZero_PROVED, Phase 39):
      Leibniz rule: I'(tau) = inner(D, g) + inner(u tau, (-1) * D_g)
      TERM1: inner(D, g) = -stokes_val + inner(f tau, g) = -stokes_val + 0
             (f tau = 0, so inner(0, g) = 0 by inner_zero_left)
      TERM2: inner(u tau, (-1) * D_g) = stokes_val   (Phase 40 symmetry)
      NET: -stokes_val + stokes_val = 0.

    No NS_ForcingOrbitZero_OPEN needed.
    #print axioms NS_ScalarLeibnizDerivZero_ZF_PROVED = classical trio. -/
theorem NS_ScalarLeibnizDerivZero_ZF_PROVED
    (u   : ℝ → Hdiv_free (s + 2)) (u₀ : Hdiv_free (s + 2)) (f : ExternalForce s)
    (hweak : WeakNS u u₀ f)
    (hf   : ∀ τ : ℝ, f τ = (0 : Hdiv_free (s + 2)))
    (T : ℝ) (hT : 0 < T) (φ : Hdiv_free (s + 2))
    (τ : ℝ) (hτ : 0 < τ) (hτT : τ < T) :
    HasDerivAt
      (fun t => @inner ℂ (Hdiv_free (s + 2)) _ (u t)
                  (corrSemigroup s (max 0 (T - t)) (le_max_left 0 (T - t)) φ))
      (0 : ℂ) τ := by
  have hTτ_pos : (0 : ℝ) < T - τ := by linarith
  let g_max := corrSemigroup s (max 0 (T - τ)) (le_max_left 0 (T - τ)) φ
  let g_sub  := corrSemigroup s (T - τ) hTτ_pos.le φ
  let D_g    := corrSemigroupDerivMap s (T - τ) hTτ_pos.le φ
  have hmax : max (0 : ℝ) (T - τ) = T - τ := max_eq_right hTτ_pos.le
  have hg_eq : g_max = g_sub := by
    show corrSemigroup s (max 0 (T - τ)) (le_max_left 0 (T - τ)) φ =
         corrSemigroup s (T - τ) hTτ_pos.le φ
    congr 1
    · exact hmax
    · exact Subsingleton.elim _ _
  obtain ⟨D, hD_u, hD_val⟩ := hweak.momentum τ hτ.le
  have hback_τ : HasDerivAt
      (fun t => corrSemigroup s (max 0 (T - t)) (le_max_left 0 (T - t)) φ)
      ((-1 : ℝ) • D_g) τ :=
    NS_BackwardDerivMap_PROVED T φ τ hTτ_pos
  have hLeibniz : HasDerivAt
      (fun t => @inner ℂ (Hdiv_free (s + 2)) _ (u t)
                  (corrSemigroup s (max 0 (T - t)) (le_max_left 0 (T - t)) φ))
      (@inner ℂ (Hdiv_free (s + 2)) _ D g_max +
       @inner ℂ (Hdiv_free (s + 2)) _ (u τ) ((-1 : ℝ) • D_g))
      τ := hD_u.inner hback_τ
  suffices hzero : @inner ℂ (Hdiv_free (s + 2)) _ D g_max +
      @inner ℂ (Hdiv_free (s + 2)) _ (u τ) ((-1 : ℝ) • D_g) = 0 by
    rwa [hzero] at hLeibniz
  rw [hg_eq]
  -- TERM1 full: inner(D, g_sub) = -stokes_val + inner(f tau, g_sub)
  have hT1_full : @inner ℂ (Hdiv_free (s + 2)) _ D g_sub =
      -@inner ℂ (Hdiv_free s) _ (stokes_op s (u τ)) (@embed (s + 2) s (by linarith) g_sub)
      + @inner ℂ (Hdiv_free (s + 2)) _ (f τ) g_sub :=
    hD_val g_sub
  -- inner(f tau, g_sub) = inner(0, g_sub) = 0
  have hfz : @inner ℂ (Hdiv_free (s + 2)) _ (f τ) g_sub = 0 := by
    rw [hf τ]; exact inner_zero_left _
  -- TERM1 simplified: inner(D, g_sub) = -stokes_val
  have hT1 : @inner ℂ (Hdiv_free (s + 2)) _ D g_sub =
      -@inner ℂ (Hdiv_free s) _ (stokes_op s (u τ)) (@embed (s + 2) s (by linarith) g_sub) := by
    rw [hT1_full, hfz, add_zero]
  -- TERM2a: inner(u tau, (-1) • D_g) = -inner(u tau, D_g)
  have hT2neg : @inner ℂ (Hdiv_free (s + 2)) _ (u τ) ((-1 : ℝ) • D_g) =
      -@inner ℂ (Hdiv_free (s + 2)) _ (u τ) D_g := by
    rw [neg_smul, one_smul, inner_neg_right]
  -- TERM2b: inner(u tau, D_g) = -stokes(corrSem(T-tau)(u tau), embed phi)
  have hT2b : @inner ℂ (Hdiv_free (s + 2)) _ (u τ) D_g =
      -@inner ℂ (Hdiv_free s) _ (stokes_op s (corrSemigroup s (T - τ) hTτ_pos.le (u τ)))
       (@embed (s + 2) s (by linarith) φ) :=
    NS_AdjointInnerDerivMap_PROVED (T - τ) hTτ_pos.le (u τ) φ
  -- CANCELLATION: stokes(corrSem(T-tau)(u tau), embed phi) = stokes(u tau, embed g_sub)
  have hcanc : @inner ℂ (Hdiv_free s) _
      (stokes_op s (corrSemigroup s (T - τ) hTτ_pos.le (u τ)))
      (@embed (s + 2) s (by linarith) φ) =
      @inner ℂ (Hdiv_free s) _ (stokes_op s (u τ))
      (@embed (s + 2) s (by linarith) g_sub) :=
    NS_AdjointSymmetry_PROVED (T - τ) hTτ_pos.le (u τ) φ
  rw [hT2neg, hT2b, neg_neg, hcanc, hT1]
  ring

/-! ## II. Adjoint_ZF: I(T) = I(0) for f = 0 WeakNS solutions -/

/-- **Phase 42: Adjoint integral constant for f = 0 (0 sorry, classical trio).**

    For f = 0 WeakNS:
      inner(u T, corrSem 0 phi) = inner(u 0, corrSem T phi).

    PROOF: MVT on I(tau) = inner(u tau, corrSem(max 0 (T-tau)) phi).
      I' = 0 on (0, T) [NS_ScalarLeibnizDerivZero_ZF_PROVED, above].
      ContinuousOn I [[0, T]] [NS_FuncIContOn_PROVED, Phase 41].
      MVT: ||I T - I 0|| <= 0.
      sub_eq_zero.mp closes Complex equality (linarith fails on C).

    #print axioms NS_ScalarLeibnizAdjoint_ZF_PROVED = classical trio. -/
theorem NS_ScalarLeibnizAdjoint_ZF_PROVED
    (u    : ℝ → Hdiv_free (s + 2)) (u₀ : Hdiv_free (s + 2)) (f : ExternalForce s)
    (hweak : WeakNS u u₀ f)
    (hf   : ∀ τ : ℝ, f τ = (0 : Hdiv_free (s + 2)))
    (T : ℝ) (hT : 0 < T) (φ : Hdiv_free (s + 2)) :
    @inner ℂ (Hdiv_free (s + 2)) _
           (u T) (corrSemigroup s 0 (le_refl 0) φ) =
    @inner ℂ (Hdiv_free (s + 2)) _
           (u 0) (corrSemigroup s T hT.le φ) := by
  set I : ℝ → ℂ := fun τ =>
    @inner ℂ (Hdiv_free (s + 2)) _ (u τ)
      (corrSemigroup s (max 0 (T - τ)) (le_max_left 0 (T - τ)) φ) with hI_def
  have hIT : I T = @inner ℂ (Hdiv_free (s + 2)) _ (u T)
      (corrSemigroup s 0 (le_refl 0) φ) := by
    simp only [hI_def, sub_self, max_self]
    congr 1; exact Subsingleton.elim _ _
  have hI0 : I 0 = @inner ℂ (Hdiv_free (s + 2)) _ (u 0)
      (corrSemigroup s T hT.le φ) := by
    simp only [hI_def, sub_zero, max_eq_right hT.le]
    congr 1; exact Subsingleton.elim _ _
  rw [← hIT, ← hI0]
  have hI_cont : ContinuousOn I [[0, T]] :=
    NS_FuncIContOn_PROVED u u₀ f hweak T hT φ
  have hI_deriv : ∀ τ ∈ Set.Ioo (0 : ℝ) T, HasDerivAt I 0 τ :=
    fun τ hτ =>
      NS_ScalarLeibnizDerivZero_ZF_PROVED u u₀ f hweak hf T hT φ τ hτ.1 hτ.2
  have hI_deriv0 : ∀ τ ∈ Set.Ioo (0 : ℝ) T, deriv I τ = 0 :=
    fun τ hτ => (hI_deriv τ hτ).deriv
  have hMVT : ‖I T - I 0‖ ≤ 0 * (T - 0) :=
    norm_image_sub_le_of_norm_deriv_le_segment' hI_cont
      (fun τ hτ => by simp [hI_deriv0 τ hτ])
  have hle : ‖I T - I 0‖ ≤ 0 := by
    have := mul_nonneg (le_refl (0 : ℝ)) (by linarith : (0 : ℝ) ≤ T - 0)
    linarith
  have hzero : I T - I 0 = 0 :=
    norm_eq_zero.mp (le_antisymm hle (norm_nonneg _))
  exact sub_eq_zero.mp hzero

/-! ## III. IntegralConst_ZF: orbit identification for f = 0 WeakNS -/

/-- **Phase 42: NS_AdjointIntegralConst_ZF_PROVED (0 sorry, classical trio).**

    For f = 0 WeakNS:
      u t = corrSemigroup s (max 0 t) (le_max_left 0 t) u0   for all t >= 0.

    PROOF (mirrors ns_adjointIntegral_from_sub, Phase 36):

      Case t = 0:
        After simp max_self: goal is u 0 = corrSemigroup s 0 _ u0.
        corrSemigroup_at_zero: corrSem 0 u0 = u0.
        rw [corrSemigroup_at_zero].
        exact hweak.init   (hweak.init : u 0 = u0; NOT .symm).

      Case t > 0 (T := t):
        apply inner_eq_of_inner_eq_all; intro phi.
        have hzero_phi := corrSemigroup_at_zero phi  -- corrSem 0 phi = phi
        have hleib_t := NS_ScalarLeibnizAdjoint_ZF_PROVED ... t ht_pos phi
        -- hleib_t : inner(u t, corrSem 0 phi) = inner(u 0, corrSem t phi)
        rw [hzero_phi] at hleib_t  -- inner(u t, phi) = inner(u 0, corrSem t phi)
        rw [hweak.init] at hleib_t -- inner(u t, phi) = inner(u0, corrSem t phi)
        have hself_t := NS_CorrSemigroupSelfAdj_PROVED t ht_pos.le u0 phi
        -- hself_t : inner(u0, corrSem t phi) = inner(corrSem t u0, phi)
        rw [hleib_t, hself_t]
        simp only [max_eq_right ht_pos.le]  -- max 0 t = t; proof irrelevance via simp

    #print axioms NS_AdjointIntegralConst_ZF_PROVED = classical trio. -/
theorem NS_AdjointIntegralConst_ZF_PROVED :
    ∀ (u : ℝ → Hdiv_free (s + 2)) (u₀ : Hdiv_free (s + 2)) (f : ExternalForce s),
      WeakNS u u₀ f →
      (∀ τ : ℝ, f τ = (0 : Hdiv_free (s + 2))) →
      ∀ (t : ℝ), 0 ≤ t →
        u t = corrSemigroup s (max 0 t) (le_max_left 0 t) u₀ := by
  intro u u₀ f hweak hf t ht
  rcases ht.eq_or_gt with rfl | ht_pos
  · -- Case t = 0: corrSem (max 0 0) u0 = u0 = u 0
    simp only [max_self]
    rw [corrSemigroup_at_zero]
    exact hweak.init
  · -- Case t > 0: adjoint inner product argument
    apply inner_eq_of_inner_eq_all
    intro φ
    -- corrSem 0 phi = phi
    have hzero_phi : corrSemigroup s 0 (le_refl 0) φ = φ := corrSemigroup_at_zero φ
    -- NS_ScalarLeibnizAdjoint_ZF: inner(u t, corrSem 0 phi) = inner(u 0, corrSem t phi)
    have hleib_t := NS_ScalarLeibnizAdjoint_ZF_PROVED u u₀ f hweak hf t ht_pos φ
    -- Rewrite corrSem 0 phi to phi on LHS
    rw [hzero_phi] at hleib_t
    -- Rewrite u 0 to u0 (hweak.init : u 0 = u0)
    rw [hweak.init] at hleib_t
    -- hleib_t : inner(u t, phi) = inner(u0, corrSem t phi)
    -- corrSem self-adjoint: inner(u0, corrSem t phi) = inner(corrSem t u0, phi)
    have hself_t := NS_CorrSemigroupSelfAdj_PROVED t ht_pos.le u₀ φ
    -- Chain: inner(u t, phi) = inner(corrSem t u0, phi)
    rw [hleib_t, hself_t]
    -- max 0 t = t for t > 0; proof irrelevance handled by simp
    simp only [max_eq_right ht_pos.le]

/-! ## IV. Phase 42 gap accounting -/

/-- **Phase 42 gap accounting (0 sorry, 0 cert axioms, classical trio).**

    PROVED IN PHASE 42 (classical trio, 0 cert axioms):
      NS_ScalarLeibnizDerivZero_ZF_PROVED
        HasDerivAt I 0 tau for f = 0 WeakNS (inner_zero_left closes forcing term).

      NS_ScalarLeibnizAdjoint_ZF_PROVED
        inner(u T, corrSem 0 phi) = inner(u 0, corrSem T phi) for f = 0 WeakNS.
        sub_eq_zero.mp closes Complex equality after MVT.

      NS_AdjointIntegralConst_ZF_PROVED
        u t = corrSem (max 0 t) u0 for f = 0 WeakNS (all t >= 0).
        t = 0: exact hweak.init.
        t > 0: inner_eq_of_inner_eq_all + Adjoint_ZF + CorrSemigroupSelfAdj.

    NAMED OPEN DEFS NOT ELIMINATED BY PHASE 42:
      NS_ForcingOrbitZero_OPEN s       -- general f still requires Duhamel principle
      NS_CorrSemigroupFourierEq_OPEN s -- Phase 17 deepest gap
      NS_StokesMaxReg_OPEN s           -- Hieber-Pruss (independent chain)

    WHAT PHASE 42 ACHIEVES:
      NS_AdjointIntegralConst_OPEN s is CLOSED for f = 0 solutions (Phase 42).
      For general f: remains open pending NS_ForcingOrbitZero_OPEN (Duhamel).
      The f = 0 case covers the homogeneous NSE, which is the physically
      natural setting for weak initial continuity.

    PROOF CHAIN CONTEXT (after Phase 42):
      NS_ForcingOrbitZero_OPEN s closed for f = 0 by inner_zero_left.
        => NS_ScalarLeibnizAdjoint_ZF_PROVED (Phase 42)
        => NS_AdjointIntegralConst_ZF_PROVED (Phase 42, u = corrSem u0 orbit)

      General-f path:
        NS_ForcingOrbitZero_OPEN s (OPEN: Duhamel + Phase 17 Fourier rep)
          => NS_ScalarLeibnizAdjoint_PROVED (Phase 39)
          => NS_AdjointIntegralConst_OPEN   (Phase 36)
          => NS_WeakInitCont_OPEN           (Phase 34)

    DEPENDENCY SUMMARY (NS Tower after Phase 42):
      OPEN:  NS_ForcingOrbitZero_OPEN (general f), NS_CorrSemigroupFourierEq_OPEN,
             NS_StokesMaxReg_OPEN
      CLOSED (f = 0): NS_AdjointIntegralConst_ZF_PROVED, NS_ScalarLeibnizAdjoint_ZF_PROVED

    CERT AXIOMS: classical trio only.
    NS Clay Surface #1: LOCKED OPEN.  No Clay Millennium Prize claim. -/
theorem phase42_gap_accounting : True := trivial

end TheoremaAureum.Towers.NS.Phase42ZeroForcing
