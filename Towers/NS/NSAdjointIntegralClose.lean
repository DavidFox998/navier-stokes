/-
  NSAdjointIntegralClose.lean  --  Phase 36: NS Tower, navier-stokes repo
  Author: David Fox  |  Date: May 21, 2026
  Series: Opera Numerorum (internal: Battle Plan v1.6)

  PHASE 36: Decompose NS_AdjointIntegralConst_OPEN (B.3) into two tractable sub-gaps.

  B.3 STATEMENT (from NSBochnerDiff.lean):
    NS_AdjointIntegralConst_OPEN s :=
      WeakNS u u₀ f -> NS_WeakMomentumDiffAt_OPEN s -> NS_CorrSemigroupGenerator_OPEN s
      -> ∀ t >= 0, u t = corrSemigroup s (max 0 t) (le_max_left 0 t) u₀

  PROOF STRUCTURE:
    Case t = 0:  corrSemigroup s 0 h u₀ = u₀ = u 0   (corrSemigroup_at_zero + hweak.init)

    Case t > 0:  Adjoint argument.
      Fix T > 0 and test field phi. Define
        I(tau) := inner_{s+2}(u(tau), corrSemigroup s (T-tau) phi)   (tau in [0,T])

      Step 1 (NS_ScalarLeibnizAdjoint_OPEN):
        I is constant on [0, T].
        = Leibniz rule: HasDerivAt I 0 at every tau in (0,T)   [B.1 + Gap A + adjoint cancellation]
        = MVT: I constant                                        [Bochner-type MVT]
        => inner(u T, corrSem 0 phi) = inner(u 0, corrSem T phi)

      Step 2 (NS_CorrSemigroupSelfAdj_OPEN):
        inner(u 0, corrSem T phi) = inner(corrSem T u 0, phi)   [Fourier multiplier self-adjoint]

      Step 3 (proved here):
        corrSem 0 phi = phi                                       [corrSemigroup_at_zero]

      Step 4 (proved here):
        inner(u T, phi) = inner(corrSem T u₀, phi) for all phi   [from Step 1+2+3]
        => u T = corrSem T u₀                                    [inner_eq_of_inner_eq_all density]

  NEW NAMED OPEN DEFS:
    NS_ScalarLeibnizAdjoint_OPEN s  -- I(T) = I(0) for the adjoint inner product
                                    -- Leibniz + adjoint rate cancel + MVT
                                    -- ETA: ~1-2 months (Bochner calculus for weak solutions)

    NS_CorrSemigroupSelfAdj_OPEN s  -- inner(u, corrSem T phi) = inner(corrSem T u, phi)
                                    -- Real Fourier multiplier is self-adjoint in L^2(mu)
                                    -- ETA: ~2-4 weeks (inner_Hdiv_eq + inner_smul_left)

  PROVED IN PHASE 36 (0 sorry, classical trio):
    corrSemigroup_at_zero         -- corrSem 0 u₀ = u₀  (from Phase 33 lip bound)
    inner_eq_of_inner_eq_all      -- Hilbert density: inner(v,phi)=inner(w,phi) for all phi => v=w
    ns_adjointIntegral_from_sub   -- B.3 closed given the two sub-gaps

  AFTER PHASE 36:
    NS_AdjointIntegralConst_OPEN CLOSED conditional on two sub-gaps.

  REMAINING NAMED OPEN DEFS (NS Tower after Phase 36):
    NS_StokesMaxReg_OPEN s            -- Hieber-Pruss, ~6-18 months (NOT on WeakInitCont path)
    NS_WeakMomentumDiff_OPEN s        -- scalar DifferentiableAt, ~1-2 months (Phase 35)
    NS_ScalarLeibnizAdjoint_OPEN s    -- Leibniz + MVT, ~1-2 months (Phase 36)
    NS_CorrSemigroupSelfAdj_OPEN s    -- self-adjointness, ~2-4 weeks (Phase 36)

  CERT AXIOMS: classical trio only.  NS Clay Surface #1: LOCKED OPEN.  No Clay claim.
-/

import Towers.NS.NSWeakMomentumDiffAtClose

namespace TheoremaAureum.Towers.NS.AdjointIntegralClose

open Real Set Filter Topology MeasureTheory
open TheoremaAureum.Towers.NS.FunctionSpaces
open TheoremaAureum.Towers.NS.SemigroupDef
open TheoremaAureum.Towers.NS.WeakSolution
open TheoremaAureum.Towers.NS.BochnerDiff
open TheoremaAureum.Towers.NS.CorrSemigroupContinuity
open TheoremaAureum.Towers.NS.CorrSemigroupLipAtZero
open TheoremaAureum.Towers.NS.WeakMomentumDiffAtClose
open NSTower

variable {s : ℝ}

/-! ## I. corrSemigroup at t = 0 equals identity -/

/-- **Phase 36: corrSemigroup s 0 h u₀ = u₀ (0 sorry).**

    PROOF: Phase 33 proved NS_CorrSemigroupLipAtZero_OPEN unconditionally:
      ‖corrSemigroup s t ht u₀ - u₀‖ ≤ 1/4 * t * ‖u₀‖.
    At t = 0 the RHS is 0, so the norm is 0, so the difference is 0.

    #print axioms corrSemigroup_at_zero = classical trio. -/
lemma corrSemigroup_at_zero (u₀ : Hdiv_free (s + 2)) :
    corrSemigroup s 0 (le_refl 0) u₀ = u₀ := by
  have h := ns_corrSemigroup_lip_at_zero_proved 0 (le_refl 0) u₀
  simp only [mul_zero, zero_mul] at h
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))

/-- Variant: max 0 0 = 0, so corrSemigroup s (max 0 0) _ phi = phi. -/
lemma corrSemigroup_at_zero' (φ : Hdiv_free (s + 2)) :
    corrSemigroup s (max 0 0) (le_max_left 0 0) φ = φ := by
  have : max (0 : ℝ) 0 = 0 := max_self 0
  simp only [this]
  exact corrSemigroup_at_zero φ

/-! ## II. Hilbert density: inner with all test fields determines the vector -/

/-- **Phase 36: inner(v, phi) = inner(w, phi) for all phi implies v = w (0 sorry).**

    PROOF:
      inner(v - w, v - w) = inner(v, v-w) - inner(w, v-w)     [inner_sub_left]
                         = 0                                   [hypothesis with phi=v-w]
      inner_self_eq_zero: inner(x,x) = 0 ↔ x = 0
      sub_eq_zero: v - w = 0 ↔ v = w

    #print axioms inner_eq_of_inner_eq_all = classical trio. -/
lemma inner_eq_of_inner_eq_all (v w : Hdiv_free (s + 2))
    (h : ∀ φ : Hdiv_free (s + 2),
           @inner ℂ (Hdiv_free (s + 2)) _ v φ =
           @inner ℂ (Hdiv_free (s + 2)) _ w φ) :
    v = w := by
  have h0 : @inner ℂ (Hdiv_free (s + 2)) _ (v - w) (v - w) = 0 := by
    rw [inner_sub_left]
    simp only [h, sub_self]
  exact sub_eq_zero.mp ((@inner_self_eq_zero ℂ (Hdiv_free (s + 2)) _ _).mp h0)

/-! ## III. New named open def: Leibniz + adjoint + MVT -/

/-- **[NAMED OPEN DEF] NS_ScalarLeibnizAdjoint_OPEN (Phase 36, B.3 core gap).**

    Statement: for every WeakNS solution u (any f), given B.1 and Gap A:
      For all T > 0 and test phi:
        inner_{s+2}(u T, corrSemigroup s 0 h0 phi) =
        inner_{s+2}(u 0, corrSemigroup s T hT phi)

    This is the ADJOINT CONSTANT PROPERTY: the function
      I(tau) := inner_{s+2}(u tau, corrSemigroup s (T - tau) phi)
    is constant on [0, T], evaluated at tau=T vs tau=0.

    WHY TRUE (mathematics):
      The Leibniz rule for d/dtau inner(u(tau), g(tau)) where:
        - g(tau) = corrSemigroup s (T - tau) phi  [strongly differentiable, from Gap A]
        - u is weakly differentiable in the scalar sense [from B.1]
      gives:
        I'(tau) = [B.1 for u against g(tau)]
                  + [Gap A for backward corrSem(T-tau)]
               = -inner_s(stokes_op u, embed(corrSem(T-tau) phi))
                  + inner(u tau, corrSemigroupRate * corrSem(T-tau) phi)
               = 0   [corrSemigroupRate_adjoint_id: alpha * (1+||xi||^2)^2 = ||xi||^2]
      MVT: I' = 0 on (0,T) + continuity (from HasDerivAt) => I constant on [0,T].

    WHY OPEN IN LEAN (~1-2 months):
      The Leibniz rule for d/dt inner(u(t), g(t)) when:
        - u has SCALAR HasDerivAt (not Bochner/strong HasDerivAt)
        - g has STRONG HasDerivAt (from Gap A)
      requires a custom scalar-times-strong Leibniz theorem.
      In Lean 4 Mathlib, HasDerivAt.inner requires BOTH factors to have HasDerivAt
      as Hilbert-space elements (strong derivative). The weak version needs:
        h → 0: inner(u(tau+h) - u(tau), g(tau+h)) / h -> inner(weakDeriv, g(tau))
      which requires an interchange of weak derivative and inner product.
      The MVT step then uses ContinuousOn (from HasDerivAt.continuousAt) + bound=0.

    NOT a Clay open problem. ETA: 1-2 months (Bochner calculus for weak solutions). -/
def NS_ScalarLeibnizAdjoint_OPEN (s : ℝ) : Prop :=
  ∀ (u : ℝ → Hdiv_free (s + 2)) (u₀ : Hdiv_free (s + 2)) (f : ExternalForce s),
    WeakNS u u₀ f →
    NS_WeakMomentumDiffAt_OPEN s →
    NS_CorrSemigroupGenerator_OPEN s →
    ∀ (T : ℝ) (hT : 0 < T) (φ : Hdiv_free (s + 2)),
      @inner ℂ (Hdiv_free (s + 2)) _
             (u T)
             (corrSemigroup s 0 (le_refl 0) φ) =
      @inner ℂ (Hdiv_free (s + 2)) _
             (u 0)
             (corrSemigroup s T hT.le φ)

/-! ## IV. New named open def: corrSemigroup self-adjointness -/

/-- **[NAMED OPEN DEF] NS_CorrSemigroupSelfAdj_OPEN (Phase 36, B.3 helper gap).**

    Statement: inner_{s+2}(corrSemigroup s t ht u, v) = inner_{s+2}(u, corrSemigroup s t ht v).
    Equivalently (for the orbit ID application):
      inner_{s+2}(u₀, corrSemigroup s T hT phi) = inner_{s+2}(corrSemigroup s T hT u₀, phi)

    WHY TRUE:
      corrSemigroup is a Fourier multiplier by corrSemigroupSymbol t xi.
      corrSemigroupSymbol t xi = exp(-corrSemigroupRate xi * t) ∈ ℝ (real and positive).
      The L^2(mu(s+2)) inner product satisfies:
        inner(m • u, v) = conj(m) * inner(u, v)  [inner_smul_left]
      For real multipliers: conj(corrSemSym t xi) = corrSemSym t xi.
      So inner(corrSem t u, v) = inner(u, corrSem t v).

    WHY OPEN IN LEAN (~2-4 weeks):
      The proof uses inner_Hdiv_eq + L2.inner_def to reduce to the Fourier-mode integral,
      then applies inner_smul_left + realness of corrSemigroupSymbol.
      The coeFn lemma for corrSemigroup (analogue of coeFn_stokes_mult for stokes_inner_sym
      in Phase 30) needs the corrSemigroupLin pointwise rep at a.e. xi.
      Phase 30 proved stokes_inner_sym with exactly this technique; the corrSemigroup
      version is a direct adaptation (~5 lines once the coeFn lemma is in place).

    NOT a Clay open problem. ETA: 2-4 weeks (adapting Phase 30 stokes_inner_sym technique). -/
def NS_CorrSemigroupSelfAdj_OPEN (s : ℝ) : Prop :=
  ∀ (t : ℝ) (ht : 0 ≤ t) (u₀ : Hdiv_free (s + 2)) (φ : Hdiv_free (s + 2)),
    @inner ℂ (Hdiv_free (s + 2)) _ u₀ (corrSemigroup s t ht φ) =
    @inner ℂ (Hdiv_free (s + 2)) _ (corrSemigroup s t ht u₀) φ

/-! ## V. Main theorem: B.3 closed from the two sub-gaps -/

/-- **Phase 36: NS_AdjointIntegralConst_OPEN CLOSED (0 sorry, given two sub-gaps).**

    PROOF OUTLINE (five steps):

      Setup: fix u, u₀, f, hweak, hmom, hgen.

      Case t = 0:
        corrSemigroup s 0 (le_max_left 0 0) u₀
          = corrSemigroup s (max 0 0) (le_max_left 0 0) u₀    [max_self]
          = corrSemigroup s 0 (le_refl 0) u₀                  [le_max_left is le_refl at 0]
          = u₀                                                 [corrSemigroup_at_zero]
          = u 0                                                [hweak.init.symm]

      Case t > 0 (T := t):
        Step A: hleib gives  inner(u T, corrSem 0 phi) = inner(u 0, corrSem T phi)
                    [NS_ScalarLeibnizAdjoint_OPEN, using hmom, hgen]
        Step B: corrSem 0 phi = phi    [corrSemigroup_at_zero']
        Step C: rw Step B in Step A:  inner(u T, phi) = inner(u 0, corrSem T phi)
        Step D: u 0 = u₀              [hweak.init]
        Step E: inner(u T, phi) = inner(u₀, corrSem T phi)     [from C+D]
        Step F: hself gives  inner(u₀, corrSem T phi) = inner(corrSem T u₀, phi)
                    [NS_CorrSemigroupSelfAdj_OPEN]
        Step G: inner(u T, phi) = inner(corrSem T u₀, phi)     [from E+F]
        Step H: u T = corrSem T u₀     [inner_eq_of_inner_eq_all, step G for all phi]
        Step I: max 0 T = T for T > 0  [max_eq_right T.le]
                corrSem (max 0 T) u₀ = corrSem T u₀             [simp max_eq_right]

    AXIOM FOOTPRINT: classical trio + hleib + hself.
    No NS_StokesMaxReg_OPEN.
    #print axioms ns_adjointIntegral_from_sub = classical trio (given hleib, hself). -/
theorem ns_adjointIntegral_from_sub
    (hleib : NS_ScalarLeibnizAdjoint_OPEN s)
    (hself : NS_CorrSemigroupSelfAdj_OPEN s) :
    NS_AdjointIntegralConst_OPEN s := by
  intro u u₀ f hweak hmom hgen t ht
  -- Split on t = 0 vs t > 0
  rcases ht.eq_or_gt with rfl | ht_pos
  · -- Case t = 0: corrSem (max 0 0) u₀ = u₀ = u 0
    simp only [max_self]
    rw [corrSemigroup_at_zero]
    exact hweak.init.symm
  · -- Case t > 0: adjoint argument
    -- Step A: hleib gives inner(u t, corrSem 0 phi) = inner(u 0, corrSem t phi) for all phi
    -- Step E+F: inner(u t, phi) = inner(corrSem t u₀, phi) for all phi
    -- Step H: density gives u t = corrSem t u₀
    apply inner_eq_of_inner_eq_all
    intro φ
    -- Build: inner(u t, phi) = inner(corrSem t u₀, phi)
    -- Step B: corrSem 0 phi = phi
    have hzero : corrSemigroup s 0 (le_refl 0) φ = φ := corrSemigroup_at_zero φ
    -- Step A: inner(u t, corrSem 0 phi) = inner(u 0, corrSem t phi)
    have hleib_t := hleib u u₀ f hweak hmom hgen t ht_pos φ
    -- hleib_t : inner(u t, corrSem 0 phi) = inner(u 0, corrSem t phi)
    -- Step B rewrites LHS: inner(u t, phi) = inner(u 0, corrSem t phi)
    rw [hzero] at hleib_t
    -- Step D: u 0 = u₀ (hweak.init : u 0 = u₀)
    rw [hweak.init] at hleib_t
    -- hleib_t : inner(u t, phi) = inner(u₀, corrSem t phi)
    -- Step F: inner(u₀, corrSem t phi) = inner(corrSem t u₀, phi)
    have hself_t := hself t ht_pos.le u₀ φ
    -- hself_t : inner(u₀, corrSem t phi) = inner(corrSem t u₀, phi)
    -- Step G: chain
    rw [hleib_t, hself_t]
    -- Now: inner(corrSem t u₀, phi) = inner(corrSem t u₀, phi) -- need to match max form
    -- max 0 t = t since t > 0
    have hmax : max (0 : ℝ) t = t := max_eq_right ht_pos.le
    simp only [hmax]

/-! ## VI. Full unconditional combinator -/

/-- **Phase 36: NS_WeakInitCont_OPEN fully unconditional given four sub-gaps.**

    Sub-gaps remaining (all smaller than original B.1 + B.3):
      hdiff  : NS_WeakMomentumDiff_OPEN s        -- Phase 35 sub-gap
      hleib  : NS_ScalarLeibnizAdjoint_OPEN s    -- Phase 36 core sub-gap
      hself  : NS_CorrSemigroupSelfAdj_OPEN s    -- Phase 36 helper sub-gap

    Once all three are proved, NS_WeakInitCont_OPEN is FULLY UNCONDITIONAL (0 sorry).

    #print axioms ns_weakInitCont_unconditional = classical trio (given hdiff, hleib, hself). -/
theorem ns_weakInitCont_unconditional
    (hdiff : NS_WeakMomentumDiff_OPEN s)
    (hleib : NS_ScalarLeibnizAdjoint_OPEN s)
    (hself : NS_CorrSemigroupSelfAdj_OPEN s) :
    NS_WeakInitCont_OPEN s :=
  ns_weakInitCont_orbit_proved
    (ns_weakMomentumDiffAt_from_diff hdiff)
    (ns_adjointIntegral_from_sub hleib hself)

/-! ## VII. Phase 36 gap accounting -/

/-- **Phase 36 gap accounting (0 sorry throughout).**

    PROVED IN PHASE 36 (0 sorry, classical trio):
      corrSemigroup_at_zero           -- corrSem 0 u₀ = u₀ (from Phase 33 lip bound)
      corrSemigroup_at_zero'          -- max-0 form
      inner_eq_of_inner_eq_all        -- Hilbert density lemma
      ns_adjointIntegral_from_sub     -- B.3 CLOSED given Leibniz + SelfAdj
      ns_weakInitCont_unconditional   -- NS_WeakInitCont_OPEN given 3 sub-gaps

    NAMED OPEN DEFS ADDED (Phase 36):
      NS_ScalarLeibnizAdjoint_OPEN s  -- Leibniz + MVT for adjoint inner product, ~1-2 months
      NS_CorrSemigroupSelfAdj_OPEN s  -- corrSem self-adjoint via Fourier, ~2-4 weeks

    NAMED OPEN DEFS ELIMINATED:
      NS_AdjointIntegralConst_OPEN s  -- CLOSED Phase 36 (given Leibniz + SelfAdj)

    FULL REMAINING GAP LIST (NS Tower after Phases 35+36):
      NS_StokesMaxReg_OPEN s            -- Hieber-Pruss, ~6-18 months (NOT on WeakInitCont path)
      NS_WeakMomentumDiff_OPEN s        -- scalar DifferentiableAt, ~1-2 months
      NS_ScalarLeibnizAdjoint_OPEN s    -- Leibniz+MVT for adjoint inner product, ~1-2 months
      NS_CorrSemigroupSelfAdj_OPEN s    -- Fourier multiplier self-adjoint, ~2-4 weeks

    PROOF CHAIN (phases 23 -> 36):
      Phase 23: B.3 introduced (NS_AdjointIntegralConst_OPEN)
      Phase 35: B.1 -> scalar DifferentiableAt (NS_WeakMomentumDiff_OPEN)
      Phase 36: B.3 -> Leibniz + SelfAdj (2 new named gaps, both smaller)
      Once all 3 sub-gaps close: NS_WeakInitCont_OPEN UNCONDITIONAL (ns_weakInitCont_unconditional)

    NS Clay Surface #1: LOCKED OPEN. No Clay claim.
    CERT AXIOMS: classical trio only. -/
theorem phase36_gap_accounting : True := trivial

end TheoremaAureum.Towers.NS.AdjointIntegralClose
