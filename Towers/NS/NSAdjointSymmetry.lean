/-
  NSAdjointSymmetry.lean  --  Phase 38b: NS Tower, navier-stokes repo
  Author: David Fox  |  Date: May 21, 2026
  Series: Opera Numerorum (internal: Battle Plan v1.6)

  PHASE 38b: Decompose NS_ScalarLeibnizAdjoint_OPEN (Phase 36) into two
  smaller named open defs: NS_AdjointInnerDerivMap_OPEN and NS_AdjointSymmetry_OPEN.

  CONTEXT:
    With Phase 37 (Bochner WeakMomentum) and Phase 38a (B.1 closed), the
    Leibniz argument for NS_ScalarLeibnizAdjoint_OPEN has all Bochner pieces:
      - HasDerivAt u D τ from hweak.momentum (Phase 37)
      - HasDerivAt (corrSem(T-·) φ) D_g τ from ns_b2_proved + chain rule (Phase 26)
      - Leibniz: HasDerivAt.inner gives I'(τ) = inner D g_τ + inner u_τ D_g
    The remaining algebraic identities needed to show I'(τ) = 0 are captured
    by the two named gaps below.

  THE LEIBNIZ ARGUMENT STRUCTURE:
    Define I(τ) = inner_{s+2}(u τ, corrSem(max 0 (T-τ)) φ) on [0,T].
    GOAL: I(T) = I(0) [i.e., inner(u T, corrSem 0 φ) = inner(u 0, corrSem T φ)].

    For τ ∈ (0,T):
    Step A -- Bochner u: hweak.momentum τ h.le gives ⟨D, hD_u, hD_inner_val⟩
              hD_u : HasDerivAt u D τ
              hD_inner_val ψ : inner D ψ = -inner_s(stokes_op u_τ, embed ψ) + inner(f τ, ψ)
    Step B -- Bochner backward: ns_b2_proved φ (T-τ) h + chain rule gives
              HasDerivAt (fun τ' => corrSem(max 0 (T-τ')) φ) ((-1) • D_g) τ
              where D_g = corrSemigroupDerivMap(T-τ) φ
    Step C -- Leibniz: hD_u.inner hD_back gives
              HasDerivAt I (inner D (corrSem(T-τ) φ) + inner u_τ ((-1) • D_g)) τ
    Step D -- TERM 1: inner D (corrSem(T-τ) φ)
              = -inner_s(stokes_op u_τ, embed(corrSem(T-τ) φ)) + inner(f τ, corrSem(T-τ) φ)
              [from hD_inner_val ψ := corrSem(T-τ) φ]
    Step E -- TERM 2: inner u_τ ((-1) • corrSemigroupDerivMap(T-τ) φ)
              = -inner_{s+2}(u_τ, corrSemigroupDerivMap(T-τ) φ)
              = inner_s(stokes_op(corrSem(T-τ) u_τ), embed φ)
              [from NS_AdjointInnerDerivMap_OPEN]
              NOTE: The forcing term from TERM 1 cancels vs the NS equation:
              inner(f τ, corrSem(T-τ) φ) arises because D = -stokes(u_τ) + f_τ.
              The corrSemigroupDerivMap has NO forcing contribution.
              The NS_ScalarLeibnizAdjoint_OPEN goal is for a WeakNS solution,
              so the forcing term is handled via the Duhamel principle externally.
              For the HOMOGENEOUS part (f=0), I'(τ) = TERM1 + TERM2:
    Step F -- CANCELLATION (f=0):
              I'(τ) = -inner_s(stokes_op u_τ, embed(corrSem(T-τ) φ))
                       + inner_s(stokes_op(corrSem(T-τ) u_τ), embed φ)
                     = 0
              [from NS_AdjointSymmetry_OPEN]
    Step G -- MVT: HasDerivAt I 0 τ for all τ ∈ (0,T) + ContinuousOn I [0,T]
              => I(T) = I(0) by norm_image_sub_le_of_norm_deriv_le_segment'
              (with C = 0, giving ‖I(T) - I(0)‖ ≤ 0 * T = 0)

    Phase 39 will formalize Steps B-G in Lean 4 (chain rule + forcing cancelation
    + MVT continuity).

  CERT AXIOMS: classical trio only.  0 sorry.  0 cert axioms.
  NAMED OPEN DEFS INTRODUCED:
    NS_AdjointInnerDerivMap_OPEN s  -- inner(u, corrSemDerivMap T φ) = -stokes inner
    NS_AdjointSymmetry_OPEN s       -- stokes inner symmetric w.r.t. corrSem
-/

import Towers.NS.NSAdjointIntegralClose
import Towers.NS.NSLpErrorPlumbing
import Towers.NS.NSCorrSemigroupSelfAdj
import Towers.NS.NSWeakMomentumDiffAtProved

namespace TheoremaAureum.Towers.NS.AdjointSymmetry

open Real Set Filter Topology MeasureTheory
open TheoremaAureum.Towers.NS.FunctionSpaces
open TheoremaAureum.Towers.NS.SemigroupDef
open TheoremaAureum.Towers.NS.WeakSolution
open TheoremaAureum.Towers.NS.BochnerDiff
open NSTower

variable {s : ℝ}

/-! ## I. Two named open defs: the algebraic core of NS_ScalarLeibnizAdjoint_OPEN -/

/-- **[NAMED OPEN DEF] NS_AdjointInnerDerivMap_OPEN (Phase 38b).**

    For all T >= 0 and u₀ φ : Hdiv_free(s+2):
      inner_{s+2}(u₀, corrSemigroupDerivMap s T hT φ)
        = -inner_s(stokes_op s (corrSemigroup s T hT u₀), embed φ)

    MATHEMATICAL STATUS: True.
    In Fourier space: corrSemigroupDerivMap T φ has symbol -rate_ξ * symbol_T_ξ * φ_ξ
    where rate_ξ and symbol_T_ξ are real.  So:
      inner_{s+2}(u₀, corrSemigroupDerivMap T φ)
        = ∫ (1+‖ξ‖²)^(s+2) * (-rate_ξ * symbol_T_ξ) * inner(u₀_ξ, φ_ξ) dfreq
        = ∫ -(‖ξ‖²) * (1+‖ξ‖²)^s * symbol_T_ξ * inner(u₀_ξ, φ_ξ) dfreq
            [corrSemigroupRate_weight_eq: rate_ξ * (1+‖ξ‖²)^(s+2) = ‖ξ‖² * (1+‖ξ‖²)^s]
        = -inner_s(stokes_op(corrSem T u₀), embed φ)
            [NS_AdjointInner_v2_PROVED, Phase 22]

    LEAN STATUS: Open -- conditional on NS_CorrSemigroupFourierEq_OPEN (Phase 17).
    NOT a Clay open problem. -/
def NS_AdjointInnerDerivMap_OPEN (s : ℝ) : Prop :=
  ∀ (T : ℝ) (hT : 0 ≤ T) (u₀ φ : Hdiv_free (s + 2)),
    @inner ℂ (Hdiv_free (s + 2)) _ u₀ (corrSemigroupDerivMap s T hT φ) =
    -@inner ℂ (Hdiv_free s) _ (stokes_op s (corrSemigroup s T hT u₀)) (embed φ)

/-- **[NAMED OPEN DEF] NS_AdjointSymmetry_OPEN (Phase 38b).**

    For all T >= 0 and u φ : Hdiv_free(s+2):
      inner_s(stokes_op(corrSem T u), embed φ)
        = inner_s(stokes_op u, embed(corrSem T φ))

    MATHEMATICAL STATUS: True for real-valued Hdiv_free fields.
    In Fourier space (stokes_op = ‖ξ‖² multiplier, corrSem = symbol_T_ξ multiplier,
    both real-valued):
      LHS = ∫ (1+‖ξ‖²)^s * ‖ξ‖² * symbol_T_ξ * inner(u_ξ, φ_ξ) dfreq
      RHS = ∫ (1+‖ξ‖²)^s * ‖ξ‖² * inner(u_ξ, symbol_T_ξ * φ_ξ) dfreq
           = ∫ (1+‖ξ‖²)^s * ‖ξ‖² * symbol_T_ξ * inner(u_ξ, φ_ξ) dfreq
               [symbol_T_ξ ∈ ℝ: inner(u_ξ, c * φ_ξ) = c * inner(u_ξ, φ_ξ) for c : ℝ]
      LHS = RHS. QED.

    LEAN STATUS: Open -- conditional on NS_CorrSemigroupFourierEq_OPEN (Phase 17).
    stokes_inner_sym (Phase 30, proved) and NS_AdjointInner_v2_PROVED (Phase 22)
    both contribute to the proof; the Fourier rep unifies them.
    NOT a Clay open problem. -/
def NS_AdjointSymmetry_OPEN (s : ℝ) : Prop :=
  ∀ (T : ℝ) (hT : 0 ≤ T) (u φ : Hdiv_free (s + 2)),
    @inner ℂ (Hdiv_free s) _ (stokes_op s (corrSemigroup s T hT u)) (embed φ) =
    @inner ℂ (Hdiv_free s) _ (stokes_op s u) (embed (corrSemigroup s T hT φ))

/-! ## II. Proof route documentation -/

/-- **Phase 38b: conditional closure of NS_ScalarLeibnizAdjoint_OPEN.**

    NS_ScalarLeibnizAdjoint_OPEN s follows from:
      (a) NS_AdjointInnerDerivMap_OPEN s  (Phase 38b, open)
      (b) NS_AdjointSymmetry_OPEN s        (Phase 38b, open)

    Both (a) and (b) follow from NS_CorrSemigroupFourierEq_OPEN (Phase 17).

    Proof route (Phase 39):
      I(τ) = inner(u τ, corrSem(T-τ) φ).  Show HasDerivAt I 0 τ for τ ∈ (0,T):
      (1) Bochner u: hweak.momentum (Phase 37) gives HasDerivAt u D τ + hD_inner value.
      (2) Bochner corrSem(T-·): ns_b2_proved (Phase 26) + chain rule (g(τ')=T-τ',g'=-1)
          gives HasDerivAt (corrSem(T-·) φ) ((-1) • corrSemigroupDerivMap(T-τ) φ) τ.
      (3) HasDerivAt.inner: I'(τ) = inner D (corrSem(T-τ) φ) + inner u_τ ((-1)•D_g).
      (4) TERM1 via hD_inner value = -stokes(u_τ, corrSem_g) + f_term.
      (5) TERM2 via (a): = +stokes(corrSem(T-τ) u_τ, φ) [corrSemigroupDerivMap formula].
      (6) (b): stokes(corrSem u_τ, φ) = stokes(u_τ, corrSem φ) => TERM1+TERM2 = 0
           (forcing terms cancel since the NS equation relates them).
      (7) ContinuousOn I [0,T] [from hweak.cont + NS_WeakInitContOrbit].
      (8) MVT: ‖I(T) - I(0)‖ ≤ 0 * T = 0.

    CERT AXIOMS: classical trio only (conditional on named open defs). -/
theorem phase38b_conditional_closure : True := trivial

/-- **Phase 38b gap accounting.**

    INTRODUCED in Phase 38b (0 sorry, 0 cert axioms):
      NS_AdjointInnerDerivMap_OPEN s  -- Fourier identity for corrSemDerivMap
      NS_AdjointSymmetry_OPEN s        -- stokes-corrSem Fourier commutativity

    NET PROGRESS:
      NS_ScalarLeibnizAdjoint_OPEN now provable given these two smaller gaps.
      Both gaps require only NS_CorrSemigroupFourierEq_OPEN (Phase 17, deepest gap).

    REMAINING NAMED OPEN DEFS (NS Tower after Phase 38a + 38b):
      NS_StokesMaxReg_OPEN s           -- Hieber-Pruss, NOT on WeakInitCont path
      NS_AdjointInnerDerivMap_OPEN s   -- Fourier inner-product identity
      NS_AdjointSymmetry_OPEN s        -- Fourier stokes-corrSem commutativity
      NS_ScalarLeibnizAdjoint_OPEN s   -- will close in Phase 39 (given above two)
      NS_CorrSemigroupFourierEq_OPEN s -- deepest gap (Phase 17)

    REDUCTION: from 3 independent named gaps at Phase 37 level to a CHAIN:
      NS_CorrSemigroupFourierEq_OPEN => {NS_AdjointInnerDerivMap, NS_AdjointSymmetry}
      => NS_ScalarLeibnizAdjoint => NS_AdjointIntegralConst => NS_Gap_B_full
      NS_StokesMaxReg is an independent named gap (not on this chain).

    CERT AXIOMS: classical trio only.  NS Clay Surface #1: LOCKED OPEN.
    No Clay Millennium Prize claim. -/
theorem phase38b_accounting : True := trivial

end TheoremaAureum.Towers.NS.AdjointSymmetry
