/-
  NSPhase41ThreeGaps.lean  --  Phase 41: NS Tower, navier-stokes repo
  Author: David Fox  |  Date: May 21, 2026
  Series: Opera Numerorum (internal: Battle Plan v1.6)

  PHASE 41: Close NS_BackwardDerivMap_OPEN and NS_FuncIContOn_OPEN.
  NS_ForcingOrbitZero_OPEN remains as a named gap (requires Duhamel principle).

  CONTEXT (after Phase 40):
    Phase 40 closed: NS_AdjointSymmetry_OPEN, NS_AdjointInnerDerivMap_OPEN.
    Phase 39 (NSScalarLeibnizAdjoint.lean) takes those as hypotheses and provides
    NS_ScalarLeibnizAdjoint_PROVED conditional on 5 named defs.
    Phases 40+41 close 4 of the 5:
      NS_AdjointInnerDerivMap_OPEN  (Phase 40) -- CLOSED
      NS_AdjointSymmetry_OPEN       (Phase 40) -- CLOSED
      NS_BackwardDerivMap_OPEN      (Phase 41) -- CLOSED HERE
      NS_FuncIContOn_OPEN           (Phase 41) -- CLOSED HERE
    Remaining: NS_ForcingOrbitZero_OPEN (forcing orthogonality, Duhamel principle).

  PROVED (0 sorry, classical trio):
    NS_BackwardDerivMap_PROVED
      HasDerivAt (corrSem(T-.) phi) ((-1) * corrSemDerivMap(T-tau) phi) tau
      via HasDerivAt.comp_hasDerivAt (chain rule).

    NS_FuncIContOn_PROVED
      ContinuousOn (fun tau => inner(u tau, corrSem(max 0 (T-tau)) phi)) [[0,T]]
      via ContinuousOn.inner (u continuous from WeakMomentum;
           corrSem(max 0 (T-.)) phi continuous from NS_CorrSemigroupGenerator_PROVED).

    NS_ScalarLeibnizAdjoint_Phase41
      NS_ScalarLeibnizAdjoint_OPEN given only NS_ForcingOrbitZero_OPEN.

  REMAINING NAMED OPEN DEFS after Phase 41 (3):
    NS_ForcingOrbitZero_OPEN s       -- forcing orthogonality (Duhamel principle needed)
    NS_CorrSemigroupFourierEq_OPEN s -- Phase 17 deepest gap (WeakInitCont chain)
    NS_StokesMaxReg_OPEN s           -- Hieber-Pruss 2018 (independent chain)

  CERT AXIOMS: classical trio only.  NS Clay Surface #1: LOCKED OPEN.  No Clay claim.
-/

import Towers.NS.NSPhase40AdjClose
import Towers.NS.NSScalarLeibnizAdjoint
import Mathlib.Analysis.Calculus.Deriv.Comp

namespace TheoremaAureum.Towers.NS.Phase41ThreeGaps

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
open NSTower

variable {s : ℝ}

/-! ## I. NS_BackwardDerivMap_PROVED -/

/-- **Phase 41: NS_BackwardDerivMap_OPEN CLOSED (0 sorry, classical trio).**

    HasDerivAt (fun t => corrSemigroup s (max 0 (T-t)) (le_max_left 0 (T-t)) phi)
               ((-1:R) • corrSemigroupDerivMap s (T-tau) hTtau_pos.le phi) tau.

    PROOF (chain rule):
    (1) NS_CorrSemigroupGenerator_PROVED (T-tau) hTtau_pos.le phi :
        HasDerivAt (fun t => corrSem(max 0 t) phi) (corrSemDerivMap(T-tau) phi) (T-tau)
    (2) hasDerivAt_id + const_sub T :
        HasDerivAt (fun t => T - t) (-1:R) tau
    (3) HasDerivAt.comp_hasDerivAt (chain rule for Bochner-valued + scalar):
        HasDerivAt (fun t => corrSem(max 0 (T-t)) phi) ((-1) • corrSemDerivMap(T-tau) phi) tau

    #print axioms NS_BackwardDerivMap_PROVED = classical trio. -/
theorem NS_BackwardDerivMap_PROVED : NS_BackwardDerivMap_OPEN s := by
  intro T φ τ hTτ_pos
  -- (1) Bochner HasDerivAt of corrSem(max 0 .) phi at T-tau
  have hgen : HasDerivAt
      (fun t => corrSemigroup s (max 0 t) (le_max_left 0 t) φ)
      (corrSemigroupDerivMap s (T - τ) hTτ_pos.le φ)
      (T - τ) :=
    NS_CorrSemigroupGenerator_PROVED (T - τ) hTτ_pos.le φ
  -- (2) HasDerivAt of (T - .) at tau is -1
  have hlin : HasDerivAt (fun t : ℝ => T - t) (-1 : ℝ) τ := by
    have h := (hasDerivAt_id τ).const_sub T
    simpa using h
  -- (3) Chain rule
  have hcomp := hgen.comp_hasDerivAt τ hlin
  -- hcomp : HasDerivAt (corrSem(max 0 .) ∘ (T-.)) ((-1) • corrSemDerivMap(T-τ) φ) τ
  convert hcomp using 2 <;> simp [Function.comp]

/-! ## II. NS_FuncIContOn_PROVED -/

/-- **Phase 41: NS_FuncIContOn_OPEN CLOSED (0 sorry, classical trio).**

    ContinuousOn (fun tau => inner(u tau, corrSem(max 0 (T-tau)) phi)) [[0, T]].

    PROOF:
    (A) u is ContinuousOn [[0,T]]:
        WeakMomentum gives HasDerivAt u D t for all t >= 0,
        so ContinuousAt u t for all t >= 0, hence ContinuousOn u (Ici 0) => [[0,T]].
    (B) corrSem(max 0 (T-.)) phi is ContinuousOn [[0,T]]:
        NS_CorrSemigroupGenerator_PROVED t ht phi gives HasDerivAt, hence ContinuousAt,
        so corrSem(max 0 .) phi is ContinuousOn (Ici 0).
        Composed with the continuous map (T-.) (which maps [[0,T]] into [0,T] ⊆ Ici 0),
        we get ContinuousOn on [[0,T]].
    (C) ContinuousOn.inner applies to (A) and (B).

    #print axioms NS_FuncIContOn_PROVED = classical trio. -/
theorem NS_FuncIContOn_PROVED : NS_FuncIContOn_OPEN s := by
  intro u u₀ f hweak T hT φ
  apply ContinuousOn.inner
  -- (A) ContinuousOn u [[0, T]]
  · apply ContinuousOn.mono (s := Set.Ici 0)
    · intro t ht
      apply ContinuousAt.continuousWithinAt
      obtain ⟨D, hD, _⟩ := hweak.momentum t (Set.mem_Ici.mp ht)
      exact hD.continuousAt
    · intro t ht
      simp only [Set.uIcc_of_le hT.le, Set.mem_Icc] at ht
      exact Set.mem_Ici.mpr ht.1
  -- (B) ContinuousOn (corrSem(max 0 (T-.)) phi) [[0, T]]
  · -- corrSem(max 0 .) phi is ContinuousOn (Ici 0)
    have hcS : ContinuousOn
        (fun t => corrSemigroup s (max 0 t) (le_max_left 0 t) φ) (Set.Ici 0) := by
      intro t ht
      apply ContinuousAt.continuousWithinAt
      exact (NS_CorrSemigroupGenerator_PROVED t (Set.mem_Ici.mp ht) φ).continuousAt
    -- (T - .) maps [[0,T]] into Ici 0
    have hrange : ∀ τ ∈ Set.uIcc 0 T, T - τ ∈ Set.Ici (0 : ℝ) := by
      intro τ hτ
      simp only [Set.uIcc_of_le hT.le, Set.mem_Icc] at hτ
      exact Set.mem_Ici.mpr (by linarith [hτ.2])
    -- Compose (T-.) with hcS
    have hcomp := hcS.comp (continuous_const.sub continuous_id).continuousOn hrange
    apply hcomp.congr
    intro τ _
    simp [Function.comp]

/-! ## III. Main combinator -/

/-- **Phase 41: NS_ScalarLeibnizAdjoint given only NS_ForcingOrbitZero_OPEN.**

    Phase 40 proved: NS_AdjointInnerDerivMap_PROVED, NS_AdjointSymmetry_PROVED.
    Phase 41 proved: NS_BackwardDerivMap_PROVED, NS_FuncIContOn_PROVED.
    The only remaining hypothesis is NS_ForcingOrbitZero_OPEN.

    #print axioms NS_ScalarLeibnizAdjoint_Phase41 = classical trio (given ForcingOrbitZero). -/
theorem NS_ScalarLeibnizAdjoint_Phase41
    (hfz : NS_ForcingOrbitZero_OPEN s) :
    NS_ScalarLeibnizAdjoint_OPEN s :=
  NS_ScalarLeibnizAdjoint_PROVED
    NS_AdjointInnerDerivMap_PROVED
    NS_AdjointSymmetry_PROVED
    hfz
    NS_BackwardDerivMap_PROVED
    NS_FuncIContOn_PROVED

/-! ## IV. Phase 41 gap accounting -/

/-- **Phase 41 gap accounting (0 sorry, 0 cert axioms, classical trio).**

    PROVED IN PHASE 41:
      NS_BackwardDerivMap_PROVED   -- chain rule for corrSem(T-.) phi (HasDerivAt.comp_hasDerivAt)
      NS_FuncIContOn_PROVED        -- ContinuousOn of inner product orbit function
      NS_ScalarLeibnizAdjoint_Phase41 -- combinator reducing to ForcingOrbitZero only

    NAMED OPEN DEFS ELIMINATED:
      NS_BackwardDerivMap_OPEN s  -- CLOSED Phase 41
      NS_FuncIContOn_OPEN s       -- CLOSED Phase 41

    REMAINING NAMED OPEN DEFS (NS Tower after Phase 41):
      NS_ForcingOrbitZero_OPEN s       -- forcing orthogonality; requires Duhamel principle
      NS_CorrSemigroupFourierEq_OPEN s -- Phase 17 deepest gap on WeakInitCont chain
      NS_StokesMaxReg_OPEN s           -- Hieber-Pruss 2018 (independent chain)

    DEPENDENCY CHAIN after Phase 41:
      NS_ForcingOrbitZero_OPEN + NS_CorrSemigroupFourierEq_OPEN
        => NS_ScalarLeibnizAdjoint_OPEN  (Phase 41 combinator)
        => NS_AdjointIntegralConst_OPEN  (Phase 36 combinator ns_adjointIntegral_from_sub)
        => NS_WeakInitCont_OPEN          (Phase 34/39/41 chain)
        => Gap B => NS_ClayStatement

    CERT AXIOMS: classical trio only.
    NS Clay Surface #1: LOCKED OPEN.  No Clay Millennium Prize claim. -/
theorem phase41_gap_accounting : True := trivial

end TheoremaAureum.Towers.NS.Phase41ThreeGaps
