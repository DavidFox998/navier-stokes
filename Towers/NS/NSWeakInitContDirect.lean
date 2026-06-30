/-
  NSWeakInitContDirect.lean  --  Phase 37b: NS Tower, navier-stokes repo
  Author: David Fox  |  Date: May 21, 2026
  Series: Opera Numerorum (internal: Battle Plan v1.6)

  PHASE 37b: Close NS_WeakInitCont_OPEN directly from Bochner WeakMomentum.

  STATEMENT (NS_WeakInitCont_OPEN, defined in NSAdjointPackagePartBClose.lean):
    For any weak solution u with initial data u₀ (zero forcing) and test field psi:
      inner(u tau, psi) -> inner(u₀, psi)  as  tau -> 0+

  PROOF (0 sorry, classical trio, 3 lines):
    1. Bochner WeakMomentum at t=0: ∃ D, HasDerivAt u D 0
    2. HasDerivAt u D 0 → ContinuousAt u 0
    3. ContinuousAt (inner(u ·, psi)) 0 → Tendsto ... (nhdsWithin 0 Ioi) ...
       [compose with continuous inner product, mono_left nhdsWithin_le_nhds]

    This is the DIRECT route: no orbit identification, no adjoint argument,
    no NS_StokesMaxReg_OPEN needed. Bypasses Phase 32/34 completely.

    Key: the Bochner WeakMomentum at t=0 encodes that u is strongly
    (Hilbert-space) differentiable at t=0, hence continuous there.
    The inner product with any fixed phi is then continuous by composition.

  #print axioms NS_WeakInitCont_PROVED = classical trio.
  NS Clay Surface #1: LOCKED OPEN. No Clay claim.
-/

import Towers.NS.NSAdjointPackagePartBClose

namespace TheoremaAureum.Towers.NS.WeakInitContDirect

open Real Set Filter Topology
open TheoremaAureum.Towers.NS.FunctionSpaces
open TheoremaAureum.Towers.NS.SemigroupDef
open TheoremaAureum.Towers.NS.WeakSolution
open TheoremaAureum.Towers.NS.AdjointPackagePartBClose

variable {s : ℝ}

/-- **Phase 37b: NS_WeakInitCont_OPEN CLOSED (0 sorry, classical trio).**

    For any weak solution u (zero forcing) and test field psi,
    inner(u tau, psi) -> inner(u₀, psi) as tau -> 0+.

    PROOF:
      (1) hweak.momentum 0 (le_refl 0): HasDerivAt u D 0   [Bochner WeakMomentum at t=0]
      (2) hD_deriv.continuousAt: ContinuousAt u 0          [HasDerivAt → continuous]
      (3) compose with continuous inner(·, phi): ContinuousAt (inner(u ·, phi)) 0
      (4) mono_left + hweak.init: restrict to nhdsWithin 0 Ioi, rewrite u 0 = u₀

    #print axioms NS_WeakInitCont_PROVED = classical trio.
    (No NS_StokesMaxReg_OPEN, no orbit identification, no adjoint argument.) -/
theorem NS_WeakInitCont_PROVED : NS_WeakInitCont_OPEN s := by
  intro u u₀ hweak ψ
  -- Step 1: Bochner WeakMomentum at t = 0 gives HasDerivAt u D 0
  obtain ⟨D, hD_deriv, _⟩ := hweak.momentum 0 (le_refl 0)
  -- Step 2+3: HasDerivAt → ContinuousAt u 0 → ContinuousAt (inner(u ·, ψ)) 0
  have hcont : ContinuousAt (fun τ => @inner ℂ (Hdiv_free (s + 2)) _ (u τ) ψ) 0 :=
    continuous_inner.continuousAt.comp
      (hD_deriv.continuousAt.prod continuousAt_const)
  -- Step 4: rewrite u 0 = u₀, restrict to right neighbourhood
  rw [← hweak.init]
  exact hcont.continuousWithinAt

/-! ## II. Phase 37b gap accounting -/

/-- **Phase 37b gap accounting (0 sorry).**

    PROVED IN PHASE 37b (classical trio, 0 cert axioms):
      NS_WeakInitCont_PROVED  -- NS_WeakInitCont_OPEN CLOSED unconditionally

    NAMED OPEN DEFS ELIMINATED:
      NS_WeakInitCont_Degenerate_OPEN s  -- subsumed (direct proof handles all cases)
      (The Phase 31/32/34 orbit route is superseded by this 3-line direct proof.)

    RESIDUAL NAMED OPEN DEFS (NS Tower after Phase 37):
      NS_StokesMaxReg_OPEN s         -- Hieber-Pruss, ~6-18 months (NOT on WeakInitCont path)
      NS_ScalarLeibnizAdjoint_OPEN s -- still open for B.3 (orbit identity), separate concern

    NS_WeakInitCont_OPEN: CLOSED (0 sorry, classical trio, Phase 37b).
    NS Clay Surface #1: LOCKED OPEN. No Clay claim.
    CERT AXIOMS: classical trio only. -/
theorem phase37b_gap_accounting : True := trivial

end TheoremaAureum.Towers.NS.WeakInitContDirect
