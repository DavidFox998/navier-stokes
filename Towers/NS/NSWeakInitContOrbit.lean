/-
  NSWeakInitContOrbit.lean  --  Phase 34: NS Tower, navier-stokes repo
  Author: David Fox  |  Date: May 21, 2026
  Series: Opera Numerorum (internal: Battle Plan v1.6)

  PHASE 34: Close NS_WeakInitCont_OPEN conditional on B.1 + B.3.

  NOW POSSIBLE BECAUSE:
    Phase 33 proved NS_CorrSemigroupLipAtZero_OPEN unconditionally (0 sorry).
    Phase 32 proved ns_weakInitCont_from_orbit conditional on B.1 + B.3 + LipAtZero.
    LipAtZero is no longer a gap.

  MAIN THEOREM:
    ns_weakInitCont_orbit_proved
      (hmom : NS_WeakMomentumDiffAt_OPEN s)   -- B.1: ~1-3 months
      (h3   : NS_AdjointIntegralConst_OPEN s)  -- B.3: ~2-4 months
    : NS_WeakInitCont_OPEN s

  PROOF: one line -- ns_weakInitCont_from_orbit h3 hmom ns_corrSemigroup_lip_at_zero_proved.

  DOWNSTREAM:
    ns_weakInitCont_degenerate_orbit_proved   -- NS_WeakInitCont_Degenerate_OPEN CLOSED
    ns_adjointpackage_partB_orbit_proved      -- NS_AdjointPackage_PartB_OPEN CLOSED

  NAMED OPEN DEF STATUS (NS Tower after Phase 34):
    NS_StokesMaxReg_OPEN s          -- Hieber-Pruss, ~6-18 months (UNCHANGED, not on this path)
    NS_WeakMomentumDiffAt_OPEN s    -- B.1: WeakMomentum HasDerivAt, ~1-3 months
    NS_AdjointIntegralConst_OPEN s  -- B.3: orbit identification via adjoint, ~2-4 months

  ELIMINATED (conditional on B.1 + B.3):
    NS_CorrSemigroupLipAtZero_OPEN  -- Phase 33 (unconditional)
    NS_WeakInitCont_OPEN            -- THIS FILE (conditional B.1 + B.3)
    NS_WeakInitCont_Degenerate_OPEN -- THIS FILE (follows immediately)
    NS_AdjointPackage_PartB_OPEN    -- THIS FILE (follows from WeakInitCont)

  NO NS_StokesMaxReg_OPEN DEPENDENCY on any of the above.

  CERT AXIOMS: classical trio only. NS Clay Surface #1: LOCKED OPEN. No Clay claim.
  #print axioms ns_weakInitCont_orbit_proved = classical trio + B.1 + B.3.
-/

import Towers.NS.NSCorrSemigroupLipAtZero

namespace TheoremaAureum.Towers.NS.WeakInitContOrbit

open TheoremaAureum.Towers.NS.FunctionSpaces
open TheoremaAureum.Towers.NS.SemigroupDef
open TheoremaAureum.Towers.NS.WeakSolution
open TheoremaAureum.Towers.NS.BochnerDiff
open TheoremaAureum.Towers.NS.CorrSemigroupContinuity
open TheoremaAureum.Towers.NS.CorrSemigroupLipAtZero
open NSTower

variable {s : ℝ}

/-! ## I. NS_WeakInitCont_OPEN closed (conditional on B.1 + B.3) -/

/-- **Phase 34: NS_WeakInitCont_OPEN CLOSED (0 sorry, given B.1 + B.3).**

    inner(u tau, psi) --> inner(u0, psi) as tau -> 0+
    for every Leray-Hopf weak solution u of NSE(u0, f=0).

    PROOF (one line):
      Phase 32 (ns_weakInitCont_from_orbit) proved this conditional on B.1 + B.3 + LipAtZero.
      Phase 33 (ns_corrSemigroup_lip_at_zero_proved) closed LipAtZero unconditionally.
      Plug in Phase 33 result as the hlip argument.

    AXIOM FOOTPRINT: classical trio + hmom (B.1) + h3 (B.3).
    No NS_StokesMaxReg_OPEN.  No NS_CorrSemigroupLipAtZero_OPEN.
    #print axioms ns_weakInitCont_orbit_proved = classical trio (given hmom, h3). -/
theorem ns_weakInitCont_orbit_proved
    (hmom : NS_WeakMomentumDiffAt_OPEN s)
    (h3   : NS_AdjointIntegralConst_OPEN s) :
    NS_WeakInitCont_OPEN s :=
  ns_weakInitCont_from_orbit h3 hmom ns_corrSemigroup_lip_at_zero_proved

/-! ## II. Degenerate case: immediate corollary -/

/-- **Phase 34: NS_WeakInitCont_Degenerate_OPEN CLOSED (0 sorry, given B.1 + B.3).**

    The full orbit route subsumes the degenerate case directly.
    The extra hypothesis _hdeg (H0 = 0) is not needed.
    #print axioms ns_weakInitCont_degenerate_orbit_proved = classical trio (given hmom, h3). -/
theorem ns_weakInitCont_degenerate_orbit_proved
    (hmom : NS_WeakMomentumDiffAt_OPEN s)
    (h3   : NS_AdjointIntegralConst_OPEN s) :
    NS_WeakInitCont_Degenerate_OPEN s :=
  ns_weakInitCont_degenerate_from_orbit h3 hmom ns_corrSemigroup_lip_at_zero_proved

/-! ## III. NS_AdjointPackage_PartB_OPEN: downstream closure -/

/-- **Phase 34: NS_AdjointPackage_PartB_OPEN CLOSED (0 sorry, given B.1 + B.3).**

    Phase 30 proved NS_AdjointPackage_PartB_OPEN conditional on NS_WeakInitCont_OPEN.
    Phase 32 connected WeakInitCont to the orbit route.
    Phase 33 eliminated LipAtZero.
    This theorem closes the full chain: PartB_OPEN holds given only B.1 + B.3.

    #print axioms ns_adjointpackage_partB_orbit_proved = classical trio (given hmom, h3). -/
theorem ns_adjointpackage_partB_orbit_proved
    (hmom : NS_WeakMomentumDiffAt_OPEN s)
    (h3   : NS_AdjointIntegralConst_OPEN s) :
    NS_AdjointPackage_PartB_OPEN s :=
  NS_AdjointPackage_PartB_from_orbit h3 hmom ns_corrSemigroup_lip_at_zero_proved

/-! ## IV. Phase 34 gap accounting -/

/-- **Phase 34 gap accounting (0 sorry throughout).**

    PROVED IN PHASE 34 (classical trio, 0 cert axioms, conditional on B.1 + B.3):
      ns_weakInitCont_orbit_proved         -- NS_WeakInitCont_OPEN CLOSED
      ns_weakInitCont_degenerate_orbit_proved -- NS_WeakInitCont_Degenerate_OPEN CLOSED
      ns_adjointpackage_partB_orbit_proved -- NS_AdjointPackage_PartB_OPEN CLOSED

    REMAINING NAMED OPEN DEFS (NS Tower after Phase 34):
      NS_StokesMaxReg_OPEN s          -- Hieber-Pruss: ~6-18 months (NOT on WeakInitCont path)
      NS_WeakMomentumDiffAt_OPEN s    -- B.1: HasDerivAt of inner(u tau, phi) at t > 0
      NS_AdjointIntegralConst_OPEN s  -- B.3: u tau = corrSemigroup orbit identification

    PROOF CHAIN SUMMARY (phases 30 -> 34):
      Phase 30: NS_AdjointPackage_PartB_OPEN <- NS_WeakInitCont_OPEN
      Phase 31: NS_WeakInitCont_OPEN (non-degenerate) <- WeakMomentum differentiability
      Phase 32: NS_WeakInitCont_OPEN <- B.1 + B.3 + LipAtZero (orbit route, no MaxReg)
      Phase 33: LipAtZero CLOSED unconditionally (0 sorry, classical trio)
      Phase 34: NS_WeakInitCont_OPEN CLOSED given B.1 + B.3 (this file)

    CERT AXIOMS: classical trio only.  NS Clay Surface #1: LOCKED OPEN.  No Clay claim. -/
theorem phase34_gap_accounting : True := trivial

end TheoremaAureum.Towers.NS.WeakInitContOrbit
