/-
  NSWeakMomentumDiffAtProved.lean  --  Phase 38a: NS Tower, navier-stokes repo
  Author: David Fox  |  Date: May 21, 2026
  Series: Opera Numerorum (internal: Battle Plan v1.6)

  PHASE 38a: Close NS_WeakMomentumDiffAt_OPEN (B.1) and NS_WeakMomentumDiff_OPEN
  unconditionally from the Phase 37 Bochner WeakMomentum upgrade.

  KEY INSIGHT (Phase 37 upgrade):
    WeakNS.momentum now returns Bochner HasDerivAt:
      hweak.momentum t ht.le = ⟨D, hD_deriv, hD_inner⟩
      hD_deriv : HasDerivAt u D t          (strong / Bochner in Hdiv_free(s+2))
      hD_inner : ∀ φ, inner D φ = VALUE    (stokes + forcing formula)

  PROOFS:
    NS_WeakMomentumDiffAt_PROVED (B.1, 0 sorry, classical trio):
      hD_deriv.inner (hasDerivAt_const t φ)
        -- HasDerivAt (fun τ => inner(u τ, φ)) (inner D φ + inner(u t) 0) t
      simp only [inner_zero_right, add_zero]
        -- HasDerivAt (fun τ => inner(u τ, φ)) (inner D φ) t
      h.congr_deriv (hD_inner φ)
        -- HasDerivAt (fun τ => inner(u τ, φ)) VALUE t

    NS_WeakMomentumDiff_PROVED (0 sorry, classical trio):
      NS_WeakMomentumDiffAt_PROVED + .differentiableAt

  WHY THIS CLOSES B.1:
    Phase 35 (NSWeakMomentumDiffAtClose.lean) proved B.1 CONDITIONAL on
    NS_WeakMomentumDiff_OPEN (scalar DifferentiableAt).
    Phase 38a proves BOTH directly and UNCONDITIONALLY from Bochner
    WeakMomentum (Phase 37), bypassing the conditional entirely.

  CERT AXIOMS: classical trio only.  0 sorry.  0 cert axioms.
  NAMED OPEN DEFS CLOSED: NS_WeakMomentumDiffAt_OPEN s, NS_WeakMomentumDiff_OPEN s.
-/

import Towers.NS.NSWeakMomentumDiffAtClose

namespace TheoremaAureum.Towers.NS.WeakMomentumDiffAtProved

open Real Set Filter Topology MeasureTheory
open TheoremaAureum.Towers.NS.FunctionSpaces
open TheoremaAureum.Towers.NS.SemigroupDef
open TheoremaAureum.Towers.NS.WeakSolution
open TheoremaAureum.Towers.NS.BochnerDiff
open TheoremaAureum.Towers.NS.WeakMomentumDiffAtClose
open NSTower

variable {s : ℝ}

/-- **Phase 38a: NS_WeakMomentumDiffAt_OPEN CLOSED (B.1, 0 sorry, classical trio).**

    Phase 37 Bochner WeakMomentum: hweak.momentum t ht.le gives
    ⟨D, hD_deriv, hD_inner⟩ where hD_deriv : HasDerivAt u D t (Bochner).

    HasDerivAt.inner (standard Mathlib Leibniz for inner product) gives:
      hD_deriv.inner (hasDerivAt_const t φ)
        : HasDerivAt (fun τ => inner(u τ, φ)) (inner D φ + inner(u t) 0) t
    simp [inner_zero_right, add_zero] simplifies the value to inner D φ.
    h.congr_deriv (hD_inner φ) replaces inner D φ with the stokes + forcing term.

    No conditional: fully unconditional from Phase 37 Bochner upgrade.
    #print axioms NS_WeakMomentumDiffAt_PROVED = classical trio. -/
theorem NS_WeakMomentumDiffAt_PROVED : NS_WeakMomentumDiffAt_OPEN s := by
  intro u u₀ f hweak φ t ht
  obtain ⟨D, hD_deriv, hD_inner⟩ := hweak.momentum t ht.le
  have h := hD_deriv.inner (hasDerivAt_const t φ)
  simp only [inner_zero_right, add_zero] at h
  exact h.congr_deriv (hD_inner φ)

/-- **Phase 38a: NS_WeakMomentumDiff_OPEN CLOSED (0 sorry, classical trio).**

    DifferentiableAt follows from HasDerivAt via .differentiableAt.
    HasDerivAt is provided by NS_WeakMomentumDiffAt_PROVED.
    #print axioms NS_WeakMomentumDiff_PROVED = classical trio. -/
theorem NS_WeakMomentumDiff_PROVED : NS_WeakMomentumDiff_OPEN s := by
  intro u u₀ f hweak φ t ht
  exact (NS_WeakMomentumDiffAt_PROVED u u₀ f hweak φ t ht).differentiableAt

/-- **Phase 38a gap accounting.**

    PROVED (0 sorry, 0 cert axioms, classical trio):
      NS_WeakMomentumDiffAt_PROVED  -- B.1 HasDerivAt form: CLOSED unconditionally
      NS_WeakMomentumDiff_PROVED    -- scalar DifferentiableAt: CLOSED unconditionally

    HOW: Phase 37 upgraded WeakNS.momentum to Bochner HasDerivAt.
    HasDerivAt.inner + congr_deriv close NS_WeakMomentumDiffAt_OPEN in 3 lines.
    .differentiableAt closes NS_WeakMomentumDiff_OPEN in 1 line.

    REMAINING NAMED OPEN DEFS (after Phase 38a):
      NS_StokesMaxReg_OPEN s           -- Hieber-Pruss, NOT on WeakInitCont path
      NS_ScalarLeibnizAdjoint_OPEN s   -- Leibniz + MVT (Phase 36)
        [decomposes into NS_AdjointInnerDerivMap_OPEN + NS_AdjointSymmetry_OPEN,
         see NSAdjointSymmetry.lean Phase 38b]
      NS_CorrSemigroupFourierEq_OPEN s -- Fourier rep (deepest, Phase 17)

    B.3 (NS_AdjointIntegralConst_OPEN) closed conditional on
    NS_ScalarLeibnizAdjoint_OPEN + NS_CorrSemigroupSelfAdj_PROVED (Phase 37a).

    CERT AXIOMS: classical trio only.  NS Clay Surface #1: LOCKED OPEN.
    No Clay Millennium Prize claim. -/
theorem phase38a_accounting : True := trivial

end TheoremaAureum.Towers.NS.WeakMomentumDiffAtProved
