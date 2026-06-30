/-
  NSCorrSemigroupSelfAdj.lean  --  Phase 37a: NS Tower, navier-stokes repo
  Author: David Fox  |  Date: May 21, 2026
  Series: Opera Numerorum (internal: Battle Plan v1.6)

  PHASE 37a: Close NS_CorrSemigroupSelfAdj_OPEN.

  STATEMENT (NS_CorrSemigroupSelfAdj_OPEN, defined in NSAdjointIntegralClose.lean):
    inner_{s+2}(u₀, corrSemigroup s t ht phi) = inner_{s+2}(corrSemigroup s t ht u₀, phi)

  PROOF (0 sorry, classical trio):
    1. inner_Hdiv_eq + L2.inner_def: reduce both sides to integrals
       ∫ xi, inner(u₀_xi, corrSemSym t xi * phi_xi) dmu =
       ∫ xi, inner(corrSemSym t xi * u₀_xi, phi_xi) dmu
    2. corrSemigroup_coeFn_ae_local: (corrSem t v)_xi =ae corrSemSym t xi * v_xi
    3. integral_congr_ae + filter_upwards: reduce to pointwise equality at xi
    4. LHS: inner_smul_right: inner(a, c*b) = c * inner(a, b)
       RHS: inner_smul_left: inner(c*a, b) = conj(c) * inner(a, b)
    5. congr 1 + corrSemigroupSymbol real: conj(ofReal x) = ofReal x
       (Phase 20 proved corrSemigroupSymbol t xi = ofReal(exp(-rate*t)) is real.)

  #print axioms NS_CorrSemigroupSelfAdj_PROVED = classical trio.
  NS Clay Surface #1: LOCKED OPEN. No Clay claim.
-/

import Towers.NS.NSFourierInner
import Towers.NS.NSAdjointIntegralClose

namespace TheoremaAureum.Towers.NS.CorrSemigroupSelfAdj

open Real Set Filter Topology MeasureTheory
open TheoremaAureum.Towers.NS.FunctionSpaces
open TheoremaAureum.Towers.NS.SemigroupDef
open TheoremaAureum.Towers.NS.WeakSolution
open TheoremaAureum.Towers.NS.FourierInner
open TheoremaAureum.Towers.NS.AdjointIntegralClose

variable {s : ℝ}

/-! ## I. Private coeFn helper (adapts corrSemigroup_coeFn_ae' from NSFourierInner) -/

/-- coeFn of corrSemigroup s t ht v (as Lp Val 2 mu(s+2)) ae-equals
    fun xi => corrSemigroupSymbol t xi * v xi.
    Proof: unfold corrSemigroup -> corrSemigroupLin -> Memℒp.toLp; apply coeFn_toLp.
    Adapted from private corrSemigroup_coeFn_ae' in NSFourierInner.lean. -/
private lemma corrSemigroup_coeFn_ae_local (t : ℝ) (ht : 0 ≤ t) (v : Hdiv_free (s + 2)) :
    ((corrSemigroup s t ht v : Hdiv_free (s + 2)) : Lp Val 2 (mu (s + 2)))
    =ᵐ[mu (s + 2)]
    fun ξ => corrSemigroupSymbol t ξ • (v : Lp Val 2 (mu (s + 2))) ξ := by
  have h1 := (corrSemigroup_memLp s t ht (v : Lp Val 2 (mu (s + 2)))).coeFn_toLp
  filter_upwards [h1] with ξ hξ
  simp only [corrSemigroup, ContinuousLinearMap.codRestrict_apply,
    ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
    corrSemigroupLin, LinearMap.coe_mk, AddHom.coe_mk]
  exact hξ

/-! ## II. Main theorem: corrSemigroup is self-adjoint -/

/-- **Phase 37a: NS_CorrSemigroupSelfAdj_OPEN CLOSED (0 sorry, classical trio).**

    inner_{s+2}(u₀, corrSem t ht phi) = inner_{s+2}(corrSem t ht u₀, phi).
    Equivalently: corrSemigroup s t ht is a self-adjoint operator on Hdiv_free(s+2).

    PROOF STRUCTURE (adapted from Phase 30 stokes_inner_sym):
      inner_Hdiv_eq + L2.inner_def → integrals
      corrSemigroup_coeFn_ae_local → pointwise substitution
      inner_smul_right + inner_smul_left → factor out symbol
      corrSemigroupSymbol real + Complex.conj_ofReal → symbols equal

    #print axioms NS_CorrSemigroupSelfAdj_PROVED = classical trio. -/
theorem NS_CorrSemigroupSelfAdj_PROVED : NS_CorrSemigroupSelfAdj_OPEN s := by
  intro t ht u₀ φ
  -- Reduce inner products on Hdiv_free to L2 integrals
  simp only [inner_Hdiv_eq, L2.inner_def]
  apply integral_congr_ae
  -- coeFn of corrSem t u₀ and corrSem t phi pointwise a.e.
  have hAu0 := corrSemigroup_coeFn_ae_local t ht u₀
  have hAphi := corrSemigroup_coeFn_ae_local t ht φ
  -- For a.e. xi: inner(u₀_xi, corrSemSym*phi_xi) = inner(corrSemSym*u₀_xi, phi_xi)
  filter_upwards [hAu0, hAphi] with ξ hau haφ
  -- Substitute corrSem coeFn on each side
  rw [haφ, hau]
  -- inner(a, c • b) = c * inner(a, b)   [inner_smul_right]
  -- inner(c • a, b) = conj(c) * inner(a, b)  [inner_smul_left]
  rw [inner_smul_right, inner_smul_left]
  -- Prove the coefficients equal: c = conj(c) for real c
  -- corrSemigroupSymbol t xi = ofReal(exp(-rate*t)) is real
  congr 1
  simp only [corrSemigroupSymbol, map_ofReal, Complex.conj_ofReal]

/-! ## III. Phase 37a gap accounting -/

/-- **Phase 37a gap accounting (0 sorry).**

    PROVED IN PHASE 37a (classical trio, 0 cert axioms):
      NS_CorrSemigroupSelfAdj_PROVED  -- corrSemigroup is self-adjoint

    NAMED OPEN DEF ELIMINATED:
      NS_CorrSemigroupSelfAdj_OPEN s  -- CLOSED Phase 37a

    REMAINING NAMED OPEN DEFS (NS Tower after Phase 37a):
      NS_StokesMaxReg_OPEN s         -- Hieber-Pruss, ~6-18 months (not on path)
      NS_WeakMomentumDiff_OPEN s     -- NOW VACUOUS (Bochner WeakMomentum in Phase 37)
      NS_ScalarLeibnizAdjoint_OPEN s -- Leibniz + MVT (next)
      NS_WeakInitCont_Degenerate_OPEN s -- CLOSED by Phase 37b direct proof

    CERT AXIOMS: classical trio only. -/
theorem phase37a_gap_accounting : True := trivial

end TheoremaAureum.Towers.NS.CorrSemigroupSelfAdj
