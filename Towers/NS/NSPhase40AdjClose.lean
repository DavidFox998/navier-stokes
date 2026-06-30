/-
  NSPhase40AdjClose.lean  --  Phase 40: NS Tower, navier-stokes repo
  Author: David Fox  |  Date: May 21, 2026
  Series: Opera Numerorum (internal: Battle Plan v1.6)

  PHASE 40: Close NS_AdjointSymmetry_OPEN and NS_AdjointInnerDerivMap_OPEN.
  Both defined in NSAdjointSymmetry.lean (Phase 38b).  0 sorry.  Classical trio.
  NS Clay Surface #1: LOCKED OPEN.  No Clay Millennium Prize claim.

  PROOF OUTLINES:

  NS_AdjointSymmetry_PROVED:
    inner_s(stokes(corrSem T u), embed phi) = inner_s(stokes u, embed(corrSem T phi))
    Both sides expand via inner_Hdiv_eq + L2.inner_def to integrals over mu(s).
    ae coeFn rewrites:
      stokes(corrSem T u)_xi = stokeSym xi * corrSemSym T xi * u_xi  [stokes_coe_ae + corrSem_coe_ae, mu(s+2) -> mu s via filter_mono ae_mono mu_mono]
      embed(phi)_xi = phi_xi  [coeFn_inclLp]
      stokes(u)_xi = stokeSym xi * u_xi  [stokes_coe_ae]
      embed(corrSem T phi)_xi = corrSemSym T xi * phi_xi  [coeFn_inclLp + corrSem_coe_ae]
    Pointwise: inner(stokeSym * corrSemSym T * u_xi, phi_xi)
      = conj(stokeSym * corrSemSym T) * inner(u_xi, phi_xi)   [inner_smul_left, smul_smul]
      = stokeSym * corrSemSym T * inner(u_xi, phi_xi)          [both real: conj = id]
      = stokeSym * inner(u_xi, corrSemSym T * phi_xi)          [inner_smul_right reversed]
      = inner(stokeSym * u_xi, corrSemSym T * phi_xi)          [ring]
    ring closes.

  NS_AdjointInnerDerivMap_PROVED:
    inner_{s+2}(u0, corrSemDerivMap T phi) = -inner_s(stokes(corrSem T u0), embed phi)
    Step 1: LHS = int corrSemDerivSym T xi * inner(u0_xi, phi_xi) d mu(s+2)
            [inner_smul_right + corrSemDeriv_coe_ae]
    Step 2: = int ((1+||xi||^2):C)^2 * (corrSemDerivSym T xi * inner(u0_xi, phi_xi)) d mu(s)
            [NS_MuIntegralShift_PROVED; integrability via Integrable.mono + bound 1/4]
    Step 3: RHS = int -inner(stokeSym * corrSemSym T * u0_xi, phi_xi) d mu(s)
            [inner_Hdiv_eq + L2.inner_def + integral_neg + coeFn ae]
    Step 4: Pointwise at xi:
            ((1+n^2):C)^2 * (-(rate xi:C) * corrSemSym T xi) * inner
              = -(rate xi * (1+n^2)^2) * corrSemSym T xi * inner
              = -n^2 * corrSemSym T xi * inner
            [by corrSemigroupRate_integrand_weight; linear_combination]
            RHS: -(conj(stokeSym) * conj(corrSemSym T)) * inner  [inner_smul_left, smul_smul]
              = -(n^2 * corrSemSym T xi) * inner   [both real: conj = id]
            linear_combination -corrSemigroupRate_integrand_weight ξ (corrSemSym T ξ * inner).

  #print axioms NS_AdjointSymmetry_PROVED = classical trio.
  #print axioms NS_AdjointInnerDerivMap_PROVED = classical trio.
-/

import Towers.NS.NSAdjointSymmetry
import Towers.NS.NSMuIntegralShift
import Towers.NS.NSDerivSemigroup
import Mathlib.MeasureTheory.Function.L2Space

namespace TheoremaAureum.Towers.NS.Phase40AdjClose

open Real Set Filter Topology MeasureTheory
open TheoremaAureum.Towers.NS.FunctionSpaces
open TheoremaAureum.Towers.NS.SemigroupDef
open TheoremaAureum.Towers.NS.WeakSolution
open TheoremaAureum.Towers.NS.FourierInner
open TheoremaAureum.Towers.NS.MuIntegralShift
open TheoremaAureum.Towers.NS.GeneratorClose
open TheoremaAureum.Towers.NS.DerivSemigroup
open TheoremaAureum.Towers.NS.AdjointSymmetry
open TheoremaAureum.Towers.NS.StokesAdjoint
open TheoremaAureum.Towers.NS.Stokes
open NSTower

variable {s : ℝ}

/-! ## I. Private coeFn ae helpers -/

/-- corrSemigroup coeFn ae at mu(s+2).
    Re-proved locally (original is private in NSCorrSemigroupSelfAdj). -/
private lemma corrSem_coe_ae (t : ℝ) (ht : 0 ≤ t) (v : Hdiv_free (s + 2)) :
    ((corrSemigroup s t ht v : Hdiv_free (s + 2)) : Lp Val 2 (mu (s + 2)))
    =ᵐ[mu (s + 2)]
    fun ξ => corrSemigroupSymbol t ξ • (v : Lp Val 2 (mu (s + 2))) ξ := by
  have h1 := (corrSemigroup_memLp s t ht (v : Lp Val 2 (mu (s + 2)))).coeFn_toLp
  filter_upwards [h1] with ξ hξ
  simp only [corrSemigroup, ContinuousLinearMap.codRestrict_apply,
    ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
    corrSemigroupLin, LinearMap.coe_mk, AddHom.coe_mk]
  exact hξ

/-- corrSemigroupDerivMap coeFn ae at mu(s+2). -/
private lemma corrSemDeriv_coe_ae (t : ℝ) (ht : 0 ≤ t) (v : Hdiv_free (s + 2)) :
    ((corrSemigroupDerivMap s t ht v : Hdiv_free (s + 2)) : Lp Val 2 (mu (s + 2)))
    =ᵐ[mu (s + 2)]
    fun ξ => corrSemigroupDerivSymbol t ξ • (v : Lp Val 2 (mu (s + 2))) ξ := by
  have h1 := (corrSemigroupDeriv_memLp t ht (v : Lp Val 2 (mu (s + 2)))).coeFn_toLp
  filter_upwards [h1] with ξ hξ
  simp only [corrSemigroupDerivMap, ContinuousLinearMap.codRestrict_apply,
    ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
    corrSemigroupDerivLin, LinearMap.coe_mk, AddHom.coe_mk]
  exact hξ

/-- stokes_op s coeFn ae at mu s (inline from NSStokesAdjoint pattern). -/
private lemma stokes_coe_ae (u : Hdiv_free (s + 2)) :
    ((stokes_op s u : Hdiv_free s) : Lp Val 2 (mu s)) =ᵐ[mu s]
    fun ξ => stokesSymbol ξ • (u : Lp Val 2 (mu (s + 2))) ξ := by
  have h1 := coeFn_stokes_mult s (u : Lp Val 2 (mu (s + 2)))
  filter_upwards [h1] with ξ hξ
  simp only [stokes_op, ContinuousLinearMap.codRestrict_apply,
    ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
  exact hξ

/-! ## II. NS_AdjointSymmetry_PROVED -/

/-- **Phase 40: NS_AdjointSymmetry_OPEN CLOSED (0 sorry, classical trio).**

    inner_s(stokes(corrSem T u), embed phi) = inner_s(stokes u, embed(corrSem T phi)).

    Proof: expand both sides as L2 integrals over mu(s) via inner_Hdiv_eq + L2.inner_def.
    Apply ae coeFn lemmas (corrSem_coe_ae via filter_mono ae_mono mu_mono, stokes_coe_ae,
    coeFn_inclLp) to get pointwise symbols.  Pointwise:
      inner(stokeSym * corrSemSym * u_xi, phi_xi) = inner(stokeSym * u_xi, corrSemSym * phi_xi)
    Both equal stokeSym * corrSemSym * inner(u_xi, phi_xi) since both symbols are real
    (conj_ofReal).  ring closes.

    #print axioms NS_AdjointSymmetry_PROVED = classical trio. -/
theorem NS_AdjointSymmetry_PROVED : NS_AdjointSymmetry_OPEN s := by
  intro T hT u φ
  simp only [inner_Hdiv_eq, L2.inner_def]
  apply integral_congr_ae
  -- ae coeFn facts at mu s
  have hSAu := stokes_coe_ae (corrSemigroup s T hT u)
  have hEφ : ((embed φ : Hdiv_free s) : Lp Val 2 (mu s)) =ᵐ[mu s]
      (φ : Lp Val 2 (mu (s + 2))) := coeFn_inclLp _ _
  -- corrSem coeFn at mu(s+2), then downscale to mu s via filter_mono
  have hAu : ((corrSemigroup s T hT u : Hdiv_free (s + 2)) : Lp Val 2 (mu (s + 2)))
      =ᵐ[mu s] fun ξ => corrSemigroupSymbol T ξ • (u : Lp Val 2 (mu (s + 2))) ξ :=
    (corrSem_coe_ae T hT u).filter_mono (ae_mono (mu_mono (by linarith)))
  have hSu := stokes_coe_ae u
  have hEAφ : ((embed (corrSemigroup s T hT φ) : Hdiv_free s) : Lp Val 2 (mu s)) =ᵐ[mu s]
      (corrSemigroup s T hT φ : Lp Val 2 (mu (s + 2))) := coeFn_inclLp _ _
  have hAφ : ((corrSemigroup s T hT φ : Hdiv_free (s + 2)) : Lp Val 2 (mu (s + 2)))
      =ᵐ[mu s] fun ξ => corrSemigroupSymbol T ξ • (φ : Lp Val 2 (mu (s + 2))) ξ :=
    (corrSem_coe_ae T hT φ).filter_mono (ae_mono (mu_mono (by linarith)))
  filter_upwards [hSAu, hEφ, hAu, hSu, hEAφ, hAφ] with ξ h1 h2 h3 h4 h5 h6
  -- Rewrite coeFns pointwise
  rw [h1, h3, h2, h4, h5, h6]
  -- inner(stokeSym * corrSemSym * u_xi, phi_xi) = inner(stokeSym * u_xi, corrSemSym * phi_xi)
  rw [smul_smul, inner_smul_left, inner_smul_right, inner_smul_right]
  simp only [corrSemigroupSymbol, stokesSymbol, map_mul, map_ofReal, Complex.conj_ofReal]
  ring

/-! ## III. NS_AdjointInnerDerivMap_PROVED -/

/-- **Phase 40: NS_AdjointInnerDerivMap_OPEN CLOSED (0 sorry, classical trio).**

    inner_{s+2}(u0, corrSemDerivMap T phi) = -inner_s(stokes(corrSem T u0), embed phi).

    Proof steps:
    (1) LHS = int corrSemDerivSym T xi * inner(u0_xi, phi_xi) d mu(s+2)
        via inner_smul_right + corrSemDeriv_coe_ae.
    (2) Apply NS_MuIntegralShift_PROVED (integrability via Integrable.mono, bound 1/4).
        = int ((1+||xi||^2):C)^2 * (corrSemDerivSym T xi * inner) d mu(s).
    (3) Expand RHS -inner_s via inner_Hdiv_eq + L2.inner_def + integral_neg.
    (4) Pointwise via stokes_coe_ae + corrSem_coe_ae + inner_smul_left:
        RHS at xi = -(stokeSym xi * corrSemSym T xi) * inner(u0_xi, phi_xi).
        LHS at xi = ((1+n^2)^2 * corrSemDerivSym T xi) * inner
                  = -(n^2) * corrSemSym T xi * inner  [corrSemigroupRate_integrand_weight].
    Both sides equal. linear_combination -corrSemigroupRate_integrand_weight ... closes.

    #print axioms NS_AdjointInnerDerivMap_PROVED = classical trio. -/
theorem NS_AdjointInnerDerivMap_PROVED : NS_AdjointInnerDerivMap_OPEN s := by
  intro T hT u₀ φ
  -- Step 1: Rewrite LHS as integral of corrSemDerivSym * inner d mu(s+2)
  have hDφ := corrSemDeriv_coe_ae T hT φ
  have hstep1 : @inner ℂ (Hdiv_free (s + 2)) _ u₀ (corrSemigroupDerivMap s T hT φ) =
      ∫ ξ : FreqDomain, corrSemigroupDerivSymbol T ξ *
        @inner ℂ Val _ ((u₀ : Lp Val 2 (mu (s + 2))) ξ) ((φ : Lp Val 2 (mu (s + 2))) ξ)
        ∂mu (s + 2) := by
    rw [inner_Hdiv_eq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hDφ] with ξ hξ
    rw [hξ, inner_smul_right]
  rw [hstep1]
  -- Step 2: Integrability of corrSemDerivSym * inner w.r.t. mu(s+2)
  have hInn : Integrable (fun ξ : FreqDomain =>
      @inner ℂ Val _ ((u₀ : Lp Val 2 (mu (s + 2))) ξ) ((φ : Lp Val 2 (mu (s + 2))) ξ))
      (mu (s + 2)) :=
    L2.inner_integrable u₀ φ
  have hInt : Integrable (fun ξ : FreqDomain => corrSemigroupDerivSymbol T ξ *
      @inner ℂ Val _ ((u₀ : Lp Val 2 (mu (s + 2))) ξ) ((φ : Lp Val 2 (mu (s + 2))) ξ))
      (mu (s + 2)) :=
    hInn.mono
      ((continuous_corrSemigroupDerivSymbol T).aestronglyMeasurable.mul
        hInn.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ξ => by
        rw [norm_mul]
        have hb : ‖corrSemigroupDerivSymbol T ξ‖ ≤ 1 :=
          le_trans (corrSemigroupDerivSymbol_norm_le T hT ξ) (by norm_num)
        exact mul_le_of_le_one_left (norm_nonneg _) hb)
  -- Step 3: Apply NS_MuIntegralShift_PROVED
  rw [NS_MuIntegralShift_PROVED hInt]
  -- Step 4: Expand RHS as -integral over mu(s)
  have hRHS : -@inner ℂ (Hdiv_free s) _
      (stokes_op s (corrSemigroup s T hT u₀)) (embed φ) =
      ∫ ξ : FreqDomain, -@inner ℂ Val _
          ((stokes_op s (corrSemigroup s T hT u₀) : Hdiv_free s : Lp Val 2 (mu s)) ξ)
          ((embed φ : Hdiv_free s : Lp Val 2 (mu s)) ξ) ∂mu s := by
    rw [inner_Hdiv_eq, L2.inner_def, integral_neg]
  rw [hRHS]
  -- Step 5: Pointwise equality via integral_congr_ae
  apply integral_congr_ae
  have hSAu₀ := stokes_coe_ae (corrSemigroup s T hT u₀)
  have hAu₀ : ((corrSemigroup s T hT u₀ : Hdiv_free (s + 2)) : Lp Val 2 (mu (s + 2)))
      =ᵐ[mu s] fun ξ => corrSemigroupSymbol T ξ • (u₀ : Lp Val 2 (mu (s + 2))) ξ :=
    (corrSem_coe_ae T hT u₀).filter_mono (ae_mono (mu_mono (by linarith)))
  have hEφ : ((embed φ : Hdiv_free s) : Lp Val 2 (mu s)) =ᵐ[mu s]
      (φ : Lp Val 2 (mu (s + 2))) := coeFn_inclLp _ _
  filter_upwards [hSAu₀, hAu₀, hEφ] with ξ h1 h2 h3
  -- Rewrite coeFns: stokes(corrSem T u0)_xi = stokeSym * corrSemSym T * u0_xi
  rw [h1, h2, h3]
  -- inner(stokeSym * (corrSemSym T * u0_xi), phi_xi) after smul_smul
  rw [smul_smul, inner_smul_left]
  simp only [stokesSymbol, corrSemigroupSymbol, map_mul, map_ofReal, Complex.conj_ofReal]
  -- Goal: ((1+‖ξ‖^2:ℝ):ℂ)^2 * (corrSemDerivSym T ξ * inner(u0_xi, phi_xi))
  --     = -(‖ξ‖^2 : ℝ : ℂ) * corrSemSym T ξ * inner(u0_xi, phi_xi)
  -- Use corrSemigroupRate_integrand_weight to close
  have hadj := corrSemigroupRate_integrand_weight ξ
      (corrSemigroupSymbol T ξ *
       @inner ℂ Val _ ((u₀ : Lp Val 2 (mu (s + 2))) ξ) ((φ : Lp Val 2 (mu (s + 2))) ξ))
  simp only [corrSemigroupDerivSymbol]
  push_cast at hadj ⊢
  linear_combination -hadj

/-! ## IV. Phase 40 gap accounting -/

/-- **Phase 40 gap accounting (0 sorry, 0 cert axioms, classical trio).**

    PROVED IN PHASE 40:
      NS_AdjointSymmetry_PROVED      -- stokes-corrSem Fourier commutativity
      NS_AdjointInnerDerivMap_PROVED  -- derivative inner product identity

    NAMED OPEN DEFS ELIMINATED:
      NS_AdjointSymmetry_OPEN s        -- CLOSED Phase 40
      NS_AdjointInnerDerivMap_OPEN s   -- CLOSED Phase 40

    REMAINING NAMED OPEN DEFS (NS Tower after Phase 40):
      NS_StokesMaxReg_OPEN s           -- Hieber-Pruss 2018; NOT on WeakInitCont path
      NS_CorrSemigroupFourierEq_OPEN s -- Fourier inner product rep; Phase 17 (deepest gap)
      NS_ScalarLeibnizAdjoint_OPEN s   -- Leibniz + MVT; Phase 39 (conditional on Phase 40)
      NS_AdjointIntegralConst_OPEN s   -- orbit identity via adjoint

    CHAIN TIGHTENED after Phase 40:
      NS_CorrSemigroupFourierEq_OPEN => NS_ScalarLeibnizAdjoint_OPEN (given Phase 40)
      => NS_AdjointIntegralConst_OPEN => Gap B => NS_ClayStatement
    NS_StokesMaxReg_OPEN is independent (not on WeakInitCont path).

    CERT AXIOMS: classical trio only.
    NS Clay Surface #1: LOCKED OPEN.  No Clay Millennium Prize claim. -/
theorem phase40_gap_accounting : True := trivial

end TheoremaAureum.Towers.NS.Phase40AdjClose
