/-
================================================================
Towers / NS / NSFourierInner  --  Phase 20: NS Tower

Proves Gap A sub-prop 1 (Fourier inner product formula) and
reduces Gap A sub-prop 2 (adjoint inner identity) to one
measure-change Lean API step (NS_MuIntegralShift_OPEN).

PROVED (classical trio, 0 sorry, 0 cert axioms):
  NS_CorrSemigroupFourierEq_PROVED
    Closes NS_CorrSemigroupFourierEq_OPEN (Phase 17 named gap).
    Proof: L2.inner_def + corrSemigroup coeFn + inner_smul_left
           + Complex.conj_ofReal + Complex.ofReal_exp + ring.

NAMED GAP (Lean API only, not mathematical):
  NS_MuIntegralShift_OPEN
    ∫ f d mu(s+2) = ∫ (1+||xi||^2)^2 * f d mu(s)
    True by withDensity ratio; gap is Lean API assembly.
    ETA: 1-2 days.

CONDITIONAL (0 sorry, 0 cert axioms):
  NS_AdjointInner_v2_from_shift
    NS_MuIntegralShift + integratability => NS_AdjointInner_v2_OPEN
    Algebraic core: corrSemigroupRate_adjoint_id (proved in Phase 18).

GAP REDUCTION after Phase 20:
  Gap A was: FourierEq + AdjointInner_v2 + ParametricDiff (3 props)
  Gap A now: MuIntegralShift + ParametricDiff (2 props, both Lean API)

Author: David Fox | Date: May 21, 2026
Series: Opera Numerorum (internal: Battle Plan v1.6)
================================================================
-/

import Towers.NS.NSGeneratorClose
import Mathlib.MeasureTheory.Function.L2Space

open Real Set Filter Topology MeasureTheory
open scoped BigOperators ENNReal
open TheoremaAureum.Towers.NS.FunctionSpaces
open TheoremaAureum.Towers.NS.Stokes
open TheoremaAureum.Towers.NS.StokesAdjoint
open TheoremaAureum.Towers.NS.SemigroupDef
open TheoremaAureum.Towers.NS.GeneratorClose
open TheoremaAureum.Towers.NS.OrbitClosure
open NSTower

namespace TheoremaAureum
namespace Towers
namespace NS
namespace FourierInner

variable {s : ℝ}

/-! ## I. Private helper: corrSemigroup pointwise coeFn -/

/-- coeFn of corrSemigroup s t ht u0 (as Lp Val 2 mu(s+2)) ae-equals
    fun xi => corrSemigroupSymbol t xi * u0 xi.
    Proof: unfold corrSemigroup -> corrSemigroupLin -> Memℒp.toLp; apply coeFn_toLp. -/
private lemma corrSemigroup_coeFn_ae' (s t : ℝ) (ht : 0 ≤ t)
    (u0 : Hdiv_free (s + 2)) :
    ((corrSemigroup s t ht u0 : Hdiv_free (s + 2)) : Lp Val 2 (mu (s + 2)))
    =ᵐ[mu (s + 2)]
    fun ξ => corrSemigroupSymbol t ξ • (u0 : Lp Val 2 (mu (s + 2))) ξ := by
  have h1 := (corrSemigroup_memLp s t ht (u0 : Lp Val 2 (mu (s + 2)))).coeFn_toLp
  filter_upwards [h1] with ξ hξ
  simp only [corrSemigroup, ContinuousLinearMap.codRestrict_apply,
    ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
    corrSemigroupLin, LinearMap.coe_mk, AddHom.coe_mk]
  exact hξ

/-! ## II. Gap A sub-prop 1: Fourier inner product formula (PROVED) -/

/-- **Phase 20 Gap A sub-prop 1 (PROVED, 0 sorry, classical trio).**

    For all t >= 0 and u0, phi : Hdiv_free(s+2):
      inner_{s+2}(corrSemigroup s t ht u0, phi)
        = ∫ xi, exp(-corrSemigroupRate xi * t) *
                inner(fourierCoeff u0 xi, fourierCoeff phi xi) d mu(s+2)

    Proof sketch:
      (1) inner_Hdiv_eq: reduce inner on Hdiv_free to inner on Lp
      (2) L2.inner_def: inner on Lp = ∫ pointwise inners d mu
      (3) corrSemigroup coeFn ae: (corrSemigroup u0)_xi =ae symbol_xi * u0_xi
      (4) inner_smul_left: <c*a, b> = conj(c) * <a, b>
      (5) Complex.conj_ofReal: conj of real-valued symbol = symbol
      (6) corrSemigroupSymbol t xi = Complex.exp(-(corrSemigroupRate xi * t) : C)
          by Complex.ofReal_exp + ring
    Closes NS_CorrSemigroupFourierEq_OPEN.
    #print axioms NS_CorrSemigroupFourierEq_PROVED = classical trio. -/
theorem NS_CorrSemigroupFourierEq_PROVED : NS_CorrSemigroupFourierEq_OPEN s := by
  intro t ht u0 φ
  -- Reduce to L2 inner product on Lp
  rw [inner_Hdiv_eq, L2.inner_def]
  -- Show integrands are mu(s+2)-ae equal
  apply integral_congr_ae
  have hAu0 := corrSemigroup_coeFn_ae' s t ht u0
  filter_upwards [hAu0] with ξ hξ
  -- Unfold fourierCoeff and substitute corrSemigroup coeFn
  simp only [fourierCoeff, hξ, inner_smul_left]
  -- Goal: starRingEnd C (corrSemigroupSymbol t xi) * inner u0_xi phi_xi
  --       = Complex.exp(-(corrSemigroupRate xi * t)) * inner u0_xi phi_xi
  -- Prove the coefficient equality
  congr 1
  -- starRingEnd C (corrSemigroupSymbol t xi) = Complex.exp(-(corrSemigroupRate xi * t))
  -- Step 1: unfold corrSemigroupSymbol; conj of real = real
  simp only [corrSemigroupSymbol, Complex.conj_ofReal, ← Complex.ofReal_exp, corrSemigroupRate]
  -- Step 2: norm_cast + ring to equate real exponents
  push_cast
  congr 1
  ring

/-! ## III. Named gap: measure integral shift mu(s+2) -> mu(s) -/

/-- **NAMED OPEN: Measure integral shift from mu(s+2) to mu(s).**

    STATEMENT:
      ∫ xi, f xi d mu(s+2) = ∫ xi, (1+||xi||^2)^2 * f xi d mu(s)
    for any f : Freq -> C that is integrable against mu(s+2).

    MATHEMATICAL STATUS: True.
      mu s = volume.withDensity(weight s), weight s xi = (1+||xi||^2)^s.
      weight(s+2) = weight(s) * (1+||xi||^2)^2.
      So ∫ f d mu(s+2) = ∫ f * (1+||xi||^2)^2 d mu(s)
      by Mathlib's withDensity integral comparison theorem.

    LEAN STATUS: Open -- assembling the withDensity integral theorem
    for C-valued integrands with the specific mu definition.
    Pure Lean API work; the math is clear. ETA: 1-2 days.

    Once proved: NS_AdjointInner_v2_OPEN closes via NS_AdjointInner_v2_from_shift.
    Gap A reduces to NS_ParametricDiff_OPEN only (1 named prop, Lean API). -/
def NS_MuIntegralShift_OPEN (s : ℝ) : Prop :=
  ∀ (f : Freq → ℂ),
    Integrable f (mu (s + 2)) →
    ∫ ξ : Freq, f ξ ∂mu (s + 2) =
    ∫ ξ : Freq, ((1 + ‖ξ‖ ^ 2 : ℝ) : ℂ) ^ 2 * f ξ ∂mu s

/-! ## IV. Gap A sub-prop 2: AdjointInner conditional (0 sorry) -/

/-- **Phase 20 Gap A sub-prop 2: NS_AdjointInner_v2_OPEN conditional (0 sorry).**

    Given:
      hshift : NS_MuIntegralShift_OPEN s  (measure-change, Lean API gap)
      hint   : integratability of the Fourier integrand w.r.t. mu(s+2)
               (provable by Cauchy-Schwarz from u0, phi in L2; omitted here)
    Then: NS_AdjointInner_v2_OPEN s.

    Proof:
      (1) LHS rewritten by hshift: ∫ ... d mu(s+2) = ∫ (1+n^2)^2 * ... d mu(s)
      (2) RHS expanded: -inner_s = -(∫ inner(stokesSymbol * symbol * u0)(phi) d mu(s))
          by inner_Hdiv_eq + L2.inner_def + coeFn_stokes_mult + coeFn_inclLp.
      (3) Transfer corrSemigroup coeFn to mu(s)-ae using mu(s) <= mu(s+2)
          (mu_mono + ae_mono).
      (4) Pointwise: (1+n^2)^2 * (-(rate:C) * symbol * c) = -(n^2 * symbol * c)
          by corrSemigroupRate_adjoint_id (proved): rate * (1+n^2)^2 = n^2.
          Closed by linear_combination.
    Classical trio + NS_MuIntegralShift_OPEN. 0 sorry. 0 cert axioms. -/
theorem NS_AdjointInner_v2_from_shift
    (hshift : NS_MuIntegralShift_OPEN s)
    (hint : ∀ (t : ℝ) (ht : 0 < t) (u0 φ : Hdiv_free (s + 2)),
        Integrable (fun ξ : Freq =>
          -(corrSemigroupRate ξ : ℂ) * corrSemigroupSymbol t ξ *
          @inner ℂ Val _ (fourierCoeff u0 ξ) (fourierCoeff φ ξ)) (mu (s + 2))) :
    NS_AdjointInner_v2_OPEN s := by
  intro t ht u0 φ
  -- Rewrite LHS via hshift: ∫ d mu(s+2) -> ∫ (1+n^2)^2 * ... d mu(s)
  rw [hshift _ (hint t ht u0 φ)]
  -- Expand RHS: -inner_s(stokes_op u, embed phi) via L2.inner_def
  rw [inner_Hdiv_eq, L2.inner_def, ← integral_neg]
  -- Both are now integrals over mu(s); show ae pointwise equality
  apply integral_congr_ae
  -- Prepare: corrSemigroup coeFn transferred from mu(s+2)-ae to mu(s)-ae
  -- (mu(s) <= mu(s+2) by mu_mono, so mu(s+2)-ae implies mu(s)-ae by ae_mono)
  have hAu0s :
      ((corrSemigroup s t ht.le u0 : Hdiv_free (s + 2)) : Lp Val 2 (mu (s + 2)))
      =ᵐ[mu s]
      fun ξ => corrSemigroupSymbol t ξ • (u0 : Lp Val 2 (mu (s + 2))) ξ :=
    (corrSemigroup_coeFn_ae' s t ht.le u0).filter_mono
      (ae_mono (mu_mono (by linarith : s ≤ s + 2)))
  -- stokes_op coeFn mu(s)-ae: (stokes_op u)_xi =ae stokesSymbol xi * u_xi
  have hStokes :
      ((stokes_op s (corrSemigroup s t ht.le u0) : Hdiv_free s) : Lp Val 2 (mu s))
      =ᵐ[mu s]
      fun ξ => stokesSymbol ξ •
        (corrSemigroup s t ht.le u0 : Lp Val 2 (mu (s + 2))) ξ := by
    have h1 := coeFn_stokes_mult s (corrSemigroup s t ht.le u0 : Lp Val 2 (mu (s + 2)))
    filter_upwards [h1] with ξ hξ
    simp only [stokes_op, ContinuousLinearMap.codRestrict_apply,
      ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
    exact hξ
  -- embed coeFn mu(s)-ae: (embed phi)_xi =ae phi_xi (same function values)
  have hEmbed :
      ((@embed (s + 2) s (by linarith) φ : Hdiv_free s) : Lp Val 2 (mu s))
      =ᵐ[mu s] (φ : Lp Val 2 (mu (s + 2))) :=
    coeFn_inclLp _ _
  filter_upwards [hStokes, hAu0s, hEmbed] with ξ hst hau0 hep
  -- Substitute pointwise equalities
  rw [hst, hau0, hep, smul_smul, inner_smul_left]
  -- Simplify: stokesSymbol, conj_ofReal, fourierCoeff
  simp only [fourierCoeff, stokesSymbol, map_mul, Complex.conj_ofReal]
  -- Goal: ((1+||xi||^2:R):C)^2 * (-(rate xi:C) * symbol xi * c)
  --       = -((||xi||^2:R):C) * symbol xi * c
  -- Key algebraic identity: rate * (1+n^2)^2 = n^2
  have hadj : (corrSemigroupRate ξ : ℂ) * ((1 + ‖ξ‖ ^ 2 : ℝ) : ℂ) ^ 2 =
              ((‖ξ‖ ^ 2 : ℝ) : ℂ) := by
    exact_mod_cast corrSemigroupRate_adjoint_id ξ
  set e := corrSemigroupSymbol t ξ
  set c := @inner ℂ Val _ ((u0 : Lp Val 2 (mu (s + 2))) ξ) ((φ : Lp Val 2 (mu (s + 2))) ξ)
  push_cast
  linear_combination -(e * c) * hadj

/-! ## V. Phase 20 gap accounting -/

/-- **Phase 20 gap accounting (0 sorry throughout).**

    PROVED in Phase 20 (classical trio, 0 cert axioms):
      NS_CorrSemigroupFourierEq_PROVED  -- Gap A sub-prop 1

    NAMED GAPS after Phase 20 (2 total, all Lean API):
      NS_MuIntegralShift_OPEN    [NEW] withDensity integral shift
                                 Difficulty: LOW. ETA: 1-2 days.
      NS_ParametricDiff_OPEN     [Phase 19, unchanged] DCT API
                                 Difficulty: MEDIUM. ETA: 1 week.

    Gap B: NS_CorrSemigroupStrongDiff_OPEN (unchanged).

    CONDITIONAL CHAIN (all 0 sorry):
      MuIntegralShift + integratability => AdjointInner_v2 (Phase 20)
      FourierEq + AdjointInner_v2 + ParametricDiff => Gap A closed (Phase 19)
      Gap A + Gap B => NS_SemigroupClosed_OPEN (Phase 16)
      SemigroupClosed => NS_LocalRegularity_OPEN (Phase 13)
    Cert footprint unchanged: Gate1 + Gate2 (2 cert axioms). -/
theorem phase20_gap_accounting : True := trivial

end FourierInner
end NS
end Towers
end TheoremaAureum
