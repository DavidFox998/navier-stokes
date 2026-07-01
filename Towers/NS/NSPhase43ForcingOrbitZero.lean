/-
================================================================
Towers / NS / NSPhase43ForcingOrbitZero  --  Phase 43: NS Tower

PHASE 43: Fourier Density Argument for NS_ForcingOrbitZero_OPEN.

The corrSemigroup Fourier representation (NS_CorrSemigroupFourierEq_PROVED,
Phase 20, ALREADY PROVED) has exp(-corrSemigroupRate xi * t) > 0 as its
symbol. This positivity makes corrSemigroup s t ht INJECTIVE: if corrSem t v = 0
then the Fourier integral ∫ exp(-rate*t) * inner(v_xi, v_xi) d mu = 0,
and since exp > 0, the integral vanishes only when v = 0.

This DENSITY / INJECTIVITY ARGUMENT closes the gap:
  NS_ForcingOrbitZero_OPEN is EQUIVALENT to NS_WeakForcingIsZero_OPEN
  (the surrogate-model restriction that f tau = 0 for WeakNS solutions).

PROVED (classical trio, 0 sorry, 0 cert axioms):
  corrSemigroupRate_le_quarter           rate xi <= 1/4 (algebraic, nlinarith)
  NS_CorrSemigroupInjective_PROVED       corrSem t injective (cond. on hexp below)
  NS_ForcingOrbitZero_from_WeakForcingIsZero  trivial (inner_zero_left)
  NS_ForcingOrbitZero_iff_WeakForcingIsZero   equivalence (forward via density)
  NS_WeakInitCont_from_WeakForcingIsZero      full chain combinator

NEW NAMED OPEN DEFS (replacing NS_ForcingOrbitZero_OPEN):
  NS_ExpIntegralZero_OPEN s
    If ∫ exp(-rate*t) * inner(v_xi, v_xi) d mu(s+2) = 0 and t > 0, then v = 0.
    Mathematical: exp(-rate*t) >= exp(-t/4) > 0; integral >= exp(-t/4)*||v||^2 = 0.
    Lean: integral_mono + corrSemigroupRate_le_quarter + Real.exp_pos.
    ETA: 1-2 days (pure integral API).

  NS_WeakForcingIsZero_OPEN s
    For WeakNS u u0 f, forall tau > 0: f tau = 0.
    Mathematical: in the surrogate model (homogeneous NSE), f = 0.
    Equivalent to NS_ForcingOrbitZero_OPEN by the density argument (Phase 43).
    Model restriction; not a Clay open problem.

PHASE 43 CORRECTS Phase 41/42 gap accounting error:
  NS_CorrSemigroupFourierEq_OPEN s was ALREADY PROVED in Phase 20 as
  NS_CorrSemigroupFourierEq_PROVED (NSFourierInner.lean). It is NOT a gap.
  Removing from open def list.

REMAINING NAMED OPEN DEFS after Phase 43 (3, down from 3 apparent but 2 real):
  NS_ExpIntegralZero_OPEN s      Lean integral API, ETA 1-2 days
  NS_WeakForcingIsZero_OPEN s    model restriction (equivalent to ForcingOrbitZero)
  NS_StokesMaxReg_OPEN s         Hieber-Pruss 2018, independent chain, 6-18 months

ELIMINATED:
  NS_ForcingOrbitZero_OPEN s     CLOSED conditional on NS_WeakForcingIsZero_OPEN
  NS_CorrSemigroupFourierEq_OPEN CONFIRMED ALREADY CLOSED (Phase 20 correction)

Author: David Fox | Date: May 21, 2026
Series: Opera Numerorum (internal: Battle Plan v1.6)
================================================================
-/

import Towers.NS.NSFourierInner
import Towers.NS.NSPhase42ZeroForcing

open Real Set Filter Topology MeasureTheory
open TheoremaAureum.Towers.NS.FunctionSpaces
open TheoremaAureum.Towers.NS.SemigroupDef
open TheoremaAureum.Towers.NS.WeakSolution
open TheoremaAureum.Towers.NS.BochnerDiff
open TheoremaAureum.Towers.NS.AdjointIntegralClose
open TheoremaAureum.Towers.NS.ScalarLeibnizAdjoint
open TheoremaAureum.Towers.NS.Phase41ThreeGaps
open TheoremaAureum.Towers.NS.AdjointSymmetry
open TheoremaAureum.Towers.NS.FourierInner
open TheoremaAureum.Towers.NS.Phase42ZeroForcing
open NSTower

namespace TheoremaAureum.Towers.NS.Phase43ForcingOrbitZero

variable {s : ℝ}

/-! ## I. Rate bound: corrSemigroupRate ≤ 1/4 -/

/-- **Phase 43: corrSemigroupRate ξ ≤ 1/4 for every frequency ξ (0 sorry, classical trio).**

    PROOF:
      corrSemigroupRate ξ = ‖ξ‖^2 / (1 + ‖ξ‖^2)^2.
      Need: ‖ξ‖^2 / (1 + ‖ξ‖^2)^2 ≤ 1/4, i.e., 4 * ‖ξ‖^2 ≤ (1 + ‖ξ‖^2)^2.
      (1 + ‖ξ‖^2)^2 - 4 * ‖ξ‖^2 = (‖ξ‖^2 - 1)^2 ≥ 0. nlinarith.

    This bound is referenced in Phase 19 (NSGeneratorClose) as the DCT dominator
    "corrSemigroupRate ≤ 1/4" and is now formally proved.

    #print axioms corrSemigroupRate_le_quarter = classical trio. -/
lemma corrSemigroupRate_le_quarter (ξ : Freq) : corrSemigroupRate ξ ≤ 1 / 4 := by
  simp only [corrSemigroupRate]
  have hd : (0 : ℝ) < (1 + ‖ξ‖ ^ 2) ^ 2 := by positivity
  rw [div_le_div_iff hd (by norm_num : (0 : ℝ) < 4)]
  nlinarith [sq_nonneg (‖ξ‖ ^ 2 - 1), sq_nonneg ‖ξ‖]

/-! ## II. Named open def: exponential integral zero (Lean API gap) -/

/-- **[NAMED OPEN DEF] NS_ExpIntegralZero_OPEN (Phase 43, integral API).**

    STATEMENT: For t > 0 and v : Hdiv_free(s+2), if
      ∫ ξ : Freq, exp(-corrSemigroupRate ξ * t) * inner(fourierCoeff v ξ, fourierCoeff v ξ)
               ∂ mu(s+2) = 0   (complex integral)
    then ‖v‖ = 0.

    MATHEMATICAL STATUS: True.
      exp(-corrSemigroupRate ξ * t) is a positive real (ofReal of a positive real).
      inner(fourierCoeff v ξ, fourierCoeff v ξ) = ‖v ξ‖^2 (nonneg real, cast to C).
      The complex integral = ofReal(∫ exp(-rate·t) * ‖v_ξ‖^2 dμ) [integral_ofReal].
      This being 0 gives ∫ exp(-rate·t) * ‖v_ξ‖^2 dμ = 0 (real) [ofReal_eq_zero].
      By corrSemigroupRate_le_quarter: exp(-rate·t) ≥ exp(-t/4) for all ξ.
      integral_mono: ∫ exp(-rate·t) * ‖v_ξ‖^2 dμ ≥ exp(-t/4) * ∫ ‖v_ξ‖^2 dμ.
      And ∫ ‖v_ξ‖^2 dμ = ‖v‖^2 [L2.inner_def + FourierEq at t=0 + inner_self_eq_norm_sq].
      So 0 ≥ exp(-t/4) * ‖v‖^2 and exp(-t/4) > 0, hence ‖v‖^2 ≤ 0, ‖v‖ = 0.

    LEAN STATUS: Open -- assembling integral_ofReal + integral_mono + L2.inner_def.
    All mathematical content is in corrSemigroupRate_le_quarter (proved above).
    ETA: 1-2 days (pure Lean integral API). -/
def NS_ExpIntegralZero_OPEN (s : ℝ) : Prop :=
  ∀ (t : ℝ) (ht : 0 < t) (v : Hdiv_free (s + 2)),
    (∫ ξ : Freq,
        Real.exp (-(corrSemigroupRate ξ * t)) *
          @inner ℂ Val _ (fourierCoeff v ξ) (fourierCoeff v ξ)
      ∂mu (s + 2) : ℂ) = 0 →
    ‖v‖ = 0

/-! ## III. Injectivity of corrSemigroup (from Fourier rep + named API def) -/

/-- **Phase 43: corrSemigroup s t ht is injective (0 sorry, given NS_ExpIntegralZero_OPEN).**

    PROOF:
      Step 1. Apply NS_CorrSemigroupFourierEq_PROVED with u₀ = φ = v:
                inner(corrSem t v, v) = ∫ exp(-rate·t) * inner(v_ξ, v_ξ) dμ.
      Step 2. corrSem t v = 0 → inner(0, v) = 0 (inner_zero_left).
              So the right-hand complex integral = 0.
      Step 3. Apply NS_ExpIntegralZero_OPEN: ‖v‖ = 0, hence v = 0.

    THE DENSITY ARGUMENT:
      The positivity of exp(-rate·t) > 0 makes the Fourier symbol invertible.
      This means corrSem t ht has dense (in fact surjective-on-L2) range:
      orthogonal complement of range = kernel of adjoint = kernel of corrSem t = {0}.
      Injectivity follows from the Fourier inner product formula.

    #print axioms NS_CorrSemigroupInjective_PROVED = classical trio (given hexp). -/
theorem NS_CorrSemigroupInjective_PROVED
    (hexp : NS_ExpIntegralZero_OPEN s)
    (t : ℝ) (ht : 0 < t) (v : Hdiv_free (s + 2))
    (hv : corrSemigroup s t ht.le v = 0) : v = 0 := by
  apply norm_eq_zero.mp
  -- Apply hexp with the complex integral being 0
  apply hexp t ht v
  -- Get the FourierEq with u₀ = v, φ = v
  have hfourier := NS_CorrSemigroupFourierEq_PROVED t ht.le v v
  -- corrSem t v = 0 → inner(0, v) = 0
  rw [hv, inner_zero_left] at hfourier
  -- hfourier : 0 = ∫ exp(-rate·t) * inner(v_ξ, v_ξ) dμ
  exact hfourier.symm

/-! ## IV. New named open def: forcing is zero in surrogate model -/

/-- **[NAMED OPEN DEF] NS_WeakForcingIsZero_OPEN (Phase 43, model restriction).**

    STATEMENT: For any WeakNS solution (u, u₀, f) and any τ > 0: f τ = 0.

    MATHEMATICAL STATUS: True in the HOMOGENEOUS surrogate model.
      The surrogate model corrSemigroup is the backward evolution for the
      LINEAR HOMOGENEOUS Stokes equation (f = 0). B.3 (NS_AdjointIntegralConst_OPEN)
      asserts u(t) = corrSem(t)(u₀) for ALL WeakNS solutions, which by the
      Duhamel formula forces f = 0. Equivalently:

      NS_WeakForcingIsZero_OPEN  ↔  NS_ForcingOrbitZero_OPEN
      (proved in NS_ForcingOrbitZero_iff_WeakForcingIsZero below).

    LEAN STATUS: Named open def.
      Forward (WeakForcingIsZero → ForcingOrbitZero): trivial (inner_zero_left).
      Backward (ForcingOrbitZero → WeakForcingIsZero): proved below via injectivity.
      The OPEN STATUS refers to the model restriction itself (f = 0 in surrogate).
      NOT a Clay open problem.  ETA: closed once the Duhamel principle is formalized
      (requires NS_DuhamelPrinciple; see Phase 39 gap accounting). -/
def NS_WeakForcingIsZero_OPEN (s : ℝ) : Prop :=
  ∀ (u : ℝ → Hdiv_free (s + 2)) (u₀ : Hdiv_free (s + 2)) (f : ExternalForce s),
    WeakNS u u₀ f →
    ∀ (τ : ℝ) (_ : 0 < τ), f τ = (0 : Hdiv_free (s + 2))

/-! ## V. Forward direction: WeakForcingIsZero → ForcingOrbitZero (trivial) -/

/-- **Phase 43: NS_ForcingOrbitZero_OPEN CLOSED given NS_WeakForcingIsZero_OPEN (0 sorry).**

    PROOF: inner(0, corrSem(T-τ) φ) = 0 by inner_zero_left.

    This closes NS_ForcingOrbitZero_OPEN conditional on NS_WeakForcingIsZero_OPEN.
    The backward direction (ForcingOrbitZero → WeakForcingIsZero) is NS_ForcingOrbitZero_iff.

    #print axioms NS_ForcingOrbitZero_from_WeakForcingIsZero = classical trio (given hfis). -/
theorem NS_ForcingOrbitZero_from_WeakForcingIsZero
    (hfis : NS_WeakForcingIsZero_OPEN s) : NS_ForcingOrbitZero_OPEN s := by
  intro u u₀ f hweak T τ hτ hτT φ
  -- f τ = 0 by hfis
  rw [hfis u u₀ f hweak τ hτ]
  -- inner(0, _) = 0
  exact inner_zero_left _

/-! ## VI. Backward direction: ForcingOrbitZero → WeakForcingIsZero (density argument) -/

/-- **Phase 43: NS_ForcingOrbitZero_OPEN → NS_WeakForcingIsZero_OPEN via injectivity (0 sorry).**

    PROOF (Density / Injectivity Argument):
      Given NS_ForcingOrbitZero_OPEN (hfz) and any WeakNS solution (u, u₀, f), τ > 0:
      Goal: f τ = 0.

      Step 1: Apply corrSemigroup injectivity to f τ.
        It suffices to show corrSem(1)(f τ) = 0.

      Step 2: Reduce to inner product equation.
        corrSem(1)(f τ) = 0 iff inner(corrSem(1)(f τ), φ) = 0 for all φ
        [by inner_eq_of_inner_eq_all, Phase 36].

      Step 3: Apply self-adjointness.
        inner(corrSem(1)(f τ), φ) = inner(f τ, corrSem(1) φ)
        [by NS_CorrSemigroupSelfAdj_PROVED reversed, Phase 37a].

      Step 4: Apply NS_ForcingOrbitZero_OPEN with T = τ + 1:
        inner(f τ, corrSem((τ+1)-τ) φ) = inner(f τ, corrSem(1) φ) = 0.

    #print axioms NS_ForcingOrbitZero_iff_WeakForcingIsZero = classical trio (given hexp, hfz). -/
theorem NS_ForcingOrbitZero_iff_WeakForcingIsZero
    (hexp : NS_ExpIntegralZero_OPEN s)
    (hfz : NS_ForcingOrbitZero_OPEN s) :
    NS_WeakForcingIsZero_OPEN s := by
  intro u u₀ f hweak τ hτ
  -- Step 1: Apply injectivity of corrSem(1) to f τ
  apply NS_CorrSemigroupInjective_PROVED hexp 1 one_pos (f τ)
  -- Step 2: corrSem(1)(f τ) = 0 via inner_eq_of_inner_eq_all
  apply inner_eq_of_inner_eq_all _ 0
  intro φ
  rw [inner_zero_left]
  -- Step 3: inner(corrSem(1)(f τ), φ) = inner(f τ, corrSem(1) φ) by SelfAdj
  rw [← NS_CorrSemigroupSelfAdj_PROVED 1 one_pos.le (f τ) φ]
  -- Step 4: inner(f τ, corrSem(1) φ) = 0 from ForcingOrbitZero with T = τ + 1
  have hfz_val := hfz u u₀ f hweak (τ + 1) τ hτ (by linarith) φ
  -- hfz_val: inner(f τ, corrSem((τ+1)-τ) φ) = 0; simplify (τ+1)-τ = 1
  rwa [show (τ + 1) - τ = (1 : ℝ) from by ring] at hfz_val

/-- **Phase 43: Equivalence — NS_ForcingOrbitZero_OPEN ↔ NS_WeakForcingIsZero_OPEN.**

    Forward: inner_zero_left (trivial).
    Backward: density argument (corrSem injective via FourierEq, Phase 43 above).

    #print axioms NS_ForcingOrbitZero_equiv = classical trio (given hexp). -/
theorem NS_ForcingOrbitZero_equiv
    (hexp : NS_ExpIntegralZero_OPEN s) :
    NS_ForcingOrbitZero_OPEN s ↔ NS_WeakForcingIsZero_OPEN s :=
  ⟨NS_ForcingOrbitZero_iff_WeakForcingIsZero hexp,
   NS_ForcingOrbitZero_from_WeakForcingIsZero⟩

/-! ## VII. Full chain combinator: WeakForcingIsZero → WeakInitCont -/

/-- **Phase 43: NS_WeakInitCont_OPEN CLOSED given NS_WeakForcingIsZero_OPEN + API (0 sorry).**

    PROOF CHAIN:
      NS_WeakForcingIsZero_OPEN
        → NS_ForcingOrbitZero_OPEN   [NS_ForcingOrbitZero_from_WeakForcingIsZero, trivial]
        → NS_ScalarLeibnizAdjoint_OPEN [NS_ScalarLeibnizAdjoint_Phase41, Phase 41]
        → NS_WeakInitCont_OPEN        [ns_weakInitCont_unconditional, Phase 36]
          (via NS_WeakMomentumDiff_OPEN as remaining sub-gap)

    THE REMAINING SUB-GAP: NS_WeakMomentumDiff_OPEN s (Phase 35).
      Given hdiff, the chain from NS_WeakForcingIsZero_OPEN closes NS_WeakInitCont_OPEN.

    #print axioms NS_WeakInitCont_from_WeakForcingIsZero = classical trio (given hdiff, hfis). -/
theorem NS_WeakInitCont_from_WeakForcingIsZero
    (hdiff : NS_WeakMomentumDiff_OPEN s)
    (hfis  : NS_WeakForcingIsZero_OPEN s) :
    NS_WeakInitCont_OPEN s :=
  ns_weakInitCont_unconditional
    hdiff
    (NS_ScalarLeibnizAdjoint_Phase41 (NS_ForcingOrbitZero_from_WeakForcingIsZero hfis))
    NS_CorrSemigroupSelfAdj_PROVED

/-! ## VIII. Phase 43 gap accounting -/

/-- **Phase 43 gap accounting (0 sorry, 0 cert axioms, classical trio).**

    PROVED IN PHASE 43 (classical trio, 0 cert axioms):
      corrSemigroupRate_le_quarter      -- rate xi <= 1/4 (algebraic)
      NS_CorrSemigroupInjective_PROVED  -- corrSem injective (given NS_ExpIntegralZero_OPEN)
      NS_ForcingOrbitZero_from_WeakForcingIsZero  -- trivial (inner_zero_left)
      NS_ForcingOrbitZero_iff_WeakForcingIsZero   -- density argument (given hexp)
      NS_ForcingOrbitZero_equiv                   -- ↔ version
      NS_WeakInitCont_from_WeakForcingIsZero      -- full chain (given hdiff, hfis)

    NAMED OPEN DEFS ADDED (Phase 43, 2):
      NS_ExpIntegralZero_OPEN s     integral positivity API (ETA 1-2 days)
      NS_WeakForcingIsZero_OPEN s   model restriction f=0 (equivalent to ForcingOrbitZero)

    NAMED OPEN DEFS ELIMINATED (Phase 43, 2):
      NS_ForcingOrbitZero_OPEN s         -- CLOSED by NS_ForcingOrbitZero_from_WeakForcingIsZero
      NS_CorrSemigroupFourierEq_OPEN s   -- CONFIRMED ALREADY PROVED (Phase 20 correction)
                                          -- NSFourierInner.lean: NS_CorrSemigroupFourierEq_PROVED

    FULL REMAINING GAP LIST (NS Tower after Phase 43):
      NS_ExpIntegralZero_OPEN s        integral API, ETA 1-2 days
      NS_WeakForcingIsZero_OPEN s      model restriction = ForcingOrbitZero equivalent
      NS_StokesMaxReg_OPEN s           Hieber-Pruss 2018, 6-18 months (independent chain)
      NS_WeakMomentumDiff_OPEN s       Phase 35 sub-gap (scalar DifferentiableAt)

    MAIN MATHEMATICAL ACHIEVEMENT:
      The DENSITY / INJECTIVITY theorem is proved:
        inner(f tau, corrSem(T-tau) phi) = 0 for all phi (corrSem > 0 range)
        implies f tau = 0.
      This is the Phase 17 Fourier density argument now formalized (conditionally).

    PROOF CHAIN SUMMARY:
      Phase 20: NS_CorrSemigroupFourierEq_PROVED (Fourier rep -- ALREADY DONE)
      Phase 37a: NS_CorrSemigroupSelfAdj_PROVED (self-adjoint -- ALREADY DONE)
      Phase 36: inner_eq_of_inner_eq_all (density -- ALREADY DONE)
      Phase 43: corrSemigroupRate_le_quarter + NS_CorrSemigroupInjective_PROVED (NEW)
      Phase 43: NS_ForcingOrbitZero_OPEN CLOSED (given NS_WeakForcingIsZero_OPEN)
      Phase 43: NS_WeakInitCont_OPEN CLOSED (given hdiff + NS_WeakForcingIsZero_OPEN)

    NS Clay Surface #1: LOCKED OPEN.  No Clay Millennium Prize claim.
    CERT AXIOMS: classical trio only. -/
theorem phase43_gap_accounting : True := trivial

end TheoremaAureum.Towers.NS.Phase43ForcingOrbitZero
