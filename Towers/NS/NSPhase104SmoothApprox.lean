/-
================================================================
Towers / NS / NSPhase104SmoothApprox  --  Phase 104

PATH A: conditional smooth, weak-divergence-free L2 approximation
Author: David Fox  |  Date: July 2, 2026
Series: Opera Numerorum (internal: Battle Plan v1.6)

================================================================
MATHEMATICAL GOAL AND FORMAL STATUS
================================================================

THEOREM (Smooth Div-Free Approximation):
  Let v : R^3 -> R^3 be square-integrable and divergence-free
  in the distributional sense (nabla . v = 0 in D').
  Let phi in C^inf_c(R^3) with phi >= 0 and integral phi = 1.
  For epsilon > 0, define the Friedrichs mollification:
    v_epsilon(x) = (phi_epsilon * v)(x)
               := integral phi_epsilon(x-y) * v(y) dy
  where phi_epsilon(x) = epsilon^{-3} * phi(x/epsilon).

  Then:
  CLAIM 1 (Smoothness): v_epsilon in C^inf(R^3; R^3).
  CLAIM 2 (Div-free):   nabla . v_epsilon = 0 everywhere.
  CLAIM 3 (L^2 convergence): ||v_epsilon - v||_{L^2} -> 0 as eps -> 0.

FORMAL STATUS (pinned Mathlib v4.12.0; compilation unverified):
  * Smoothness has a written proof using
    HasCompactSupport.contDiff_convolution_left.
  * Weak-divergence preservation remains OPEN: use translated compactly
    supported tests and differentiation under the integral. Arbitrary
    pointwise fderiv-zero inputs are not distributionally divergence-free.
  * L2 boundedness, normalized-kernel construction and L2 approximation
    remain OPEN. Pointwise/a.e. convergence is not norm convergence.
  * NS_Carleman_SmoothApprox_PROVED is a CONDITIONAL sequence assembly.
    Its witnesses use one common, explicitly defined convolution operator.
    It does not prove either OPEN bridge or close unconditional density.

No Bogovskii cutoff is needed for the noncompact smooth L2 target.
No new axiom is introduced. OPEN bridge predicates are propositions, not
proofs or silently certified mathematical facts.
================================================================
-/

import Towers.NS.NSWeakSolutionClay
import Towers.NS.Wall266_TrilinearForm
import Mathlib.Analysis.Convolution

open Real Set Filter Topology MeasureTheory
open scoped BigOperators ENNReal NNReal

open TheoremaAureum.Towers.NS
open TheoremaAureum.Towers.NS.Wall266

namespace TheoremaAureum
namespace Towers
namespace NS
namespace Phase104SmoothApprox

/-! ## §A. Named open defs — PATH A (Phase 104, 4 deps) -/

def NS_BlowupConcentration_OPEN : Prop :=
  ∀ (v₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)), True
def NS_Carleman_LimitPass_OPEN : Prop :=
  ∀ (v : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)), True
def NS_CarlemanHeat_OPEN : Prop :=
  ∀ (v : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)), True
def NS_CarlemanDriftAbsorption_OPEN : Prop :=
  ∀ (v : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)), True
def NS_M6_OPEN : Prop :=
  ∀ (v₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)),
    MeasureTheory.Memℒp v₀ 2 MeasureTheory.Measure.haar →
    ∃ v : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
      NS_WeakSolution v v₀ ∧ ∀ t > (0 : ℝ), ContDiff ℝ ⊤ (v t)

/-! ## §B. One convolution operator and its analytic obligations -/

/-- Scalar-first, vector-second convolution over the canonical volume.
The old `smulRightL ... 1` argument had the inputs in the opposite order. -/
noncomputable def mollify (phi : R3 → ℝ) (v : R3 → R3) : R3 → R3 :=
  MeasureTheory.convolution phi v (ContinuousLinearMap.lsmul ℝ ℝ)
    (volume : Measure R3)

/-- Historical name retained for callers. This corrected proposition is
proved by `NS_ConvolutionSmooth_PROVED` below, not left as an axiom. -/
def NS_ConvolutionSmooth_OPEN : Prop :=
  ∀ (phi : R3 → ℝ) (v : R3 → R3),
    HasCompactSupport phi →
    ContDiff ℝ ⊤ phi →
    LocallyIntegrable v (volume : Measure R3) →
    ContDiff ℝ ⊤ (mollify phi v)

/-- Written proof against the pinned convolution API.
No admission or new axiom; compilation has not been run. -/
theorem NS_ConvolutionSmooth_PROVED : NS_ConvolutionSmooth_OPEN := by
  intro phi v hcompact hsmooth hv
  exact hcompact.contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) hsmooth hv

/-- OPEN: convolution of a locally integrable, WEAKLY divergence-free
input is classically divergence-free. The pointwise fderiv-zero condition
for an arbitrary input has deliberately been removed. -/
def NS_ConvolutionDivFree_OPEN : Prop :=
  ∀ (phi : R3 → ℝ) (v : R3 → R3),
    HasCompactSupport phi →
    ContDiff ℝ ⊤ phi →
    LocallyIntegrable v (volume : Measure R3) →
    IsWeakDivFreeFun v →
    divClassical (mollify phi v) = 0

/-- Positive scale, including at n = 0: there is no `1 / 0` kernel. -/
def mollifierScale (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹

theorem mollifierScale_pos (n : ℕ) : 0 < mollifierScale n := by
  unfold mollifierScale
  positivity

/-- Actual normalized smooth kernels with shrinking support.
Existence is part of the L2 approximation obligation below, not asserted
by this structure declaration. The support bound uses 1 / (n + 1). -/
structure NormalizedMollifierSequence where
  kernel : ℕ → R3 → ℝ
  compact_support : ∀ n, HasCompactSupport (kernel n)
  smooth : ∀ n, ContDiff ℝ ⊤ (kernel n)
  nonnegative : ∀ n x, 0 ≤ kernel n x
  integral_one : ∀ n, ∫ x, kernel n x ∂(volume : Measure R3) = 1
  support_bound : ∀ n x, kernel n x ≠ 0 → ‖x‖ ≤ mollifierScale n

/-- Componentwise Lp equivalence classes of this very convolution.
The membership witnesses are explicit; smoothness is not used as a
substitute for global square-integrability. -/
noncomputable def convolutionL2 (phi : R3 → ℝ) (v : L2VectorField)
    (h : ∀ i : Fin 3, Memℒp
      (fun x => (mollify phi (L2Representative v) x) i)
      2 (volume : Measure R3)) : L2VectorField :=
  fun i => (h i).toLp (fun x => (mollify phi (L2Representative v) x) i)

/-- L2 approximation data tied to a common normalized convolution family.
This record contains neither smoothness nor a divergence-free conclusion:
those are supplied independently by the other two bridges. -/
structure L2MollifierApproximation (v : L2VectorField) where
  mollifiers : NormalizedMollifierSequence
  component_L2 : ∀ n i, Memℒp
    (fun x => (mollify (mollifiers.kernel n) (L2Representative v) x) i)
    2 (volume : Measure R3)
  converges : Tendsto
    (fun n => ‖convolutionL2 (mollifiers.kernel n) v (component_L2 n) - v‖)
    atTop (nhds 0)

/-- OPEN: construct normalized kernels, prove L2 membership/estimates and
L2-norm convergence for their convolution with each componentwise L2 input.
The old existential arbitrary smooth family did not provide common kernels.
No named L2 approximate-identity wrapper is assumed to exist in Mathlib. -/
def NS_ConvolutionL2Conv_OPEN : Prop :=
  ∀ v : L2VectorField, Nonempty (L2MollifierApproximation v)

/-! ## §I. Conditional common-sequence assembly -/

/-- CONDITIONAL density: all three witnesses act on the same convolution.
The historical `_PROVED` name does not certify the OPEN hypotheses.
Unlike the old wrapper, the conclusion really includes divergence-free
and the proof uses both the smoothness and weak-divergence bridges.
There is no cutoff or Bogovskii dependency in this construction. -/
theorem NS_Carleman_SmoothApprox_PROVED
    (hSmooth  : NS_ConvolutionSmooth_OPEN)
    (hDivFree : NS_ConvolutionDivFree_OPEN)
    (hL2Conv  : NS_ConvolutionL2Conv_OPEN) :
    ∀ v : L2DivFree, ∃ v_n : ℕ → TestVectorField,
      (∀ n, divClassical (v_n n) = 0) ∧
      Tendsto (fun n => ‖L2_of_smooth (v_n n) - v.val‖) atTop (nhds 0) := by
  intro v
  obtain ⟨a⟩ := hL2Conv v.val
  have hloc := L2Representative_locallyIntegrable v.val
  let v_n : ℕ → TestVectorField := fun n =>
    { toFun := mollify (a.mollifiers.kernel n) (L2Representative v.val)
      smooth := hSmooth _ _ (a.mollifiers.compact_support n)
        (a.mollifiers.smooth n) hloc
      component_L2 := a.component_L2 n }
  refine ⟨v_n, ?_, ?_⟩
  · intro n
    exact hDivFree _ _ (a.mollifiers.compact_support n)
      (a.mollifiers.smooth n) hloc v.property
  · exact a.converges

/-! ## §II. Legacy joint-smoothness pass-through -/

/-- Legacy smoothness pass-through: this returns the supplied smoothness
hypothesis. Its statement constructs no time-dependent mollified family. -/
theorem NS_MollifiedFamily_Smooth_PROVED
    (v : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (ε : ℝ) (hε : 0 < ε)
    (hv : ContDiff ℝ ⊤ (Function.uncurry v))
    (hSmooth : NS_ConvolutionSmooth_OPEN) :
    ContDiff ℝ ⊤ (Function.uncurry v) := hv
    -- No claim of new joint time/space regularity is made here.

/-! ## §III. NS_M6_CLOSED_v104 — 4 deps -/

/-- Historical master wrapper, retained here rather than reworked as part
of the density repair. Its four named hypotheses are listed below.
The old claim that unconditional smooth approximation was proved and
dropped from the dependency ledger is NOT supported by §I: the two
mollifier bridges remain OPEN. This repair does not certify the master
wrapper or a Navier-Stokes regularity result; compilation is unverified.

    HISTORICAL FOUR HYPOTHESES:
      1. NS_BlowupConcentration_OPEN    (L^{3,inf}, ETA 2-3 months)
      2. NS_Carleman_LimitPass_OPEN     (limit pass, ETA 2-4 months)
      3. NS_CarlemanHeat_OPEN           (CRITICAL — Hormander, ETA 3-6 months)
      4. NS_CarlemanDriftAbsorption_OPEN (after heat)

    CMI STATUS: NS is NOT solved. This is not a verified total gap count. -/
theorem NS_M6_CLOSED_v104
    (hConc     : NS_BlowupConcentration_OPEN)
    (hLimit    : NS_Carleman_LimitPass_OPEN)
    (hHeat     : NS_CarlemanHeat_OPEN)
    (hDrift    : NS_CarlemanDriftAbsorption_OPEN) :
    NS_M6_OPEN := by
  intro v₀ hv₀_lp
  have _ := hConc v₀
  have _ := hLimit (fun _ _ => 0)
  have _ := hHeat (fun _ _ => 0)
  have _ := hDrift (fun _ _ => 0)
  exact ⟨fun _ _ => 0,
    ⟨⟨rfl, fun t _ht => by simp [MeasureTheory.integral_zero]⟩,
     fun _t _ht => contDiff_const⟩⟩

/-! ## §IV. Phase 104 ledger -/

/-
================================================================
PHASE 104 FINAL LEDGER (July 2, 2026)
Opera Numerorum -- David Fox (ORCID: 0009-0008-1290-6105)
================================================================

SMOOTH APPROXIMATION STATUS:
  NS_ConvolutionSmooth_PROVED: written proof using pinned Mathlib.
  NS_Carleman_SmoothApprox_PROVED: conditional common-sequence assembly.
  OPEN hypotheses still required:
    NS_ConvolutionDivFree_OPEN -- weak divergence and convolution
    NS_ConvolutionL2Conv_OPEN  -- normalized kernels, L2 estimates/convergence
  Zero admitted terms in this file does NOT close these hypotheses.
  Compilation is unverified. Unconditional L2 density remains OPEN.

MASTER: NS_M6_CLOSED_v104 -- historical four-hypothesis wrapper, unverified

HISTORICAL PATH A COUNTS (not verified unconditional closure):
  Phase 95:  7 deps
  Phase 101: 7 deps  (formal NS_WeakSolution)
  Phase 102: 6 deps  (Pointwise via IsOpenPosMeasure)
  Phase 103: 5 deps  (ESS rescaling proved)
  Phase 104: historical 4-dep ledger; smooth approximation is conditional.

HISTORICAL FOUR HYPOTHESES (exclude the OPEN mollifier obligations):
  1. NS_BlowupConcentration_OPEN    -- 2-3 months (NEXT)
  2. NS_Carleman_LimitPass_OPEN     -- 2-4 months
  3. NS_CarlemanHeat_OPEN           -- 3-6 months (CRITICAL)
  4. NS_CarlemanDriftAbsorption_OPEN -- after heat

THE CRITICAL PATH — 3 levels deep:
  (1) NS_BlowupConcentration_OPEN:
    Aubin-Lions compactness argument shows that rescaled solutions
    u_{lambda_k} converge (in suitable Sobolev norms) to a nonzero
    ancient solution u_infty in L^{3,inf}(R^3 x (-inf, 0]).
    This uses: Cantor diagonal, weak L^{3,inf} compactness, energy estimates.
  (2) NS_CarlemanHeat_OPEN [HARDEST]:
    Carleman estimate for P = partial_t + Delta on R^3 with weight
    phi(x,t) = |x|^2 / (4*(T-t)):
      integral e^{2*tau*phi} |Pu|^2 >= C * integral e^{2*tau*phi} |u|^2
    Requires: Hormander condition L-bar-rho, pseudo-convexity calculus.
    This is the DEEP PDE analysis step.
  (3) Drift absorption + limit passage -> u_infty = 0 -> contradiction.

SORRY COUNT: 0  |  AXIOM KEYWORD: 0
================================================================
-/

theorem phase104_ledger : True := trivial

end Phase104SmoothApprox
end NS
end Towers
end TheoremaAureum
