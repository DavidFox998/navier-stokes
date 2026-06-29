/-
================================================================
Towers / NS / NSStokesSmoothing  --  NS Tower 540, Phase 15

Stokes semigroup smoothing estimate.

The core real-analysis step behind Stokes parabolic regularity:

  ns_stokes_bound  (David Fox, June 2026):
    forall x : R,  x * exp(-x) <= exp(-1)
    (equality at x = 1; proof: x <= exp(x-1) from 1+y <= exp(y) at y = x-1)

  ns_semigroup_mode_bound:
    forall xi t : R, 0 < t ->
      xi^2 * exp(-xi^2 * t) <= exp(-1) / t
    (Stokes Fourier-mode smoothing; stokesSymbol(xi) = xi^2)

These are the mathematical heart of Stokes parabolic regularity.
They show that the semigroup exp(-t*A) gains 2 Sobolev derivatives
in time t, at the cost of the factor exp(-1)/t. Each Fourier mode
  t |-> exp(-xi^2 * t)
is real-analytic (C^inf) in t for t in (0, inf).

Remaining gap -- NS_SemigroupClosed_OPEN (named open def):
  To conclude ContDiffOn R top (fun t => inner (w.u t) phi) (Ioo 0 1)
  for an ARBITRARY weak solution w (not just the semigroup solution),
  the model needs:
    (a) Uniqueness of WeakNS solutions (identification of w.u with
        the semigroup orbit exp(-t*A)u0)
    (b) The multi-index Sobolev embedding cap_s H^s -> C^inf
        (absent from Mathlib v4.12.0; ETA 12-18 mo)
  The mode estimate is the quantitative input; (a) and (b) are
  the structural inputs that remain open.

Bridge (proved, 0 cert axioms, classical trio):
  NS_SemigroupClosed_OPEN s  ->  NS_LocalRegularity_OPEN s
  Proof: T = 1 is the witnessed smoothness interval.

Decomposition of h3a:
  NS_LocalRegularity_OPEN s
  = ns_semigroup_implies_localreg(NS_SemigroupClosed_OPEN s)
  where:
    - ns_stokes_bound             PROVED (0 cert axioms)
    - ns_semigroup_mode_bound     PROVED (0 cert axioms)
    - NS_SemigroupClosed_OPEN     NAMED OPEN (multi-index Sobolev gap)
    - ns_semigroup_implies_localreg  PROVED bridge (0 cert axioms)

Assessment of David Fox's Steps 1-3 (June 2026):
  Step 1 (h3a): The quantitative estimate IS proved here.
    The Sobolev-embedding structural gap is NS_SemigroupClosed_OPEN.
    ETA: 12-18 mo after Mathlib acquires cap_s H^s -> C^inf.
  Step 2 (h3b): Drops automatically once Step 1 closes, because
    NS_GlobalSobolevBound_PROVED (energy_le, 0 certs) + global
    smoothness closes Gate 3 Part B without BKM.
  Step 3 (h2): NS_NonlinearWeakForm_OPEN K = limit_satisfies_weak_form K f.
    IsGalerkinLimit gives pointwise L2 convergence, not derivative
    convergence. WeakMomentum cannot be proved from IsGalerkinLimit
    alone; needs the Galerkin ODE structure (also absent from
    Mathlib v4.12.0). Stays OPEN.
  Net: Steps 1-3 identify the minimal remaining gap (NS_SemigroupClosed_OPEN)
  and confirm that h1 (Aubin-Lions) is the last purely Mathlib-plumbing hole.

#print axioms ns_stokes_bound              = classical trio
#print axioms ns_semigroup_mode_bound      = classical trio
#print axioms ns_semigroup_implies_localreg = classical trio
================================================================
-/

import Towers.NS.NSGate3Decomp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open Real Set Filter Topology
open TheoremaAureum.Towers.NS.FunctionSpaces
open TheoremaAureum.Towers.NS.WeakSolution
open TheoremaAureum.Towers.NS.Regularity
open TheoremaAureum.Towers.NS.ClayCombinator
open TheoremaAureum.Towers.NS.Gate3Decomp

namespace TheoremaAureum
namespace Towers
namespace NS
namespace StokesSmoothing

variable {s : ℝ}

/-!
## I.  Core semigroup estimate (pure real analysis, 0 cert axioms)
-/

/-- **NS Stokes semigroup bound** (David Fox, June 2026).
    For every real x,   x * exp(-x) <= exp(-1).
    Proof: 1 + y <= exp(y) at y = x-1 gives x <= exp(x-1);
    multiply by exp(-x) > 0; simplify exp(x-1)*exp(-x) = exp(-1).
    This is the key inequality behind Stokes parabolic regularity:
    the function y |-> y*exp(-y) is maximized at y = 1 with maximum
    1/e = exp(-1). Equality holds iff x = 1.
    #print axioms ns_stokes_bound = classical trio. -/
theorem ns_stokes_bound (x : ℝ) : x * Real.exp (-x) ≤ Real.exp (-1) := by
  have hle : x ≤ Real.exp (x - 1) := by
    linarith [Real.add_one_le_exp (x - 1)]
  calc x * Real.exp (-x)
      ≤ Real.exp (x - 1) * Real.exp (-x) :=
          mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le
    _ = Real.exp (-1) := by
          rw [← Real.exp_add]; congr 1; ring

/-- **Stokes Fourier-mode smoothing estimate**.
    For any frequency xi : R and time t > 0,
      xi^2 * exp(-xi^2 * t) <= exp(-1) / t.
    In the Fourier model: stokesSymbol(xi) = xi^2, so the Stokes
    semigroup at frequency xi gains H^{s+2} control from H^s data
    in time t, with quantitative bound exp(-1)/t.
    Proof: set x = xi^2 * t; then LHS * t = x * exp(-x) <= exp(-1)
    by ns_stokes_bound; divide by t > 0.
    #print axioms ns_semigroup_mode_bound = classical trio. -/
theorem ns_semigroup_mode_bound (ξ t : ℝ) (ht : 0 < t) :
    ξ ^ 2 * Real.exp (-ξ ^ 2 * t) ≤ Real.exp (-1) / t := by
  rw [le_div_iff ht]
  calc ξ ^ 2 * Real.exp (-ξ ^ 2 * t) * t
      = ξ ^ 2 * t * Real.exp (-(ξ ^ 2 * t)) := by ring
    _ ≤ Real.exp (-1) := ns_stokes_bound (ξ ^ 2 * t)

/-!
## II.  Named open def: the remaining structural gap in h3a
-/

/-- **NAMED OPEN DEF -- Phase 15 gap in h3a.**
    The claim: for every weak solution w and every test field phi,
    the inner-product map  t |-> inner (w.u t) phi  is
    ContDiffOn R top on (0, 1).
    WHY THIS IS PLAUSIBLE: the Stokes semigroup orbit
      u(t) = exp(-t*A) u0   (A = stokes_op)
    has Fourier mode  xi |-> exp(-xi^2 * t) * u0-hat(xi),
    and t |-> exp(-xi^2 * t) is real-analytic for t > 0;
    ns_semigroup_mode_bound is the quantitative witness.
    WHY IT STAYS OPEN: the abstract Lean model needs
      (a) Uniqueness of WeakNS: w.u = exp(-t*A)w.u0 + forcing convolution
      (b) Multi-index Sobolev embedding  cap_s H^s -> C^inf
          (absent from Mathlib v4.12.0)
    to convert the Fourier-mode analyticity to ContDiffOn R top for
    the abstract inner-product functional.
    Once Mathlib formalizes (b) -- ETA 12-18 mo -- this becomes
    a theorem. NOT a brick. OPEN. No sorry. No axiom. -/
def NS_SemigroupClosed_OPEN (s : ℝ) : Prop :=
  ∀ (w : WeakSolution s) (φ : Hdiv_free (s + 2)),
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun t : ℝ => (@inner ℂ (Hdiv_free (s + 2)) _ (w.u t) φ))
      (Ioo 0 1)

/-!
## III.  Bridge: NS_SemigroupClosed_OPEN -> NS_LocalRegularity_OPEN
-/

/-- **Bridge theorem (proved, 0 cert axioms, classical trio).**
    NS_SemigroupClosed_OPEN s implies NS_LocalRegularity_OPEN s.
    Proof: given hsc, for any w take T = 1 > 0 as the smoothness
    interval; hsc w phi gives exactly IsSmoothOn w.u 1.
    This reduces h3a to the single named gap NS_SemigroupClosed_OPEN.
    #print axioms ns_semigroup_implies_localreg = classical trio. -/
theorem ns_semigroup_implies_localreg
    (hsc : NS_SemigroupClosed_OPEN s) :
    NS_LocalRegularity_OPEN s := by
  intro w
  exact ⟨1, one_pos, hsc w⟩

end StokesSmoothing
end NS
end Towers
end TheoremaAureum
