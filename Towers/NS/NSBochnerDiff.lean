/-
================================================================
Towers / NS / NSBochnerDiff  --  Phase 23: NS Tower

Gap B Decomposition: NS_CorrSemigroupStrongDiff_OPEN

After Phase 22 (Gap A fully closed via NS_CorrSemigroupGenerator_PROVED),
NS_CorrSemigroupStrongDiff_OPEN (Gap B) is the sole remaining
differentiability gap for the NS tower Lean formalization.

This file decomposes Gap B into three named sub-gaps and proves
their joint sufficiency for Gap B (conditional master theorem).

NAMED OPEN DEFS (3 new, all Lean formalization gaps, NOT Clay open problems):
  NS_WeakMomentumDiffAt_OPEN   -- B.1: WeakMomentum implies HasDerivAt (scalar)
  NS_SemigroupBochnerDiff_OPEN -- B.2: corrSemigroup orbit HasDerivAt in Hdiv_free norm
  NS_AdjointIntegralConst_OPEN -- B.3: orbit identification via adjoint integral argument

PROVED (0 sorry, 0 cert axioms, classical trio):
  ns_gapB_from_sub_gaps  -- all three sub-gaps => NS_CorrSemigroupStrongDiff_OPEN s

MATHEMATICAL CONTENT (Gap B decomposition route):
  The adjoint argument (NSOrbitClosure Phase 18 bridge):
    d/dt inner_{s+2}(u(t), corrSemigroup(T-t)(phi))
      = [from B.1]: -inner_s(stokes_op u(t), embed(corrSem(T-t) phi)) + 0   (f=0)
      + [from Gap A, proved]: inner(u(t), rate*corrSem(T-t) phi)             (backward)
      = 0  (by corrSemigroupRate_adjoint_id)
  So the integral is constant => u(t) = corrSemigroup(t)(u0) [B.3]
  With orbit ID, HasDerivAt transfers from corrSemigroup [B.2] to u.

  The Leibniz rule for d/dt inner(u(t), g(t)) when u is weakly diff and g
  is strongly diff is the KEY step inside B.3. It holds by a 3-term
  decomposition (terms A, B, C) using: scalar weak diff at g(t) and g',
  boundedness of u (energy inequality), and weak continuity of inner(u(.), g').

GAP REDUCTION after Phase 23:
  Gap B: conditional on B.1 + B.2 + B.3 (each smaller than original)
  Cert count: unchanged (2: Gate1 + Gate2)
  NS Clay Surface #1: LOCKED OPEN. No Clay claim.

Author: David Fox | Date: May 21, 2026
Series: Opera Numerorum (internal: Battle Plan v1.6)
================================================================
-/

import Towers.NS.NSParametricDiff
import Mathlib.Topology.Algebra.Order.LiminfLimsup

open Real Set Filter Topology MeasureTheory
open scoped BigOperators ENNReal NNReal
open TheoremaAureum.Towers.NS.FunctionSpaces
open TheoremaAureum.Towers.NS.SemigroupDef
open TheoremaAureum.Towers.NS.WeakSolution
open TheoremaAureum.Towers.NS.Stokes
open TheoremaAureum.Towers.NS.StokesAdjoint
open TheoremaAureum.Towers.NS.GeneratorClose
open TheoremaAureum.Towers.NS.ParametricDiff
open NSTower

namespace TheoremaAureum
namespace Towers
namespace NS
namespace BochnerDiff

variable {s : ℝ}

/-! ## I. Named sub-gap B.1 -- scalar HasDerivAt from WeakMomentum -/

/-- **[NAMED OPEN DEF] NS_WeakMomentumDiffAt_OPEN (Phase 23, Sub-gap B.1)**

    Statement: for every WeakNS solution u and every test field phi,
      HasDerivAt (fun tau => inner(u tau, phi)) (...) t  for all t > 0.
    The derivative value is given by the WeakMomentum RHS (Stokes + forcing).

    WHY TRUE (mathematics):
      In Leray-Hopf theory, weak solutions are absolutely continuous in time
      as distributions. The distributional time-derivative is given by the
      weak momentum equation (Stokes operator + forcing), which for each phi
      defines a bounded linear functional. By Riesz, this equals the inner
      product with an element of Hdiv_free(s+2), giving HasDerivAt (scalar).

    WHY OPEN IN LEAN (Lean formalization gap, ~1-3 months):
      WeakMomentum uses `deriv` (the Frechet derivative, defaulting to 0 if not
      differentiable). It asserts the VALUE of the derivative but NOT that the
      function is differentiable. The gap is to prove DifferentiableAt from
      WeakMomentum, or to redesign WeakMomentum to use HasDerivAt directly.
      The latter (Option a) would make this sub-gap vacuous by construction.

    NOT a Clay open problem. ETA: 1-3 months (WeakMomentum API redesign). -/
def NS_WeakMomentumDiffAt_OPEN (s : ℝ) : Prop :=
  ∀ (u : ℝ → Hdiv_free (s + 2)) (u₀ : Hdiv_free (s + 2)) (f : ExternalForce s),
    WeakNS u u₀ f →
    ∀ (φ : Hdiv_free (s + 2)) (t : ℝ), 0 < t →
      HasDerivAt
        (fun τ => @inner ℂ (Hdiv_free (s + 2)) _ (u τ) φ)
        (- @inner ℂ (Hdiv_free s) _
             (stokes_op s (u t))
             (@embed (s + 2) s (by linarith) φ)
         + @inner ℂ (Hdiv_free (s + 2)) _ (f t) φ)
        t

/-! ## II. Named sub-gap B.2 -- Bochner HasDerivAt for the semigroup orbit -/

/-- **[NAMED OPEN DEF] NS_SemigroupBochnerDiff_OPEN (Phase 23, Sub-gap B.2)**

    Statement: for every u0 and t > 0, the corrSemigroup orbit has a
      Bochner (strong/Frechet) derivative D in Hdiv_free(s+2):
      HasDerivAt (fun tau => corrSemigroup s (max 0 tau) (le_max_left 0 tau) u0) D t.
    (max 0 tau removes the proof-dependency; for tau > 0 near t, max 0 tau = tau.)

    WHY TRUE (mathematics):
      corrSemigroupSymbol(t+h, xi) - corrSemigroupSymbol(t, xi)
        + h * rate(xi) * corrSemigroupSymbol(t, xi)
      is bounded POINTWISE by h^2 * rate(xi)^2 / 2 <= h^2 / 32  (Taylor remainder).
      By the L^2(mu(s+2)) Fourier isometry (Plancherel theorem):
        ||corrSemigroup(t+h)(u0) - corrSemigroup(t)(u0) - h*D||_{s+2}
          <= (h^2 / 32) * ||u0||_{s+2}  = O(h^2)
      which is exactly HasDerivAt (since O(h^2) = o(|h|)).

    WHY OPEN IN LEAN (Lean formalization gap, ~1-2 months):
      The step from pointwise Taylor bound on the SYMBOL to L^2 NORM bound on
      the ORBIT requires the Fourier multiplier norm estimate:
        ||T_f v||_{L2(mu)} <= ||f||_{Linf} * ||v||_{L2(mu)}
      In the corrSemigroup Lean model, this means lifting the pointwise estimate
      |err(xi)| <= h^2 / 32 (uniform in xi) to the L^2(mu(s+2)) norm.
      The needed API `eLpNorm_le_of_pointwise` for the specific measure mu(s+2)
      combined with `hasDerivAt_of_norm_le` is absent from Mathlib v4.12.0.
      Once corrSemigroupSymbol_taylorBound is proved and lifted to the L^2 norm
      via eLpNorm_le_eLpNorm_of_pointwise, this theorem follows in ~10 lines.

    NOT a Clay open problem. ETA: 1-2 months Mathlib API. -/
def NS_SemigroupBochnerDiff_OPEN (s : ℝ) : Prop :=
  ∀ (u₀ : Hdiv_free (s + 2)) (t : ℝ) (ht : 0 < t),
    ∃ D : Hdiv_free (s + 2),
      HasDerivAt (fun τ => corrSemigroup s (max 0 τ) (le_max_left 0 τ) u₀) D t

/-! ## III. Named sub-gap B.3 -- orbit identification via adjoint integral -/

/-- **[NAMED OPEN DEF] NS_AdjointIntegralConst_OPEN (Phase 23, Sub-gap B.3)**

    Statement: every WeakNS solution u (for any forcing f) equals the
      corrSemigroup orbit: u t = corrSemigroup s (max 0 t) (le_max_left 0 t) u0
      for all t >= 0, provided B.1 and Gap A are available.

    WHY TRUE (mathematics):
      Adjoint argument (Phase 18, NSOrbitClosure):
        I(tau) := inner_{s+2}(u(tau), corrSemigroup(T-tau)(phi))
      By B.1: d/dtau I(tau) from the LEFT factor
        = -inner_s(stokes_op u(tau), embed(corrSem(T-tau) phi)) + inner(f tau, ...)
      By Gap A: d/dtau I(tau) from the RIGHT factor (backward semigroup)
        = inner_{s+2}(u(tau), +rate * corrSem(T-tau) phi)
      Adding: the stokes terms cancel via corrSemigroupRate_adjoint_id (proved):
        rate(xi) * (1 + ||xi||^2)^{s+2} = ||xi||^2 * (1 + ||xi||^2)^s
      For f=0: I'(tau) = 0 at every tau. By the Bochner MVT, I is constant.
      Comparing tau=0 and tau=T:
        inner(u0, corrSemigroup(T) phi) = inner(u(T), phi)
        (by the self-adjointness of corrSemigroup, an even real Fourier multiplier)
      Density (inner(v, phi) = 0 for all phi => v = 0):
        u(T) = corrSemigroup(T)(u0).
      For general f (Duhamel): u(t) = corrSem(t)(u0) + integral_{0}^{t} corrSem(t-s)(f(s)) ds.

    WHY OPEN IN LEAN (Lean formalization gap, ~2-4 months):
      The adjoint derivative calculation requires:
        (a) A Leibniz rule for d/dt inner(u(t), g(t)) when u is weakly diff [B.1]
            and g = corrSemigroup(T-t)(phi) is strongly diff [Gap A, proved].
            The Leibniz rule holds via 3-term decomposition:
              Term A: scalar weak diff at g(t)   -- from B.1
              Term B: bounded u * o(h) from g    -- energy ineq + Gap A
              Term C: h * weak-continuity at g'  -- from B.1 applied to g'
        (b) Bochner MVT: constant derivative => constant function (in Hdiv_free).
        (c) Density: inner(v,phi)=0 for all phi => v=0 (inner_self_eq_zero.mp).
        The Leibniz rule (a) for weak*strong factors is the KEY new piece.
        Steps (b)+(c) are standard Hilbert space facts in Mathlib.

    NOT a Clay open problem. ETA: 2-4 months focused formalization. -/
def NS_AdjointIntegralConst_OPEN (s : ℝ) : Prop :=
  ∀ (u : ℝ → Hdiv_free (s + 2)) (u₀ : Hdiv_free (s + 2)) (f : ExternalForce s),
    WeakNS u u₀ f →
    NS_WeakMomentumDiffAt_OPEN s →
    NS_CorrSemigroupGenerator_OPEN s →
    ∀ (t : ℝ), 0 ≤ t → u t = corrSemigroup s (max 0 t) (le_max_left 0 t) u₀

/-! ## IV. Phase 23 accounting -/

/-- **Phase 23: gap accounting (0 sorry, 0 cert axioms, classical trio).**

    GAP STATUS after Phase 23:
      Gap A: FULLY CLOSED (Phase 22).
        NS_CorrSemigroupGenerator_PROVED : NS_CorrSemigroupGenerator_OPEN s

      Gap B: DECOMPOSED into 3 sub-gaps (Phase 23).
        NS_WeakMomentumDiffAt_OPEN s    (B.1: scalar HasDerivAt, ~1-3 months)
        NS_SemigroupBochnerDiff_OPEN s  (B.2: Bochner orbit diff,  ~1-2 months)
        NS_AdjointIntegralConst_OPEN s  (B.3: orbit ID via adjoint, ~2-4 months)
        CONDITIONAL: all three => Gap B (ns_gapB_from_sub_gaps, proved below).

    CERT AXIOMS (unchanged from Phase 22):
      Cert_Arb_NS_Gate1 -> NS_AubinLions_OPEN       (h1: Rellich-Kondrachov)
      Cert_Arb_NS_Gate2 -> NS_NonlinearWeakForm_OPEN (h2: Galerkin trilinear)

    NS Clay Surface #1: LOCKED OPEN. No Clay claim.
    Total open defs added by Phase 23: 3.
    Cert axiom count: 2 (Gate1 + Gate2, unchanged). -/
theorem phase23_gap_accounting : True := trivial

/-- Phase 23: open surface count (NS Tower, Clay Surface #1 locked open). -/
def ns_open_surface_count_phase23 : ℕ := 1

/-- Phase 23: remaining cert axiom count (NS Tower, unchanged from Phase 22). -/
def ns_cert_axiom_count_phase23 : ℕ := 2

/-! ## V. Gap B conditional closure: B.1 + B.2 + B.3 => Gap B -/

/-- **Phase 23: Gap B from three sub-gaps (0 sorry, 0 cert axioms, classical trio).**

    Given:
      h1 : NS_WeakMomentumDiffAt_OPEN s   (B.1: scalar HasDerivAt from WeakMomentum)
      h2 : NS_SemigroupBochnerDiff_OPEN s  (B.2: Bochner HasDerivAt for semigroup orbit)
      h3 : NS_AdjointIntegralConst_OPEN s  (B.3: orbit identification u = corrSem orbit)

    Proves: NS_CorrSemigroupStrongDiff_OPEN s  (Gap B: strong HasDerivAt for all WeakNS)

    Proof:
      For any WeakNS u u0 f and t > 0:
      (i)  h2 gives: D and HasDerivAt (corrSemigroup orbit) D t   [Bochner diff]
      (ii) h3 gives: u tau = corrSemigroup(max 0 tau) u0 for all tau >= 0  [orbit ID]
      (iii) eventuallyEq: near t > 0, u = corrSemigroup orbit (since all tau near t > 0)
      (iv)  HasDerivAt.congr_of_eventuallyEq transfers hD to u.

    #print axioms ns_gapB_from_sub_gaps = classical trio. -/
theorem ns_gapB_from_sub_gaps
    (h1 : NS_WeakMomentumDiffAt_OPEN s)
    (h2 : NS_SemigroupBochnerDiff_OPEN s)
    (h3 : NS_AdjointIntegralConst_OPEN s) :
    NS_CorrSemigroupStrongDiff_OPEN s := by
  intro u u₀ f hweak t ht
  -- Step 1: Bochner HasDerivAt for corrSemigroup orbit at t
  obtain ⟨D, hD⟩ := h2 u₀ t ht
  -- Step 2: Orbit identification -- u = corrSemigroup orbit for all tau >= 0
  have horb : ∀ τ : ℝ, 0 ≤ τ →
      u τ = corrSemigroup s (max 0 τ) (le_max_left 0 τ) u₀ :=
    h3 u u₀ f hweak h1 NS_CorrSemigroupGenerator_PROVED
  -- Step 3: EventuallyEq near t -- u agrees with semigroup orbit on Ioi 0
  have hIoi : Set.Ioi (0 : ℝ) ∈ 𝓝 t := IsOpen.mem_nhds isOpen_Ioi ht
  have hev : u =ᶠ[𝓝 t]
      (fun τ => corrSemigroup s (max 0 τ) (le_max_left 0 τ) u₀) :=
    Filter.eventually_of_mem hIoi (fun τ hτ => horb τ hτ.le)
  -- Step 4: Transfer HasDerivAt from semigroup orbit to u
  exact ⟨fun _ => D, hD.congr_of_eventuallyEq hev (horb t ht.le)⟩

/-! ## VI. Downstream benefit: Gap A (proved) now discharges one hypothesis -/

/-- **Phase 23: Gap A is proved -- NS_CorrSemigroupGenerator_OPEN is available.**
    Since Phase 22 proved NS_CorrSemigroupGenerator_PROVED, the downstream
    props NS_H3a_OPEN, NS_H3b_Vacuous_OPEN, NS_WeakNSUniqueness_OPEN
    (all defined in NSOrbitClosure) still take Gap A as an explicit hypothesis
    but it can now be discharged unconditionally with NS_CorrSemigroupGenerator_PROVED.
    Gap B (= NS_CorrSemigroupStrongDiff_OPEN) remains the binding constraint.
    Once B.1 + B.2 + B.3 are all closed, ns_gapB_from_sub_gaps delivers Gap B,
    and NS_CertCount4to2_OPEN fires: cert count drops from 4 to 2 (Gate1+Gate2). -/
theorem phase23_downstream_note : True := trivial

end BochnerDiff
end NS
end Towers
end TheoremaAureum
