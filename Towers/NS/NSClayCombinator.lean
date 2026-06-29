/-
================================================================
Towers / NS / NSClayCombinator  —  NS Tower 540, Phase 7C (Master)

**Clay-grade master reduction for the incompressible Navier–Stokes problem.**

This file is the capstone of NS Tower 540. It reduces the Clay
Navier–Stokes existence-and-smoothness problem to THREE ATOMIC NAMED
SURFACES — the smallest set of named OPEN gates whose proofs would (in
the formalized Fourier model) give NS global regularity. It mirrors the
YM `ym_closure_combinator` and the BSD `BSD_Genesis759_Combinator`.

### The THREE atomic Clay gates

  1. `NS_AubinLions_OPEN K` — for all initial data `(u₀, f)`, the Galerkin
     sequence has a convergent subsequence and the energy inequality passes
     to the limit. Requires the Rellich–Kondrachov compact embedding
     `H^{s+2} ↪↪ H^s` (absent from Mathlib v4.12.0).

  2. `NS_NonlinearWeakForm_OPEN K` — the Galerkin limit satisfies the full
     (nonlinear) Navier–Stokes weak form for any forcing `f`. Requires
     the physical-space trilinear form `B(u,v,w)` in L² (absent from
     Mathlib v4.12.0).

  3. `NS_GlobalContinuation_OPEN s` — every (modeled) weak solution is
     locally smooth (i.e., `global_smooth_exists` holds) AND that local
     smoothness extends globally (no finite-time blow-up). This is the
     GENUINE Clay open problem.

### What is PROVED (classical trio, 0 sorry)

  * `ns_clay_combinator` — 3 atomic gates → `NS_ClayStatement s`.
    Proof: Gate 1 → `galerkin_subsequence_converges` + `energy_inequality_passes_to_limit`;
           Gate 2 → `limit_satisfies_weak_form`;
           `weak_solution_exists` (Phase 5);
           Gate 3 → local smoothness + global continuation.
    `#print axioms ns_clay_combinator` = classical trio. NS stays OPEN.
  * `ns_open_gate_count` — surface count: 3.
  * `ns_integration_by_parts_discharged` — `integration_by_parts` is CLOSED.

### Honest scope

  * `NS_ClayStatement s` is a MODELED surrogate (Fourier-side, ν=1, linear
    Stokes surrogate weak form, IsSmoothOn = temporal smoothness of tested
    profiles). NOT the literal Clay `u ∈ C^∞(ℝ³×[0,∞))` statement.
  * NS Tower stays `Status: Open`. Surfaces #1/#2 stay OPEN. No Clay claim.
================================================================
-/

import Towers.NS.NSStokesAdjoint
import Towers.NS.NSNonlinearTerm
import Towers.NS.Wall300_Scaffold

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal
open TheoremaAureum.Towers.NS.FunctionSpaces
open TheoremaAureum.Towers.NS.WeakSolution
open TheoremaAureum.Towers.NS.Regularity
open TheoremaAureum.Towers.NS.Wall300Scaffold

namespace TheoremaAureum
namespace Towers
namespace NS
namespace ClayCombinator

variable {s : ℝ}

/-!
## Atomic Clay gates (formally minimal named Props)
-/

/-- **CLAY GATE 1: Compact Sobolev embedding + Galerkin convergence.**
    For ALL initial data `(u₀, f)`, the Galerkin sequence has a convergent
    subsequence (compact embedding gives the extraction) AND the energy
    inequality passes to the limit (weak lower semicontinuity of norm).
    Requires Rellich–Kondrachov: `H^{s+2} ↪↪ H^s` compact. ABSENT from
    Mathlib v4.12.0.
    Mathematical status: KNOWN (Leray 1934, Aubin 1963, Lions 1969). -/
def NS_AubinLions_OPEN
    (K : ℕ → Submodule ℂ (Hdiv_free (s + 2))) [∀ n, FiniteDimensional ℂ (K n)] : Prop :=
  ∀ (u₀ : Hdiv_free (s + 2)) (f : ExternalForce s),
    galerkin_subsequence_converges K u₀ f ∧ energy_inequality_passes_to_limit K

/-- **CLAY GATE 2: Nonlinear weak form (limit satisfies NS).**
    For ANY forcing `f`, the Galerkin limit satisfies the (modeled) weak
    momentum balance `WeakMomentum u f`. Requires the nonlinear trilinear form
    `B(u,v,w) = ∫ ((u·∇)u)·v dx` in L² and its continuity under the Galerkin
    convergence topology. ABSENT from Mathlib v4.12.0.
    Mathematical status: KNOWN (Leray 1934). -/
def NS_NonlinearWeakForm_OPEN
    (K : ℕ → Submodule ℂ (Hdiv_free (s + 2))) [∀ n, FiniteDimensional ℂ (K n)] : Prop :=
  ∀ (f : ExternalForce s), limit_satisfies_weak_form K f

/-- **CLAY GATE 3: Local regularity + Global continuation (no blow-up).**
    EVERY (modeled) weak solution is smooth on some short interval `(0,T)` —
    i.e., `global_smooth_exists` holds — AND that local smoothness extends
    to every finite time `T > 0` — ruling out finite-time blow-up.
    The first part (`global_smooth_exists`) is provable from Stokes parabolic
    regularity + the energy inequality + Gate 2 in principle but requires
    the Sobolev embedding `∩_s H^s ↪ C^∞` (absent from Mathlib v4.12.0).
    The second part (NO BLOW-UP) is THE GENUINE Clay open problem.
    Mathematical status: OPEN (Clay 2000, Fefferman 2000). -/
def NS_GlobalContinuation_OPEN (s : ℝ) : Prop :=
  global_smooth_exists (s := s) ∧
  ∀ w : WeakSolution s, (∃ T > 0, IsSmoothOn w.u T) →
    ∀ T : ℝ, 0 < T → IsSmoothOn w.u T

/-!
## The NS Clay formal statement (modeled surrogate)
-/

/-- **NS Clay formal statement** (Fourier-side modeled surrogate).
    For every initial datum `u₀ ∈ Hdiv_free (s+2)` and forcing `f`,
    there exists a (modeled) weak solution `w : WeakSolution s` with
    `w.u₀ = u₀` that is smooth on every finite interval `(0,T)`.
    HONEST scope: MODELED (Fourier-side, ν=1, linear Stokes surrogate,
    IsSmoothOn = temporal-only smoothness). NOT the Clay C^∞(ℝ³×[0,∞)) statement. -/
def NS_ClayStatement (s : ℝ) : Prop :=
  ∀ (u₀ : Hdiv_free (s + 2)) (f : ExternalForce s),
    ∃ w : WeakSolution s, w.u₀ = u₀ ∧ ∀ T : ℝ, 0 < T → IsSmoothOn w.u T

/-!
## The master Clay combinator
-/

/-- **NS Clay master combinator (Phase 7C, trio-clean capstone).**

    GIVEN the THREE ATOMIC CLAY GATES:
      * `h1 : NS_AubinLions_OPEN K`      — compact embedding + Galerkin convergence,
      * `h2 : NS_NonlinearWeakForm_OPEN K` — nonlinear term in weak NS,
      * `h3 : NS_GlobalContinuation_OPEN s` — local regularity + no blow-up,

    the modeled `NS_ClayStatement s` holds.

    **Proof route:**
      (u₀, f) given.
      Gate 1 → `galerkin_subsequence_converges K u₀ f` + `energy_inequality_passes_to_limit K`
      Gate 2 → `limit_satisfies_weak_form K f`
      `weak_solution_exists` (Phase 5 combinator) → `∃ u, WeakNS u u₀ f`
      Package → `w : WeakSolution s` with `w.u₀ = u₀`
      Gate 3.1 (`global_smooth_exists`) + `weak_implies_strong` → `∃ T > 0, IsSmoothOn w.u T`
      Gate 3.2 (no blow-up) → `∀ T > 0, IsSmoothOn w.u T`

    `#print axioms ns_clay_combinator` = classical trio
    `[propext, Classical.choice, Quot.sound]` — NO `sorryAx`. NS stays OPEN. -/
theorem ns_clay_combinator
    (K : ℕ → Submodule ℂ (Hdiv_free (s + 2))) [∀ n, FiniteDimensional ℂ (K n)]
    (h1 : NS_AubinLions_OPEN K)
    (h2 : NS_NonlinearWeakForm_OPEN K)
    (h3 : NS_GlobalContinuation_OPEN s) :
    NS_ClayStatement s := by
  intro u₀ f
  -- Gate 1 → subsequence convergence + energy inequality for (u₀, f)
  obtain ⟨hconv, hener⟩ := h1 u₀ f
  -- Gate 2 → weak form for forcing f
  -- K explicit: `variable (K ...)` (round brackets) makes K an explicit param
  have hweak : limit_satisfies_weak_form K f := h2 f
  -- Phase 5 combinator: 3 inputs → ∃ u, WeakNS u u₀ f
  obtain ⟨u, hwns⟩ := weak_solution_exists K u₀ f hconv hweak hener
  -- Package the weak solution (fields: u, u₀, f, isWeak)
  let w : WeakSolution s := ⟨u, u₀, f, hwns⟩
  -- Gate 3.1 (global_smooth_exists) + Phase 6 combinator → local smoothness
  have hloc : ∃ T > 0, IsSmoothOn w.u T :=
    weak_implies_strong h3.1 w
  -- Gate 3.2 (no blow-up) → global-in-time smoothness
  exact ⟨w, rfl, h3.2 w hloc⟩

/-- **NS open gate count**: 3 (minimum in this formalization). -/
def ns_open_gate_count : ℕ := 3

/-- **Confirmed**: `integration_by_parts` is NOW CLOSED (Phase 7A). -/
theorem ns_integration_by_parts_discharged :
    @Energy.integration_by_parts s :=
  StokesAdjoint.integration_by_parts_proved

/-- **The Wall300 combinator** re-stated in Phase-7C terms: it is the
    special case of `ns_clay_combinator` where Gate 1 is given via
    `h_weak_exists` directly (bypassing the Galerkin construction). -/
theorem ns_clay_from_wall300
    (u₀ : Hdiv_free (s + 2)) (f : ExternalForce s)
    (h_weak_exists : ∃ u : ℝ → Hdiv_free (s + 2), WeakNS u u₀ f)
    (h_local : global_smooth_exists (s := s))
    (h_global : ∀ w : WeakSolution s, (∃ T > 0, IsSmoothOn w.u T) →
        ∀ T : ℝ, 0 < T → IsSmoothOn w.u T) :
    ∃ w : WeakSolution s, ∀ T : ℝ, 0 < T → IsSmoothOn w.u T :=
  navier_stokes_global_regularity u₀ f h_weak_exists h_local h_global

end ClayCombinator
end NS
end Towers
end TheoremaAureum
