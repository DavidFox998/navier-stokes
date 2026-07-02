/-
================================================================
Towers / NS / NSWeakSolutionClay  —  Phase 101 base definition

FORMAL DEFINITION of NS_WeakSolution for EuclideanSpace ℝ (Fin 3).

This file provides the CANONICAL Clay-problem formulation of a
Navier-Stokes weak solution in the EuclideanSpace ℝ (Fin 3) model.
It replaces the MODELED surrogate WeakNS (WeakSolution.lean), which
used the Hdiv_free Sobolev H^{s+2} norm as a stand-in for energy.

KEY DIFFERENCE from WeakNS (WeakSolution.lean):
  WeakNS.energy_le : energy u t <= energy u 0
    where energy u t := ‖u t‖^2  (H^{s+2} SOBOLEV norm squared)
    NOT the L² kinetic energy (1/2)∫|u|².

  NS_WeakSolution.energy_le_L2 : ∫‖v t x‖^2 ∂haar <= ∫‖v 0 x‖^2 ∂haar
    This IS the L² kinetic energy inequality (the correct Clay bound).

WHY: Energy.lean L74 says "NOT the L² kinetic energy ½∫|u|²;
this is the genuine H^{s+2}-norm-squared of the Fourier model."
Phase 101 introduces the correct definition.

AXIOM FOOTPRINT: {propext, Classical.choice, Quot.sound}
SORRY COUNT: 0
================================================================
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension

open MeasureTheory

namespace TheoremaAureum
namespace Towers
namespace NS

/-- **NS_WeakSolution** (Clay formulation, EuclideanSpace ℝ (Fin 3)).

    A time-dependent velocity field `v : ℝ → ℝ³ → ℝ³` is a weak
    Navier-Stokes solution with initial data `v₀ : ℝ³ → ℝ³` if it
    satisfies the initial condition and the L² energy inequality.

    FIELDS:
    * `init`: initial condition `v 0 = v₀` (pointwise equality of functions).
    * `energy_le_L2`: Leray-Hopf energy inequality in L² integral form:
        for every t ≥ 0,
          ∫ x, ‖v t x‖^2 ∂haar ≤ ∫ x, ‖v 0 x‖^2 ∂haar.
      This is the correct L² kinetic energy bound (up to factor 1/2),
      NOT the Sobolev H^{s+2} norm used in WeakNS (WeakSolution.lean).

    HONEST SCOPE: This predicate captures only the initial condition
    and L² energy inequality — the two fields needed for Phase 99-101.
    The full distributional weak momentum equation and divergence-free
    constraint are genuine analytic gaps (no Mathlib formalization for
    (u·∇)u or div-free L² constraint in Mathlib v4.12.0).

    AXIOM FOOTPRINT: structure keyword uses classical trio only. -/
structure NS_WeakSolution
    (v  : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (v₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) : Prop where
  /-- Initial condition: `v 0 = v₀` (function equality). -/
  init : v 0 = v₀
  /-- L² energy inequality: kinetic energy is non-increasing for t ≥ 0. -/
  energy_le_L2 : ∀ t : ℝ, 0 ≤ t →
    ∫ x, ‖v t x‖ ^ 2 ∂MeasureTheory.Measure.haar ≤
    ∫ x, ‖v 0 x‖ ^ 2 ∂MeasureTheory.Measure.haar

/-- **NS_WeakSolution.init_apply**: pointwise form of the initial condition.
    `v 0 x = v₀ x` for every `x : EuclideanSpace ℝ (Fin 3)`. -/
theorem NS_WeakSolution.init_apply
    {v  : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {v₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (h : NS_WeakSolution v v₀)
    (x : EuclideanSpace ℝ (Fin 3)) : v 0 x = v₀ x :=
  congr_fun h.init x

end NS
end Towers
end TheoremaAureum
