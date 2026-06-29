/-
================================================================
Towers / NS / NSAdjointPackageClose  --  Phase 29

Closes Parts A (self-adjoint) and C (at t=0 = id) of
NS_AdjointPackage_OPEN (defined in Phase 28).
Introduces NS_AdjointPackage_PartB_OPEN (the remaining gap).

PROVED (classical trio, 0 sorry, 0 cert axioms):
  corrSemigroup_self_adjoint   -- Part A
    inner(corrSem t u₀, phi) = inner(u₀, corrSem t phi)
    Proof: L2.inner_def on both sides; corrSemigroup_coeFn_ae;
           inner_smul_left / inner_smul_right; corrSemigroupSymbol
           is a real cast so conj_ofReal kills the difference.

  corrSemigroup_at_zero        -- Part C
    corrSemigroup s 0 h u₀ = u₀
    Proof: corrSemigroupSymbol 0 xi = exp(0) = 1;
           corrSemigroup_coeFn_ae at t=0 gives ae 1 * u₀ xi = u₀ xi;
           Subtype.ext + Lp.ext closes.

NAMED OPEN DEF (replaces Part B of NS_AdjointPackage_OPEN):
  NS_AdjointPackage_PartB_OPEN
    inner(u t, phi) = inner(corrSem t u0, phi) for f=0, t > 0.
    Route: I(tau) = inner(u tau, corrSem(T-tau) phi); I' = 0 (Leibniz + A);
           scalar MVT => I(0) = I(T); density + Parts A,C => equality.
    Requires: NS_MuIntegralShift_OPEN (~1-2 days)
              + NS_ParametricDiff_OPEN (~1 week).
    ETA: 4-8 weeks.

CONDITIONAL (0 sorry, 0 cert axioms):
  NS_AdjointPackage_from_partB
    NS_AdjointPackage_PartB_OPEN => NS_AdjointPackage_OPEN
    (Parts A and C supplied here; Part B from the hypothesis.)

Named open defs after Phase 29 (to make ns_b3/ns_gapB unconditional):
  NS_StokesMaxReg_OPEN           (~2-4 months, Fourier DCT route)
  NS_AdjointPackage_PartB_OPEN   (~4-8 weeks, MVT + Leibniz)

Author: David Fox | Date: May 21, 2026
Series: Opera Numerorum (internal: Battle Plan v1.6)
================================================================
-/

import Towers.NS.NSAdjointArgument
import Towers.NS.NSFourierInner

open Real Set Filter Topology MeasureTheory
open scoped BigOperators ENNReal
open TheoremaAureum.Towers.NS.FunctionSpaces
open TheoremaAureum.Towers.NS.Stokes
open TheoremaAureum.Towers.NS.StokesAdjoint
open TheoremaAureum.Towers.NS.SemigroupDef
open TheoremaAureum.Towers.NS.GeneratorClose
open TheoremaAureum.Towers.NS.OrbitClosure
open TheoremaAureum.Towers.NS.FourierInner
open NSTower

namespace TheoremaAureum
namespace Towers
namespace NS
namespace AdjointPackageClose

variable {s : ℝ}

/-! ## I. Part A: corrSemigroup is self-adjoint in inner_{s+2} -/

/-- **Phase 29 Part A (PROVED, 0 sorry, classical trio).**

    inner_{s+2}(corrSem t u₀, phi) = inner_{s+2}(u₀, corrSem t phi).

    Proof:
      Expand both sides via L2.inner_def + corrSemigroup_coeFn_ae:
        LHS integrand: inner(symbol xi * u₀ xi, phi xi)
                     = conj(symbol xi) * inner(u₀ xi, phi xi)    [inner_smul_left]
        RHS integrand: inner(u₀ xi, symbol xi * phi xi)
                     = symbol xi * inner(u₀ xi, phi xi)           [inner_smul_right]
      corrSemigroupSymbol t xi = (Real.exp (...) : R) : C is real-cast,
      so conj(symbol) = symbol by Complex.conj_ofReal.
      Both integrands are equal; integral_congr_ae closes.
    #print axioms corrSemigroup_self_adjoint = classical trio. -/
theorem corrSemigroup_self_adjoint (s : ℝ) (u₀ φ : Hdiv_free (s + 2)) (t : ℝ) (ht : 0 ≤ t) :
    @inner ℂ (Hdiv_free (s + 2)) _ (corrSemigroup s t ht u₀) φ =
    @inner ℂ (Hdiv_free (s + 2)) _ u₀ (corrSemigroup s t ht φ) := by
  -- Reduce both sides to L2 integrals over mu(s+2)
  simp only [inner_Hdiv_eq, L2.inner_def]
  -- Show integrands ae-equal (filter_upwards on both corrSem coeFn)
  apply integral_congr_ae
  have hLp1 := corrSemigroup_coeFn_ae s t ht u₀
  have hLp2 := corrSemigroup_coeFn_ae s t ht φ
  filter_upwards [hLp1, hLp2] with ξ h1 h2
  -- Substitute: (corrSem t u₀) ξ = symbol ξ • u₀ ξ, etc.
  rw [h1, h2]
  -- inner(symbol • u₀ ξ, phi ξ) vs inner(u₀ ξ, symbol • phi ξ)
  rw [inner_smul_left, inner_smul_right]
  -- Goal: conj(symbol) * inner(u₀ ξ, phi ξ) = symbol * inner(u₀ ξ, phi ξ)
  -- corrSemigroupSymbol is real-cast => conj(symbol) = symbol
  congr 1
  simp only [corrSemigroupSymbol, map_ofReal, Complex.conj_ofReal]

/-! ## II. Part C: corrSemigroup at t=0 is the identity -/

/-- **Phase 29 Part C (PROVED, 0 sorry, classical trio).**

    corrSemigroup s 0 h u₀ = u₀ in Hdiv_free(s+2).

    Proof:
      corrSemigroupSymbol 0 xi = exp(-(||xi||^2 * 0) / ...) = exp(0) = 1.
      corrSemigroup_coeFn_ae at t=0: (corrSem 0 u₀) xi =ae 1 • u₀ xi = u₀ xi.
      Lp.ext (ae pointwise) + Subtype.ext closes.
    #print axioms corrSemigroup_at_zero = classical trio. -/
theorem corrSemigroup_at_zero (s : ℝ) (h : (0 : ℝ) ≤ 0) (u₀ : Hdiv_free (s + 2)) :
    corrSemigroup s 0 h u₀ = u₀ := by
  -- Reduce Hdiv_free equality to Lp equality
  apply Subtype.ext
  -- Reduce Lp equality to ae pointwise equality
  apply Lp.ext
  -- corrSemigroup_coeFn_ae at t=0 gives: (corrSem 0 u₀) xi =ae symbol 0 xi • u₀ xi
  have hae := corrSemigroup_coeFn_ae s 0 h u₀
  -- symbol 0 xi = exp(0) = 1; so 1 • u₀ xi = u₀ xi
  simp only [corrSemigroupSymbol, mul_zero, neg_zero, zero_div,
             Real.exp_zero, Complex.ofReal_one, one_smul] at hae
  exact hae

/-! ## III. Named open def: Part B (f=0 scalar inner equality) -/

/-- **[NAMED OPEN DEF] NS_AdjointPackage_PartB_OPEN -- Phase 29 remaining gap.**

    STATEMENT:
      For f=0 WeakNS solutions u with data u₀, any phi, t > 0:
        inner_{s+2}(u t, phi) = inner_{s+2}(corrSem t u₀, phi).

    MATHEMATICAL ROUTE (0 sorry, depends on NS_MuIntegralShift_OPEN):
      Define I(tau) = inner(u tau, corrSem(T-tau) phi) for tau in [0, T].
      HasDerivAt I:
        I'(tau) = inner(D_u tau, corrSem(T-tau) phi)           [hmreg: HasDerivAt u D_u tau]
                + inner(u tau, d/dtau corrSem(T-tau) phi)       [Gap A: HasDerivAt corrSem]
      By hmreg inner product formula (for f=0):
        inner(D_u tau, psi) = -inner_s(stokes u tau, embed psi)
      By the generator + Part A (self-adjoint):
        inner(u tau, d/dtau corrSem(T-tau) phi)
          = inner_s(stokes u tau, embed corrSem(T-tau) phi)     [NS_AdjointInner_v2_OPEN]
      These cancel: I'(tau) = 0 for f=0.
      Scalar MVT (Mathlib isConst_of_deriv_eq_zero): I constant => I(0) = I(T).
      I(T) = inner(u T, corrSem 0 phi) = inner(u T, phi)       [Part C: corrSem 0 = id]
      I(0) = inner(u 0, corrSem T phi) = inner(u₀, corrSem T phi) [WeakNS.init]
            = inner(corrSem T u₀, phi)                          [Part A: self-adjoint]
      QED.

    LEAN OBSTACLES (each a Lean API gap, not mathematical):
      NS_MuIntegralShift_OPEN  (withDensity integral shift; ETA: 1-2 days)
        -> closes NS_AdjointInner_v2_OPEN (Phase 20 conditional)
        -> used in I'=0 cancellation (inner(u, stokes corrSem phi) step)
      NS_ParametricDiff_OPEN   (DCT for HasDerivAt t -> inner(corrSem t phi, psi))
        -> used for HasDerivAt of tau -> corrSem(T-tau) phi
      HasDerivAt.inner         (Leibniz rule for Hilbert inner product; in Mathlib v4.12.0)
      isConst_of_deriv_eq_zero (scalar MVT; in Mathlib v4.12.0)

    ETA: 4-8 weeks (after NS_MuIntegralShift_OPEN + NS_ParametricDiff_OPEN). -/
def NS_AdjointPackage_PartB_OPEN (s : ℝ) : Prop :=
  ∀ (u : ℝ → Hdiv_free (s + 2)) (u₀ : Hdiv_free (s + 2))
    (_hmreg : NS_StokesMaxReg_OPEN s)
    (_hweak : WeakNS u u₀ (fun _ => (0 : Hdiv_free (s + 2))))
    (φ : Hdiv_free (s + 2)) (t : ℝ) (ht : 0 < t),
    @inner ℂ (Hdiv_free (s + 2)) _ (u t) φ =
    @inner ℂ (Hdiv_free (s + 2)) _ (corrSemigroup s t ht.le u₀) φ

/-! ## IV. Conditional: NS_AdjointPackage_OPEN from Part B -/

/-- **Phase 29 conditional (0 sorry, classical trio).**

    Given NS_AdjointPackage_PartB_OPEN s, all three parts of
    NS_AdjointPackage_OPEN s are satisfied:
      hpkg.1   -- Part A: corrSemigroup_self_adjoint (proved above)
      hpkg.2.1 -- Part B: hpartB (hypothesis, named open)
      hpkg.2.2 -- Part C: corrSemigroup_at_zero (proved above)

    Net reduction: NS_AdjointPackage_OPEN reduces to one remaining gap.
    #print axioms NS_AdjointPackage_from_partB = classical trio + NS_AdjointPackage_PartB_OPEN. -/
theorem NS_AdjointPackage_from_partB
    (hpartB : NS_AdjointPackage_PartB_OPEN s) :
    NS_AdjointPackage_OPEN s :=
  ⟨-- Part A: self-adjoint (proved in this file)
   fun u₀ φ t ht => corrSemigroup_self_adjoint s u₀ φ t ht,
   -- Part B: scalar inner equality for f=0 (named open, conditional)
   fun u u₀ hmreg hweak φ t ht => hpartB u u₀ hmreg hweak φ t ht,
   -- Part C: corrSem at t=0 = id (proved in this file)
   fun u₀ h => corrSemigroup_at_zero s h u₀⟩

/-! ## V. Strengthened ns_b3 and ns_gapB using Phase 29 -/

/-- **Phase 29: ns_b3 conditional on PartB + NS_StokesMaxReg only (0 sorry).**

    Compared to Phase 28 (ns_b3_fZero_from_adjPkg):
      Phase 28: needs NS_StokesMaxReg_OPEN + NS_AdjointPackage_OPEN (2 named open defs)
      Phase 29: needs NS_StokesMaxReg_OPEN + NS_AdjointPackage_PartB_OPEN (Parts A,C proved)
    Net improvement: NS_AdjointPackage_PartB_OPEN replaces the full NS_AdjointPackage_OPEN. -/
theorem ns_b3_fZero_v2 (s : ℝ)
    (hmreg  : NS_StokesMaxReg_OPEN s)
    (hpartB : NS_AdjointPackage_PartB_OPEN s)
    (u  : ℝ → Hdiv_free (s + 2))
    (u₀ : Hdiv_free (s + 2))
    (hweak : WeakNS u u₀ (fun _ => (0 : Hdiv_free (s + 2))))
    (t : ℝ) (ht : 0 ≤ t) :
    u t = corrSemigroup s (max 0 t) (le_max_left 0 t) u₀ :=
  ns_b3_fZero_from_adjPkg s hmreg (NS_AdjointPackage_from_partB hpartB) u u₀ hweak t ht

/-- **Phase 29: ns_gapB conditional on PartB + NS_StokesMaxReg only (0 sorry).** -/
theorem ns_gapB_fZero_v2 (s : ℝ)
    (hmreg  : NS_StokesMaxReg_OPEN s)
    (hpartB : NS_AdjointPackage_PartB_OPEN s) :
    NS_CorrSemigroupStrongDiff_fZero s :=
  ns_gapB_fZero_from_maxReg_adjPkg s hmreg (NS_AdjointPackage_from_partB hpartB)

/-! ## VI. Phase 29 gap accounting -/

/-- **Phase 29 gap accounting (0 sorry throughout).**

    PROVED IN PHASE 29 (classical trio, 0 cert axioms):
      corrSemigroup_self_adjoint  -- Part A of NS_AdjointPackage_OPEN
      corrSemigroup_at_zero       -- Part C of NS_AdjointPackage_OPEN
      NS_AdjointPackage_from_partB  -- Part B suffices for full NS_AdjointPackage_OPEN
      ns_b3_fZero_v2              -- Phase 28 B.3 but with fewer hypotheses
      ns_gapB_fZero_v2            -- Phase 28 Gap B but with fewer hypotheses

    NAMED GAPS after Phase 29 (2 total, for ns_gapB unconditional):

      NS_StokesMaxReg_OPEN  (~6-18 months Hieber-Pruss abstract route)
        Fourier DCT route: ~2-4 months.
        Approach: energy uniqueness (stokes_op PSD + WeakMomentum Gronwall)
        -> u = corrSem orbit for f=0 -> DCT: (corrSem(t+h)-corrSem t)/h -> D in Lp.
        Blocks: ns_b3_fZero_v2, ns_gapB_fZero_v2 (directly).

      NS_AdjointPackage_PartB_OPEN  (~4-8 weeks)
        Next step: Phase 30 = NS_MuIntegralShift_OPEN (~1-2 days).
        Then Phase 31 = Part B (Leibniz + scalar MVT, ~4-6 weeks).
        Blocks: ns_b3_fZero_v2, ns_gapB_fZero_v2 (via NS_AdjointPackage_from_partB).

    CLOSURE ROADMAP:
      Phase 30: NS_MuIntegralShift_OPEN (~1-2 days)
        withDensity integral mu(s+2) -> mu(s) with density factor.
      Phase 31: NS_AdjointPackage_PartB_OPEN (~4-8 weeks)
        Closes NS_AdjointPackage_OPEN via NS_AdjointPackage_from_partB.
      Phase 32: NS_StokesMaxReg_OPEN via Fourier DCT (~2-4 months)
        Step A: Uniqueness (energy argument: stokes_op PSD + Gronwall)
        Step B: DCT convergence in Lp (bounded symbol, DCT API)
        Step C: Inner product formula from Gap A

    AFTER PHASES 30+31+32:
      ns_b3_fZero_v2, ns_gapB_fZero_v2 FULLY UNCONDITIONAL (0 named open defs).

    CERT FOOTPRINT: 2 (Gate1 + Gate2, unchanged). NS Clay Surface #1: LOCKED OPEN. -/
theorem phase29_gap_accounting : True := trivial

end AdjointPackageClose
end NS
end Towers
end TheoremaAureum
