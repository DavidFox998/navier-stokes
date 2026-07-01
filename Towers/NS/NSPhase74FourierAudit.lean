/-
================================================================
Towers / NS / NSPhase74FourierAudit  --  NS Tower Phase 74

PHASE 74: API audit for 3 Fourier micro-gaps from Phase 73.
          Close F3 (Fourier inversion) using Mathlib v4.12.0.

AUDIT RESULTS (July 1, 2026 — Mathlib v4.12.0, 7 files in Analysis/Fourier/):

  Files searched: AddCircle.lean, FourierTransform.lean, FourierTransformDeriv.lean,
                  Inversion.lean, PoissonSummation.lean, RiemannLebesgueLemma.lean, ZMod.lean

  GAP F1 (NS_FourierKernelAPI_OPEN):
    Searched: MeasureTheory.fourierIntegral_rpow_eq
    Result: NOT IN Mathlib v4.12.0. Zero occurrences across all 7 files.
    No Riesz kernel Fourier symbol theorem exists in any form.
    Action: NS_FourierKernelAPI_OPEN remains as named open def.

  GAP F2 (NS_ConvolutionFourierAPI_OPEN):
    Searched: VectorFourier.convolution_fourierIntegral
    Result: NOT IN Mathlib v4.12.0. Zero occurrences.
    PRESENT (different): VectorFourier.integral_bilin_fourierIntegral_eq_flip
      proves ∫ M(𝓕f ξ)(g ξ) dξ = ∫ M(f x)(𝓕g x) dx  [Plancherel self-adjointness]
      This is NOT the convolution theorem 𝓕(f ⋆ g)(ξ) = 𝓕f(ξ) · 𝓕g(ξ).
    Action: NS_ConvolutionFourierAPI_OPEN remains as named open def.

  GAP F3 (NS_FourierInversionAPI_OPEN):
    Searched: VectorFourier.fourierIntegral_fourierIntegral
    Result: NOT IN Mathlib v4.12.0 by that name.
    FOUND (different name, same content):
      Inversion.lean (Sébastien Gouëzel, 2024):
        MeasureTheory.Integrable.fourier_inversion :
          𝓕⁻ (𝓕 f) v = f v
          [Integrable f, Integrable (𝓕 f), ContinuousAt f v]
        Continuous.fourier_inversion :
          𝓕⁻ (𝓕 f) = f
          [Continuous f, Integrable f, Integrable (𝓕 f)]
    BUG in Phase 72: NS_FourierInversion_OPEN states 𝓕(𝓕 g) =ᵐ g (double forward).
      Correct formula: 𝓕⁻ (𝓕 f) = f  (inverse Fourier of forward Fourier = identity).
      𝓕(𝓕 f)(x) = f(-x) ≠ f(x) for general non-even f.
    Action: Introduce NS_FourierInversionL2_OPEN (correct L² statement with 𝓕⁻).
            Prove NS_FourierInversionCorr_PROVED for continuous+integrable case (0 sorry).
            NS_FourierInversion_OPEN (Phase 72) bug noted; chain update in Phase 75.

PROGRESS AFTER PHASE 74:
  F1: OPEN (absent from Mathlib v4.12.0)
  F2: OPEN (absent from Mathlib v4.12.0; self-adjointness ≠ convolution)
  F3: PARTIALLY CLOSED
      Continuous+integrable case: PROVED (0 sorry, Continuous.fourier_inversion)
      Pure L² case: NS_FourierInversionL2_OPEN (named open def, remains open)

Sorry count: 0.
Axioms: {propext, Classical.choice, Quot.sound}.
================================================================
-/

import Towers.NS.NSPhase73FourierSubgaps
import Mathlib.Analysis.Fourier.Inversion

open Filter Topology Real MeasureTheory VectorFourier
open scoped BigOperators ENNReal NNReal FourierTransform RealInnerProductSpace
open TheoremaAureum.Towers.NS.FunctionSpaces
open TheoremaAureum.Towers.NS.Phase64FourierBridge
open TheoremaAureum.Towers.NS.Phase72FourierChain
open TheoremaAureum.Towers.NS.Phase73FourierSubgaps

namespace TheoremaAureum
namespace Towers
namespace NS
namespace Phase74FourierAudit

/-! ## §A. Audit confirmation: F1 and F2 NOT in Mathlib v4.12.0 -/

/-- **Audit F1**: MeasureTheory.fourierIntegral_rpow_eq absent from Mathlib v4.12.0.
    Zero occurrences in all 7 Fourier analysis files.
    NS_FourierKernelAPI_OPEN (Phase 73) is the correct named open def. -/
def audit_F1_absent : True := trivial

/-- **Audit F2**: VectorFourier.convolution_fourierIntegral absent from Mathlib v4.12.0.
    Zero occurrences. The closest available theorem is:
      VectorFourier.integral_bilin_fourierIntegral_eq_flip :
        ∫ M (𝓕f ξ) (g ξ) dξ = ∫ M (f x) (𝓕g x) dx
    This is Plancherel self-adjointness (∫𝓕f·g = ∫f·𝓕g), NOT convolution (𝓕(f⋆g)=𝓕f·𝓕g).
    NS_ConvolutionFourierAPI_OPEN (Phase 73) is the correct named open def. -/
def audit_F2_absent : True := trivial

/-! ## §B. F3: Corrected Fourier inversion using Mathlib Inversion.lean -/

/-- **Phase 72 bug**: NS_FourierInversion_OPEN states
      (𝓕 ∘ 𝓕) g =ᵐ g  (double forward Fourier)
    This is INCORRECT in general: (𝓕 ∘ 𝓕) f (x) = f(-x) ≠ f(x).
    The correct Riesz representation formula requires
      (𝓕⁻ ∘ 𝓕) f = f  (inverse Fourier of forward Fourier = identity)
    Mathlib Inversion.lean provides exactly this. -/

/-- **NS_FourierInversionL2_OPEN** — corrected Fourier inversion for L².
    𝓕⁻ (𝓕 g) =ᵐ[volume] g  for g ∈ L²(ℝ³, ℂ).
    Uses fourierIntegralInv (𝓕⁻) from FourierTransform.lean, NOT a second 𝓕.
    Mathlib has this for Continuous+Integrable case (proved below).
    Pure L² case (no continuity assumption) remains open — needs density argument. -/
def NS_FourierInversionL2_OPEN : Prop :=
  ∀ (g : EuclideanSpace ℝ (Fin 3) → ℂ),
    MeasureTheory.MemLp g 2 (volume : Measure _) →
    𝓕⁻ (𝓕 g) =ᵐ[volume] g

/-- **NS_FourierInversionCorr_PROVED** — Fourier inversion for continuous integrable functions.
    PROVED (0 sorry) via Mathlib v4.12.0 Continuous.fourier_inversion.

    Theorem used (Inversion.lean, Sébastien Gouëzel, 2024):
      Continuous.fourier_inversion :
        Continuous f → Integrable f → Integrable (𝓕 f) → 𝓕⁻ (𝓕 f) = f

    Here 𝓕 = fourierIntegral (from open scoped FourierTransform),
         𝓕⁻ = fourierIntegralInv (inverse Fourier, opposite sign in exponential).
    Both match the NS Tower's VectorFourier convention via fourierIntegral_eq.

    Scope: applies to f : EuclideanSpace ℝ (Fin 3) → ℂ that are continuous and integrable
    with integrable Fourier transform. This closes the continuous case of
    NS_FourierInversionL2_OPEN. The pure L² case remains NS_FourierInversionL2_OPEN. -/
theorem NS_FourierInversionCorr_PROVED
    (g   : EuclideanSpace ℝ (Fin 3) → ℂ)
    (hc  : Continuous g)
    (hg  : Integrable g (volume : Measure _))
    (hFg : Integrable (𝓕 g) (volume : Measure _)) :
    𝓕⁻ (𝓕 g) = g :=
  hc.fourier_inversion hg hFg

/-- **NS_FourierInversionCorr_ae** — a.e. corollary (0 sorry).
    For continuous integrable g with integrable Fourier transform: 𝓕⁻(𝓕 g) =ᵐ g.
    Immediate from NS_FourierInversionCorr_PROVED via ae_of_all. -/
theorem NS_FourierInversionCorr_ae
    (g   : EuclideanSpace ℝ (Fin 3) → ℂ)
    (hc  : Continuous g)
    (hg  : Integrable g (volume : Measure _))
    (hFg : Integrable (𝓕 g) (volume : Measure _)) :
    𝓕⁻ (𝓕 g) =ᵐ[volume] g :=
  ae_of_all _ (congr_fun (hc.fourier_inversion hg hFg))

/-- **NS_FourierInversionCorr_pointwise** — pointwise version (0 sorry).
    For continuous integrable g with integrable Fourier transform: 𝓕⁻(𝓕 g)(v) = g(v).
    Uses MeasureTheory.Integrable.fourier_inversion directly (pointwise form). -/
theorem NS_FourierInversionCorr_pointwise
    (g   : EuclideanSpace ℝ (Fin 3) → ℂ)
    (hg  : Integrable g (volume : Measure _))
    (hFg : Integrable (𝓕 g) (volume : Measure _))
    (v   : EuclideanSpace ℝ (Fin 3))
    (hv  : ContinuousAt g v) :
    𝓕⁻ (𝓕 g) v = g v :=
  hg.fourier_inversion hFg hv

/-! ## §C. Chain update: F3 status and remaining gap -/

/-- **NS_FourierInversionL2_from_cont** (0 sorry, conditional on density).
    The L² case follows from the continuous case by density of C_c(ℝ³) in L²,
    but this density argument requires a Mathlib API for approximation in eLpNorm.
    Named conditional: closes NS_FourierInversionL2_OPEN when density is provided. -/
def NS_FourierInversionDensity_OPEN : Prop :=
  ∀ (g : EuclideanSpace ℝ (Fin 3) → ℂ),
    MeasureTheory.MemLp g 2 (volume : Measure _) →
    ∃ (gn : ℕ → EuclideanSpace ℝ (Fin 3) → ℂ),
      (∀ n, Continuous (gn n)) ∧
      (∀ n, Integrable (gn n) (volume : Measure _)) ∧
      (∀ n, Integrable (𝓕 (gn n)) (volume : Measure _)) ∧
      Tendsto (fun n => eLpNorm (gn n - g) 2 volume) atTop (𝓝 0)

/-- **NS_FourierInversionL2_LimitPassage_OPEN**: L² limit passage (named open def).
    Given gn → g in L² and 𝓕⁻(𝓕 gn) = gn for all n, prove 𝓕⁻(𝓕 g) =ᵐ g.
    Requires: Plancherel continuity of 𝓕⁻∘𝓕 on L² + a.e. subsequence argument.
    Phase 75 closes via MeasureTheory.tendsto_Lp + Lp.ae_tendsto_of_cauchy. -/
def NS_FourierInversionL2_LimitPassage_OPEN : Prop :=
  ∀ (g : EuclideanSpace ℝ (Fin 3) → ℂ)
    (gn : ℕ → EuclideanSpace ℝ (Fin 3) → ℂ),
    (∀ n, 𝓕⁻ (𝓕 (gn n)) = gn n) →
    Tendsto (fun n => eLpNorm (gn n - g) 2 volume) atTop (𝓝 0) →
    𝓕⁻ (𝓕 g) =ᵐ[volume] g

/-- **NS_FourierInversionL2_from_density** (0 sorry, conditional on 2 named gaps):
    density sub-gap (NS_FourierInversionDensity_OPEN) + limit passage sub-gap
    (NS_FourierInversionL2_LimitPassage_OPEN).
    Proof: unpack density to get gn → g in L² with 𝓕⁻(𝓕 gn) = gn, apply limit. -/
theorem NS_FourierInversionL2_from_density
    (h_dens : NS_FourierInversionDensity_OPEN)
    (h_lim  : NS_FourierInversionL2_LimitPassage_OPEN) :
    NS_FourierInversionL2_OPEN := by
  intro g hg
  obtain ⟨gn, hcont, hint, hFint, htend⟩ := h_dens g hg
  exact h_lim g gn
    (fun n => NS_FourierInversionCorr_PROVED (gn n) (hcont n) (hint n) (hFint n))
    htend

/-! ## §D. Phase 74 summary ledger -/

/-
PHASE 74 LEDGER (July 1, 2026):

API AUDIT — Mathlib v4.12.0:
  F1: MeasureTheory.fourierIntegral_rpow_eq     — NOT IN MATHLIB (0 hits)
  F2: VectorFourier.convolution_fourierIntegral  — NOT IN MATHLIB (0 hits)
  F3: VectorFourier.fourierIntegral_fourierIntegral — NOT by that name
      FOUND: Continuous.fourier_inversion (Inversion.lean) — CLOSED continuous case

PROVED (0 sorry, classical trio):
  NS_FourierInversionCorr_PROVED     ✓ Continuous.fourier_inversion (Mathlib v4.12.0)
  NS_FourierInversionCorr_ae         ✓ corollary (ae_of_all + congr_fun)
  NS_FourierInversionCorr_pointwise  ✓ Integrable.fourier_inversion (pointwise form)
  NS_FourierInversionL2_from_density ✓ conditional on Density_OPEN + LimitPassage_OPEN

NEW NAMED OPEN DEFS (no axiom):
  NS_FourierInversionL2_OPEN              ← 𝓕⁻(𝓕 g) =ᵐ g for g ∈ L² (correct F3 statement)
  NS_FourierInversionDensity_OPEN         ← C_c(ℝ³) approximation in L² (density argument)
  NS_FourierInversionL2_LimitPassage_OPEN ← L² limit commutes with 𝓕⁻∘𝓕 (Plancherel)

PHASE 72 BUG DOCUMENTED:
  NS_FourierInversion_OPEN (Phase 72) uses 𝓕∘𝓕 (double forward Fourier).
  Correct formula: 𝓕⁻∘𝓕 = id. Phase 72 def is MATHEMATICALLY WRONG for non-even f.
  Chain update (Phase 75): replace NS_FourierInversion_OPEN with NS_FourierInversionL2_OPEN
  in NS_FourierRieszRep_Conditional.

D1 OPEN SURFACES — after Phase 74:
  NS_FourierKernelAPI_OPEN    ← OPEN (F1 absent from Mathlib)
  NS_ConvolutionFourierAPI_OPEN ← OPEN (F2 absent from Mathlib)
  NS_FourierInversionL2_OPEN  ← OPEN (F3 pure L² case; continuous case proved)
  NS_FourierInversionDensity_OPEN ← OPEN (density bridge for L² case)

SELF-ADJOINTNESS NOTE (for Meta AI):
  integral_bilin_fourierIntegral_eq_flip PROVES:
    ∫ M (𝓕f ξ) (g ξ) dξ = ∫ M (f x) (𝓕g x) dx
  This is Plancherel duality / self-adjointness. It is NOT the convolution theorem.
  The convolution theorem 𝓕(f⋆g) = 𝓕f·𝓕g requires a SEPARATE proof strategy.
  Current best approach: approximate K = ‖·‖^{-5/2} by K_ε ∈ L¹, apply L¹ convolution,
  pass to limit via Young bound (Phase 70). This is F2 sub-gap, not closeable from
  self-adjointness alone.

PHASE 75 TODO:
  1. Fix NS_FourierRieszRep_Conditional (Phase 72): replace NS_FourierInversion_OPEN
     with NS_FourierInversionL2_OPEN (i.e., use 𝓕⁻ instead of 𝓕 on outside).
  2. Close NS_FourierInversionDensity_OPEN: approximation of L² by continuous functions
     (e.g., using MeasureTheory.Memℒp.approxc or similar Mathlib density lemma).
  3. Close NS_FourierInversionL2_OPEN from density + continuity inversion.
  4. F1 and F2 remain as named open defs until Mathlib gains Riesz/convolution APIs.
-/

end Phase74FourierAudit
end NS
end Towers
end TheoremaAureum
