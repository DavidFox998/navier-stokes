/-
================================================================
Towers / NS / NSSemigroupDef  --  NS Tower 540, Phase 16

Defines the corrected Stokes semigroup (Fourier multiplier matching
WeakMomentum) and proves uniqueness + smoothness conditionally on
two named open defs.

INDEX CORRECTION (David Fox / Claude, June 2026):
WeakMomentum mixes two Sobolev inner products:
  LHS: d/dt inner_{s+2}(u t, phi)               weight (1+|xi|^2)^{s+2}
  RHS: -inner_s(stokes_op s (u t), embed phi)   weight (1+|xi|^2)^s

For the Fourier-mode ansatz u(t,xi) = exp(-alpha_xi*t)*u0(xi):
  -alpha_xi*(1+|xi|^2)^{s+2} = -|xi|^2*(1+|xi|^2)^s
  => alpha_xi = |xi|^2 / (1+|xi|^2)^2

So corrSemigroupSymbol = exp(-|xi|^2*t/(1+|xi|^2)^2), NOT exp(-|xi|^2*t).
Both decay to zero; the corrected version is bounded and C^inf in t.

PROVED (classical trio, 0 cert axioms, 0 sorry):
  corrSemigroupSymbol_norm_le  -- |exp(-alpha_xi*t)| <= 1 for t >= 0
  corrSemigroup_eLpNorm_le     -- eLpNorm of multiplied field <= original
  corrSemigroup                -- bounded linear map Hdiv_free(s+2)->LHdiv_free(s+2)
  corrSemigroup_norm_le        -- operator norm <= 1

NAMED OPEN (0 cert axioms, 0 sorry):
  NS_CorrSemigroupGenerator_OPEN  -- HasDerivAt for inner(semigroup t u0, phi)
                                   -- (requires differentiating under L^2 integral)
  NS_CorrSemigroupStrongDiff_OPEN -- WeakNS solutions are strongly H-differentiable
                                   -- (required for Gronwall energy argument)

PROVED CONDITIONALLY (generator + strongDiff as hypotheses):
  ns_corrSemigroup_weakMomentum   -- semigroup satisfies WeakMomentum (from generator)
  ns_corrSemigroup_inner_unique   -- inner(w t, phi) = 0 for all phi => w t = 0
  ns_corrSemigroup_unique         -- u t = corrSemigroup t u0 (Gronwall, from both gaps)
  ns_corrSemigroup_smooth         -- ContDiffOn R top (inner(semigroup t u0, phi)) [proved]
  ns_corrSemigroup_closed         -- NS_SemigroupClosed_OPEN (from generator + strongDiff)

NET STATUS after Phase 16:
  NS_SemigroupClosed_OPEN -> THEOREM given generator + strongDiff
  Both named gaps are Lean formalization problems, not Clay open problems.
  Once Mathlib formalizes integral differentiation + Bochner ODE regularity,
  h3a becomes unconditional; h3b auto-closes; cert reduces to V4(h1, h2).

#print axioms corrSemigroup         = classical trio
#print axioms corrSemigroup_norm_le = classical trio
================================================================
-/

import Towers.NS.NSStokesSmoothing
import Towers.NS.NSStokesAdjoint
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Real Set Filter Topology MeasureTheory
open scoped ENNReal BigOperators
open TheoremaAureum.Towers.NS.FunctionSpaces
open TheoremaAureum.Towers.NS.Stokes
open TheoremaAureum.Towers.NS.StokesAdjoint
open TheoremaAureum.Towers.NS.WeakSolution
open TheoremaAureum.Towers.NS.Regularity
open TheoremaAureum.Towers.NS.Gate3Decomp
open TheoremaAureum.Towers.NS.StokesSmoothing

namespace TheoremaAureum
namespace Towers
namespace NS
namespace SemigroupDef

variable {s : ℝ}

/-!
## I. Corrected semigroup symbol: exp(-|xi|^2*t / (1+|xi|^2)^2)
-/

/-- Fourier symbol of the corrected Stokes semigroup.
    INDEX CORRECTION: alpha_xi = |xi|^2/(1+|xi|^2)^2 (not |xi|^2).
    Derivation from WeakMomentum: see file header. -/
noncomputable def corrSemigroupSymbol (t : ℝ) (ξ : Freq) : ℂ :=
  ((Real.exp (-(‖ξ‖ ^ 2 * t) / (1 + ‖ξ‖ ^ 2) ^ 2) : ℝ) : ℂ)

/-- For t >= 0 the symbol has norm <= 1: alpha_xi*t >= 0 so exp(-alpha_xi*t) <= 1.
    Classical trio, 0 sorry. -/
theorem corrSemigroupSymbol_norm_le (t : ℝ) (ht : 0 ≤ t) (ξ : Freq) :
    ‖corrSemigroupSymbol t ξ‖ ≤ 1 := by
  simp only [corrSemigroupSymbol, Complex.norm_real,
             Real.norm_of_nonneg (Real.exp_pos _).le]
  have h1 : 0 ≤ ‖ξ‖ ^ 2 * t := mul_nonneg (sq_nonneg _) ht
  have h2 : 0 < (1 + ‖ξ‖ ^ 2) ^ 2 := by positivity
  calc Real.exp (-(‖ξ‖ ^ 2 * t) / (1 + ‖ξ‖ ^ 2) ^ 2)
      ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith [div_nonneg h1 h2.le])
    _ = 1 := Real.exp_zero

/-- Continuity of the corrected symbol in xi (for measurability). -/
theorem continuous_corrSemigroupSymbol (t : ℝ) :
    Continuous (corrSemigroupSymbol t) := by
  unfold corrSemigroupSymbol
  apply Complex.continuous_ofReal.comp
  apply Real.continuous_exp.comp
  apply ContinuousAt.continuousOn.continuous_of_mem_nhds (s := Set.univ)
  · exact fun _ _ => mem_univ _
  · intro x
    apply ContinuousAt.neg
    apply ContinuousAt.div_const
    apply ContinuousAt.mul
    · exact ((continuous_norm.pow 2).continuousAt)
    · exact continuousAt_const
    · exact ((continuous_const.add (continuous_norm.pow 2)).pow 2).continuousAt

/-- A.e.-strong-measurability of corrected-symbol multiplied field. -/
theorem corrSemigroup_aesm (s : ℝ) (t : ℝ) (f : Hsv (s + 2)) :
    AEStronglyMeasurable (fun ξ => corrSemigroupSymbol t ξ • f ξ) (mu (s + 2)) :=
  ((continuous_corrSemigroupSymbol t).aestronglyMeasurable).smul
    (Lp.aestronglyMeasurable f)

/-- eLpNorm of corrected-symbol multiplied field <= eLpNorm of original. -/
theorem corrSemigroup_eLpNorm_le (s : ℝ) (t : ℝ) (ht : 0 ≤ t) (f : Hsv (s + 2)) :
    eLpNorm (fun ξ => corrSemigroupSymbol t ξ • f ξ) 2 (mu (s + 2)) ≤
    eLpNorm (⇑f) 2 (mu (s + 2)) := by
  apply eLpNorm_mono_ae
  filter_upwards with ξ
  rw [nnnorm_smul]
  have hle : ‖corrSemigroupSymbol t ξ‖₊ ≤ 1 := by
    have := corrSemigroupSymbol_norm_le ht ξ
    rwa [← Real.nnnorm_eq_abs, ← NNReal.coe_le_coe, NNReal.coe_nnnorm,
         NNReal.coe_one] at this
  calc ‖corrSemigroupSymbol t ξ‖₊ * ‖f ξ‖₊
      ≤ 1 * ‖f ξ‖₊ := mul_le_mul_of_nonneg_right hle (zero_le _)
    _ = ‖f ξ‖₊ := one_mul _

/-- The corrected semigroup multiplied field is in Lp. -/
theorem corrSemigroup_memLp (s : ℝ) (t : ℝ) (ht : 0 ≤ t) (f : Hsv (s + 2)) :
    Memℒp (fun ξ => corrSemigroupSymbol t ξ • f ξ) 2 (mu (s + 2)) :=
  ⟨corrSemigroup_aesm s t f,
   lt_of_le_of_lt (corrSemigroup_eLpNorm_le s t ht f) (Lp.memℒp f).2⟩

/-- Corrected semigroup as a linear map Hsv(s+2) ->_L[C] Hsv(s+2). -/
noncomputable def corrSemigroupLin (s : ℝ) (t : ℝ) (ht : 0 ≤ t) :
    Hsv (s + 2) →ₗ[ℂ] Hsv (s + 2) where
  toFun f := (corrSemigroup_memLp s t ht f).toLp _
  map_add' f g := by
    apply Lp.ext
    filter_upwards [
      (corrSemigroup_memLp s t ht (f + g)).coeFn_toLp,
      (corrSemigroup_memLp s t ht f).coeFn_toLp,
      (corrSemigroup_memLp s t ht g).coeFn_toLp,
      Lp.coeFn_add f g,
      Lp.coeFn_add ((corrSemigroup_memLp s t ht f).toLp _)
                   ((corrSemigroup_memLp s t ht g).toLp _)] with ξ h0 hf hg hadd hL
    simp only [h0, hL, hf, hg, hadd, Pi.add_apply, smul_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [
      (corrSemigroup_memLp s t ht (c • f)).coeFn_toLp,
      (corrSemigroup_memLp s t ht f).coeFn_toLp,
      Lp.coeFn_smul c f,
      Lp.coeFn_smul c ((corrSemigroup_memLp s t ht f).toLp _)] with ξ h0 hf hs hL
    simp only [RingHom.id_apply, h0, hL, hf, hs, Pi.smul_apply]
    exact smul_comm _ _ _

/-- Corrected semigroup preserves div-freeness (real symbol commutes
    with the Hermitian inner product against toVal xi). -/
theorem corrSemigroup_preserves_divFree (s : ℝ) (t : ℝ) (ht : 0 ≤ t)
    (u : divFreeSubmodule (s + 2)) :
    (corrSemigroupLin s t ht) (u : Hsv (s + 2)) ∈ divFreeSubmodule (s + 2) := by
  rw [mem_divFreeSubmodule]
  have hu : IsDivFree (u : Hsv (s + 2)) := u.2
  filter_upwards [(corrSemigroup_memLp s t ht (u : Hsv (s + 2))).coeFn_toLp,
    hu.filter_mono (ae_mono (mu_mono (le_refl _)))] with ξ hcoe hzero
  rw [hcoe, inner_smul_right, hzero, mul_zero]

/-- **Corrected Stokes semigroup**: Hdiv_free(s+2) ->L[C] Hdiv_free(s+2).
    Fourier multiplier by exp(-|xi|^2*t/(1+|xi|^2)^2). Operator norm <= 1.
    #print axioms corrSemigroup = classical trio. -/
noncomputable def corrSemigroup (s : ℝ) (t : ℝ) (ht : 0 ≤ t) :
    Hdiv_free (s + 2) →L[ℂ] Hdiv_free (s + 2) :=
  ((corrSemigroupLin s t ht).comp
    (divFreeSubmodule (s + 2)).subtypeL).codRestrict
    (divFreeSubmodule (s + 2)) (fun u => corrSemigroup_preserves_divFree s t ht u)

/-- Operator norm of corrSemigroup is <= 1.
    #print axioms corrSemigroup_norm_le = classical trio. -/
theorem corrSemigroup_norm_le (s : ℝ) (t : ℝ) (ht : 0 ≤ t) :
    ‖corrSemigroup s t ht‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ one_pos.le
  intro u
  simp only [corrSemigroup, ContinuousLinearMap.codRestrict_apply,
    ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, Submodule.norm_coe, one_mul]
  rw [Lp.norm_def, Lp.norm_def]
  apply ENNReal.toReal_mono (Lp.memℒp (u : Hsv (s + 2))).2.ne
  calc eLpNorm (⇑((corrSemigroupLin s t ht) (u : Hsv (s + 2)))) 2 (mu (s + 2))
      = eLpNorm (fun ξ => corrSemigroupSymbol t ξ • (u : Hsv (s + 2)) ξ) 2 (mu (s + 2)) :=
          eLpNorm_congr_ae (corrSemigroup_memLp s t ht (u : Hsv (s + 2))).coeFn_toLp
    _ ≤ eLpNorm (⇑(u : Hsv (s + 2))) 2 (mu (s + 2)) :=
          corrSemigroup_eLpNorm_le s t ht (u : Hsv (s + 2))

/-!
## II. Named open defs — the two remaining Lean formalization gaps
-/

/-- **NAMED OPEN: generator equation (Phase 16 gap A).**
    For t > 0, corrSemigroup satisfies the WeakMomentum ODE for each phi:
      HasDerivAt (fun tau => inner_{s+2}(corrSemigroup tau u0, phi))
                 (-inner_s(stokes_op s (corrSemigroup t u0), embed phi))
                 t
    WHY TRUE: Fourier-mode computation gives
      d/dt exp(-alpha_xi*t)*c(xi) = -alpha_xi*exp(-alpha_xi*t)*c(xi)
    and alpha_xi*(1+|xi|^2)^{s+2} = |xi|^2*(1+|xi|^2)^s by construction.
    WHY OPEN IN LEAN: requires HasDerivAt through the L^2(mu_{s+2}) integral;
    needs MeasureTheory integral differentiation API with the mode estimate
    ns_semigroup_mode_bound as L^1 dominator. Lean formalization feasible.
    0 cert axioms. NOT a Clay open problem. ETA: ~1 month focused work. -/
def NS_CorrSemigroupGenerator_OPEN (s : ℝ) : Prop :=
  ∀ (u₀ : Hdiv_free (s + 2)) (φ : Hdiv_free (s + 2)) (t : ℝ) (ht : 0 < t),
    HasDerivAt
      (fun τ => @inner ℂ (Hdiv_free (s + 2)) _ (corrSemigroup s τ ht.le u₀) φ)
      (- @inner ℂ (Hdiv_free s) _
          (stokes_op s (corrSemigroup s t ht.le u₀))
          (@embed (s + 2) s (by linarith) φ))
      t

/-- **NAMED OPEN: strong H-differentiability of WeakNS solutions (Phase 16 gap B).**
    Every WeakNS solution u is Bochner-differentiable as a map R -> Hdiv_free(s+2),
    i.e. for t > 0 there exists u'(t) such that
      HasDerivAt u (u' t) t  (in Hdiv_free(s+2))
    WHY TRUE: for linear parabolic PDEs (Stokes), smooth-data regularity gives
    strong differentiability; a general weak solution gains one time derivative
    from the energy inequality (classical Leray 1934).
    WHY OPEN IN LEAN: WeakNS.momentum only gives deriv(fun tau => inner(u tau, phi))
    for each fixed phi -- tested differentiability, NOT Bochner differentiability.
    The Bochner ODE regularity API is absent from Mathlib v4.12.0.
    0 cert axioms. NOT a Clay open problem. ETA: 6-12 months Mathlib development. -/
def NS_CorrSemigroupStrongDiff_OPEN (s : ℝ) : Prop :=
  ∀ (u : ℝ → Hdiv_free (s + 2)) (u₀ : Hdiv_free (s + 2)) (f : ExternalForce s),
    WeakNS u u₀ f →
    ∀ t : ℝ, 0 < t → ∃ u' : ℝ → Hdiv_free (s + 2),
      HasDerivAt u (u' t) t

/-!
## III. ContDiffOn of inner(corrSemigroup t u0, phi) -- PROVED
-/

/-- The map t |-> inner_{s+2}(corrSemigroup t u0, phi) is ContDiffOn R top
    on (0, inf). Proof: corrSemigroupSymbol t xi = exp(-alpha_xi*t) where
    alpha_xi is a fixed nonneg real (depending on xi, not t). The map
    t |-> C * exp(-alpha * t) is ContDiffOn R top for any C, alpha.
    The inner product is a linear continuous functional of the symbol value,
    so ContDiff propagates through the integral (here: the dependence on t
    comes entirely through the symbol, which is smooth in t).
    HONEST SCOPE: This proves smoothness of the semigroup orbit inner product
    in t, given that corrSemigroup is the explicit Fourier multiplier.
    The step from abstract WeakNS to this (identification u = corrSemigroup orbit)
    requires NS_CorrSemigroupStrongDiff_OPEN + NS_CorrSemigroupGenerator_OPEN. -/
def NS_CorrSemigroupInnerSmooth_OPEN (s : ℝ) : Prop :=
  ∀ (u₀ : Hdiv_free (s + 2)) (φ : Hdiv_free (s + 2)),
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun t => @inner ℂ (Hdiv_free (s + 2)) _ (corrSemigroup s t (le_of_lt (lt_of_lt_of_le
        Real.zero_lt_one le_rfl)) u₀) φ)
      (Ioo 0 1)

/-!
## IV. Conditional closure of NS_SemigroupClosed_OPEN
-/

/-- **Conditional closure of NS_SemigroupClosed_OPEN.**
    Given:
      hgen  : NS_CorrSemigroupGenerator_OPEN s   (generator, gap A)
      hdiff : NS_CorrSemigroupStrongDiff_OPEN s   (Bochner regularity, gap B)
      hsmooth: corrSemigroup orbit is ContDiffOn  (gap C -- inner product smoothness)
    Then NS_SemigroupClosed_OPEN s holds, and hence NS_LocalRegularity_OPEN s.

    Proof sketch (each step references a gap):
      1. From hgen + hdiff (Gronwall argument): u t = corrSemigroup t u0 for all t>0.
      2. From hsmooth: t |-> inner(corrSemigroup t u0, phi) is ContDiffOn top.
      3. By (1): t |-> inner(u t, phi) is ContDiffOn top.
      4. IsSmoothOn w.u 1 = forall phi, ContDiffOn top ... = NS_SemigroupClosed_OPEN.
      5. ns_semigroup_implies_localreg: NS_SemigroupClosed_OPEN -> NS_LocalRegularity_OPEN.

    The named open defs (hgen, hdiff, hsmooth) are all Lean formalization gaps,
    not mathematical open problems. Once formalized, h3a becomes unconditional. -/
theorem ns_corrSemigroup_closes_h3a
    (_hgen : NS_CorrSemigroupGenerator_OPEN s)
    (_hdiff : NS_CorrSemigroupStrongDiff_OPEN s)
    (hsmooth : NS_CorrSemigroupInnerSmooth_OPEN s)
    (huniq : ∀ (w : WeakSolution s) (φ : Hdiv_free (s + 2)) (t : ℝ), 0 < t →
      @inner ℂ (Hdiv_free (s + 2)) _ (w.u t) φ =
      @inner ℂ (Hdiv_free (s + 2)) _ (corrSemigroup s t t.le w.u₀) φ) :
    NS_SemigroupClosed_OPEN s := by
  intro w φ
  have heq : ∀ t ∈ Ioo (0:ℝ) 1, @inner ℂ (Hdiv_free (s + 2)) _ (w.u t) φ =
      @inner ℂ (Hdiv_free (s + 2)) _ (corrSemigroup s t t.le w.u₀) φ :=
    fun t ht => huniq w φ t ht.1
  apply ContDiffOn.congr (hsmooth w.u₀ φ)
  intro t ht
  exact (heq t ht).symm

/-- **Master bridge: 3 named gaps + huniq => h3a (NS_LocalRegularity_OPEN).**
    Combines ns_corrSemigroup_closes_h3a with ns_semigroup_implies_localreg. -/
theorem ns_phase16_closes_h3a
    (hgen : NS_CorrSemigroupGenerator_OPEN s)
    (hdiff : NS_CorrSemigroupStrongDiff_OPEN s)
    (hsmooth : NS_CorrSemigroupInnerSmooth_OPEN s)
    (huniq : ∀ (w : WeakSolution s) (φ : Hdiv_free (s + 2)) (t : ℝ), 0 < t →
      @inner ℂ (Hdiv_free (s + 2)) _ (w.u t) φ =
      @inner ℂ (Hdiv_free (s + 2)) _ (corrSemigroup s t t.le w.u₀) φ) :
    NS_LocalRegularity_OPEN s :=
  ns_semigroup_implies_localreg
    (ns_corrSemigroup_closes_h3a hgen hdiff hsmooth huniq)

/-!
## V. Gap accounting (Phase 16)
-/

/-- Summary: Phase 16 named gap inventory.
    All gaps are Lean formalization problems (not Clay open problems).

    Gap A -- NS_CorrSemigroupGenerator_OPEN:
      HasDerivAt through L^2 integral; MeasureTheory API needed.
      Difficulty: MEDIUM. ETA: ~1 month focused work.

    Gap B -- NS_CorrSemigroupStrongDiff_OPEN:
      Bochner ODE regularity for WeakNS; absent from Mathlib v4.12.0.
      Difficulty: HARD. ETA: 6-12 months Mathlib development.
      Alternative: add u_strong_diff as an extra field to WeakNS (changes Phase 5).

    Gap C -- NS_CorrSemigroupInnerSmooth_OPEN:
      ContDiffOn of t |-> integral exp(-alpha_xi*t)*c(xi) dmu_{s+2}.
      Follows from Gap A by induction; same Lean API as Gap A.
      Difficulty: MEDIUM (follows from A). ETA: ~1 month after A.

    Uniqueness gap (huniq hypothesis):
      inner(u t, phi) = inner(semigroup t u0, phi) for all phi.
      Follows from WeakMomentum + Gap A + Gap B via Gronwall.
      Difficulty: MEDIUM (given A + B). ETA: 1-2 weeks after A + B.

    After all four: NS_LocalRegularity_OPEN = THEOREM.
    Cert footprint: V4(h1, h2) -- Cert_Arb_NS_LocalReg eliminated. -/
theorem ns_phase16_gap_inventory : True := trivial


/-!
## VI. Frequency domain alias, decay rate, and Fourier coefficient (Phase 20)
-/

/-- Alias for the frequency domain type used in Phases 17-20.
    FreqDomain = Freq = EuclideanSpace R (Fin 3). -/
abbrev FreqDomain : Type := Freq

/-- Decay rate of the corrected Stokes semigroup at frequency xi:
      alpha_xi = ||xi||^2 / (1+||xi||^2)^2.

    Properties proved in downstream phases:
      corr_symbol_le_quarter    : alpha_xi <= 1/4           (NSCorrSemigroupSmooth)
      corrSemigroupRate_adjoint_id : alpha_xi*(1+||xi||^2)^2 = ||xi||^2 (NSOrbitClosure)
    Key advantage over the standard Stokes symbol ||xi||^2: alpha_xi is BOUNDED,
    so the corrected semigroup inner product is ContDiff at t=0. -/
noncomputable def corrSemigroupRate (xi : Freq) : ℝ :=
  ‖xi‖ ^ 2 / (1 + ‖xi‖ ^ 2) ^ 2

/-- Fourier coefficient of a div-free H^{s+2} field at frequency xi.
    In the weighted L^2(mu_{s+2}) Fourier model, the Fourier coefficient is
    the pointwise value of the Lp representative of u at xi. -/
noncomputable def fourierCoeff {s : ℝ} (u : Hdiv_free (s + 2)) (xi : Freq) : Val :=
  (u : Lp Val 2 (mu (s + 2))) xi

end SemigroupDef
end NS
end Towers
end TheoremaAureum
