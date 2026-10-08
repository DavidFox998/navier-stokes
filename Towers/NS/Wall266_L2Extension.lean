import Towers.NS.Wall266_TrilinearForm
import Towers.NS.NSPhase97aSobolevC2alphaClose
import Towers.NS.NSPhase104SmoothApprox -- Conditional sequence assembly, supplied witnesses below.
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace TheoremaAureum.Towers.NS.Wall266L2

open TheoremaAureum.Towers.NS.Wall266
open TheoremaAureum.Towers.NS.Phase97a
open TheoremaAureum.Towers.NS.Phase104SmoothApprox
open Filter Topology
open MeasureTheory Set
open scoped BigOperators

/-- The trace of the derivative of a vector field, written as a continuous
linear functional so that it can be passed through an integrable Bochner
integral. This is a real coordinate trace, not a divergence placeholder. -/
private noncomputable def divergenceTrace : (R3 →L[ℝ] R3) →L[ℝ] ℝ :=
  ∑ i : Fin 3, (EuclideanSpace.proj i).comp
    (ContinuousLinearMap.apply ℝ R3 (EuclideanSpace.single i 1))

private theorem divergenceTrace_apply (A : R3 →L[ℝ] R3) :
    divergenceTrace A = ∑ i : Fin 3, (A (EuclideanSpace.single i 1)) i := by
  simp [divergenceTrace, ContinuousLinearMap.sum_apply]

private theorem divClassical_eq_trace {w : R3 → R3} {x : R3}
    (hw : DifferentiableAt ℝ w x) :
    divClassical w x = divergenceTrace (fderiv ℝ w x) := by
  rw [divClassical, divergenceTrace_apply]
  apply Finset.sum_congr rfl
  intro i _
  have hi : HasFDerivAt (fun y => (w y) i)
      ((EuclideanSpace.proj i).comp (fderiv ℝ w x)) x := by
    simpa [Function.comp_def, EuclideanSpace.proj_apply] using
      ((EuclideanSpace.proj i).hasFDerivAt.comp x hw.hasFDerivAt)
  rw [hi.fderiv]
  rfl

private theorem gradient_component (f : R3 → ℝ) (x : R3) (i : Fin 3) :
    (gradient f x) i = fderiv ℝ f x (EuclideanSpace.single i 1) := by
  have hcoord : (gradient f x) i =
      inner (gradient f x) (EuclideanSpace.single i (1 : ℝ)) := by
    rw [EuclideanSpace.inner_single_right]
    simp
  rw [hcoord, gradient]
  exact InnerProductSpace.toDual_symm_apply

/-- Weak divergence is preserved by smooth compact-kernel convolution.
The input is only locally integrable, not classically differentiable.
For each output point x, use the compact scalar test y ↦ phi (x - y).
Mathlib supplies differentiation of convolution with the compact kernel;
its integrability theorem justifies commuting the continuous trace with
the integral. No invented Fubini/derivative wrapper is used.

This is a written proof against Mathlib v4.12; compilation is unverified. -/
theorem weak_div_preservation : NS_ConvolutionDivFree_OPEN := by
  intro phi v hcompact hsmooth hloc hweak
  funext x
  let L : ℝ →L[ℝ] R3 →L[ℝ] R3 := ContinuousLinearMap.lsmul ℝ ℝ
  let K : R3 → (R3 →L[ℝ] R3) := fun y =>
    (L.flip.precompR R3) (v y) (fderiv ℝ phi (x - y))
  have hphi1 : ContDiff ℝ 1 phi := hsmooth.of_le le_top
  have hK : Integrable K (volume : Measure R3) :=
    (hcompact.fderiv ℝ).convolutionExists_right (L.flip.precompR R3)
      hloc (hphi1.continuous_fderiv le_rfl) x
  have hmoll : mollify phi v =
      MeasureTheory.convolution v phi L.flip (volume : Measure R3) := by
    exact (MeasureTheory.convolution_flip L).symm
  have hder : HasFDerivAt (mollify phi v)
      (∫ y, K y ∂(volume : Measure R3)) x := by
    have hd := hcompact.hasFDerivAt_convolution_right L.flip hloc hphi1 x
    rw [← hmoll] at hd
    simpa only [MeasureTheory.convolution_def] using hd
  let psi : TestFunction :=
    { toFun := fun y => phi (x - y)
      smooth := hsmooth.comp (contDiff_const.sub contDiff_id)
      compact_support := hcompact.comp_homeomorph (Homeomorph.subLeft x) }
  have hpsi : ∀ y, HasFDerivAt psi.toFun (-fderiv ℝ phi (x - y)) y := by
    intro y
    have hd := (hphi1.differentiable le_rfl).differentiableAt.hasFDerivAt.comp y
      ((hasFDerivAt_const x y).sub (hasFDerivAt_id y))
    convert hd using 1
    ext z
    simp
  have hgrad : ∀ y i, (gradTest psi y) i =
      -(fderiv ℝ phi (x - y) (EuclideanSpace.single i 1)) := by
    intro y i
    rw [gradTest, gradient_component, (hpsi y).fderiv]
    rfl
  have htrace : ∀ y, divergenceTrace (K y) =
      -(∑ i : Fin 3, (v y) i * (gradTest psi y) i) := by
    intro y
    rw [divergenceTrace_apply]
    change (∑ i : Fin 3,
      (fderiv ℝ phi (x - y) (EuclideanSpace.single i 1)) * (v y) i) =
      -(∑ i : Fin 3, (v y) i * (gradTest psi y) i)
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [hgrad y i]
    ring
  calc
    divClassical (mollify phi v) x =
        divergenceTrace (fderiv ℝ (mollify phi v) x) :=
      divClassical_eq_trace hder.differentiableAt
    _ = divergenceTrace (∫ y, K y ∂(volume : Measure R3)) := by rw [hder.fderiv]
    _ = ∫ y, divergenceTrace (K y) ∂(volume : Measure R3) :=
      (divergenceTrace.integral_comp_comm hK).symm
    _ = ∫ y, -(∑ i : Fin 3, (v y) i * (gradTest psi y) i)
        ∂(volume : Measure R3) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall htrace
    _ = -(∫ y, (∑ i : Fin 3, (v y) i * (gradTest psi y) i)
        ∂(volume : Measure R3)) := integral_neg _
    _ = 0 := by rw [hweak psi, neg_zero]

/-- Genuine L2 translations of the componentwise equivalence classes.
This does not assume that chosen representatives are pointwise continuous. -/
noncomputable def translateL2 (v : L2VectorField) (a : R3) : L2VectorField :=
  fun i => Lp.compMeasurePreserving (fun x : R3 => x + a)
    (measurePreserving_add_right (volume : Measure R3) a) (v i)

theorem translateL2_component_norm (v : L2VectorField) (a : R3) (i : Fin 3) :
    ‖translateL2 v a i‖ = ‖v i‖ :=
  Lp.norm_compMeasurePreserving _ _

/-- Norm-topology continuity of L2 translation, using the pinned Lp
measure-preserving composition theorem. This is one ingredient for the
remaining approximate-identity proof, not the approximation theorem itself. -/
theorem translateL2_continuous (v : L2VectorField) :
    Continuous (translateL2 v) := by
  letI : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
  let shifts : C(R3, C(R3, R3)) :=
    (ContinuousMap.mk (fun p : R3 × R3 => p.2 + p.1)
      (continuous_snd.add continuous_fst)).curry
  apply continuous_pi
  intro i
  exact (continuous_const : Continuous (fun _ : R3 => v i)).compMeasurePreservingLp
    shifts.continuous
    (fun a => measurePreserving_add_right (volume : Measure R3) a) (by simp)

theorem translateL2_zero (v : L2VectorField) : translateL2 v 0 = v := by
  funext i
  apply Lp.ext
  simpa only [translateL2, Function.comp_apply, add_zero] using
    (Lp.coeFn_compMeasurePreserving (v i)
      (measurePreserving_add_right (volume : Measure R3) (0 : R3)))

/-- The repository's L2VectorField uses the finite-product sup norm.
Translation preserves that norm because it preserves every L2 component. -/
theorem translateL2_norm (v : L2VectorField) (a : R3) :
    ‖translateL2 v a‖ = ‖v‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg v)).2
    intro i
    rw [translateL2_component_norm]
    exact norm_le_pi_norm v i
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (translateL2 v a))).2
    intro i
    rw [← translateL2_component_norm v a i]
    exact norm_le_pi_norm (translateL2 v a) i

/-- A genuine smooth bump at each positive scale, with inner radius half
the outer radius. Mathlib constructs the underlying function on R3.
We normalize its actual volume integral rather than assuming an unproved
Jacobian/scaling wrapper or using the zero cutoff from the Bogovskii scaffold. -/
noncomputable def normalizedBump (n : ℕ) : ContDiffBump (0 : R3) where
  rIn := mollifierScale n / 2
  rOut := mollifierScale n
  rIn_pos := div_pos (mollifierScale_pos n) (by norm_num)
  rIn_lt_rOut := by linarith [mollifierScale_pos n]

/-- All normalized-kernel fields are constructed, not assumed.
The ball radius is 1/(n+1), so n=0 is also well-defined. -/
noncomputable def normalizedMollifiers : NormalizedMollifierSequence where
  kernel n := (normalizedBump n).normed (volume : Measure R3)
  compact_support n := (normalizedBump n).hasCompactSupport_normed
  smooth n := (normalizedBump n).contDiff_normed
  nonnegative n x := (normalizedBump n).nonneg_normed x
  integral_one n := (normalizedBump n).integral_normed
  support_bound n x hx := by
    have hball : x ∈ Metric.ball (0 : R3) (mollifierScale n) := by
      rw [← show (normalizedBump n).rOut = mollifierScale n from rfl]
      rw [← (normalizedBump n).support_normed_eq (μ := (volume : Measure R3))]
      exact hx
    exact (show ‖x‖ < mollifierScale n by
      simpa only [Metric.mem_ball, dist_zero_right] using hball).le

theorem mollifierKernel_integrable (n : ℕ) :
    Integrable (normalizedMollifiers.kernel n) (volume : Measure R3) :=
  (normalizedBump n).integrable_normed

/-- The real L1 norm is the norm of the corresponding Mathlib L1 class,
not a new informal subscript notation. -/
theorem mollifierKernel_L1_norm (n : ℕ) :
    ‖(mollifierKernel_integrable n).toL1 (normalizedMollifiers.kernel n)‖ = 1 := by
  rw [L1.norm_of_fun_eq_integral_norm]
  calc
    (∫ x, ‖normalizedMollifiers.kernel n x‖ ∂(volume : Measure R3)) =
        ∫ x, normalizedMollifiers.kernel n x ∂(volume : Measure R3) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        show ‖normalizedMollifiers.kernel n x‖ = normalizedMollifiers.kernel n x
        rw [Real.norm_eq_abs, abs_of_nonneg (normalizedMollifiers.nonnegative n x)]
    _ = 1 := normalizedMollifiers.integral_one n

theorem mollifierScale_tendsto_zero :
    Tendsto mollifierScale atTop (nhds (0 : ℝ)) := by
  change Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (nhds (0 : ℝ))
  exact tendsto_inv_atTop_zero.comp
    (tendsto_atTop_add_const_right atTop (1 : ℝ)
      (tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop))

/-- A Bochner average IN L2VectorField of its translated equivalence classes.
This is distinct from the pointwise R3-valued convolution until the
almost-everywhere identification in the density proof is established. -/
noncomputable def mollifierL2Average (v : L2VectorField) (n : ℕ) : L2VectorField :=
  MeasureTheory.convolution (normalizedMollifiers.kernel n) (translateL2 v)
    (ContinuousLinearMap.lsmul ℝ ℝ) (volume : Measure R3) (0 : R3)

theorem mollifierL2Average_integral (v : L2VectorField) (n : ℕ) :
    mollifierL2Average v n =
      ∫ y, normalizedMollifiers.kernel n y • translateL2 v (-y)
        ∂(volume : Measure R3) := by
  simp only [mollifierL2Average, MeasureTheory.convolution_def,
    ContinuousLinearMap.lsmul_apply, zero_sub]

theorem mollifierL2Average_integrable (v : L2VectorField) (n : ℕ) :
    Integrable (fun y => normalizedMollifiers.kernel n y • translateL2 v (-y))
      (volume : Measure R3) := by
  have hc : Continuous
      (fun y => normalizedMollifiers.kernel n y • translateL2 v (-y)) :=
    (normalizedBump n).continuous_normed.smul
      ((translateL2_continuous v).comp continuous_neg)
  exact hc.integrable_of_hasCompactSupport
    (normalizedMollifiers.compact_support n).smul_right

/-- Minkowski and translation isometry give contraction for the actual
L2-valued average. No membership of the pointwise convolution is assumed. -/
theorem mollifierL2Average_norm_le (v : L2VectorField) (n : ℕ) :
    ‖mollifierL2Average v n‖ ≤ ‖v‖ := by
  rw [mollifierL2Average_integral]
  calc
    ‖∫ y, normalizedMollifiers.kernel n y • translateL2 v (-y)
        ∂(volume : Measure R3)‖ ≤
        ∫ y, ‖normalizedMollifiers.kernel n y • translateL2 v (-y)‖
          ∂(volume : Measure R3) := norm_integral_le_integral_norm _
    _ = ∫ y, normalizedMollifiers.kernel n y * ‖v‖
        ∂(volume : Measure R3) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => by
        show ‖normalizedMollifiers.kernel n y • translateL2 v (-y)‖ =
          normalizedMollifiers.kernel n y * ‖v‖
        rw [norm_smul, Real.norm_eq_abs, translateL2_norm,
          abs_of_nonneg (normalizedMollifiers.nonnegative n y)]
    _ = ‖v‖ := by
      rw [integral_mul_right, normalizedMollifiers.integral_one, one_mul]

/-- Apply Mathlib's shrinking normalized-bump theorem to the continuous
Banach-valued translation map. This is norm-topology convergence in L2,
not pointwise or merely almost-everywhere convergence of representatives. -/
theorem mollifierL2Average_tendsto (v : L2VectorField) :
    Tendsto (mollifierL2Average v) atTop (nhds v) := by
  have h : Tendsto (mollifierL2Average v) atTop (nhds (translateL2 v 0)) :=
    ContDiffBump.convolution_tendsto_right_of_continuous
      (φ := normalizedBump) (μ := (volume : Measure R3))
      mollifierScale_tendsto_zero (translateL2_continuous v) (0 : R3)
  simpa only [translateL2_zero] using h

theorem mollifierL2Average_norm_sub_tendsto (v : L2VectorField) :
    Tendsto (fun n => ‖mollifierL2Average v n - v‖) atTop (nhds (0 : ℝ)) := by
  have h := (mollifierL2Average_tendsto v).sub
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => v) atTop (nhds v))
  simpa only [sub_self, norm_zero] using h.norm

private theorem mollify_component_integral (v : L2VectorField)
    (n : ℕ) (i : Fin 3) (x : R3) :
    (mollify (normalizedMollifiers.kernel n) (L2Representative v) x) i =
      ∫ y, normalizedMollifiers.kernel n y * v i (x - y)
        ∂(volume : Measure R3) := by
  have hi : Integrable
      (fun y => (ContinuousLinearMap.lsmul ℝ ℝ)
        (normalizedMollifiers.kernel n y) (L2Representative v (x - y)))
      (volume : Measure R3) :=
    (normalizedMollifiers.compact_support n).convolutionExistsLeft
      (ContinuousLinearMap.lsmul ℝ ℝ) (normalizedMollifiers.smooth n).continuous
      (L2Representative_locallyIntegrable v) x
  unfold mollify
  rw [MeasureTheory.convolution_def]
  change (EuclideanSpace.proj i) (∫ y,
    (ContinuousLinearMap.lsmul ℝ ℝ) (normalizedMollifiers.kernel n y)
      (L2Representative v (x - y)) ∂(volume : Measure R3)) = _
  rw [← (EuclideanSpace.proj i).integral_comp_comm hi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    change normalizedMollifiers.kernel n y * (L2Representative v (x - y)) i =
      normalizedMollifiers.kernel n y * v i (x - y)
    rw [L2Representative_apply]

/-- Identify the average by bounded L2 functionals: integration over each
compact set is pairing with its L2 indicator. Fubini is applied only after
cutting the INPUT to a compact set containing s - tsupport(kernel).
This cutoff is solely an integrability device for Fubini, not a cutoff of
the approximating field and not a Bogovskii correction. -/
private theorem mollifierL2Average_setIntegral_eq (v : L2VectorField)
    (n : ℕ) (i : Fin 3) (s : Set R3) (hs : IsCompact s) :
    (∫ x in s, (mollifierL2Average v n i) x ∂(volume : Measure R3)) =
      ∫ x in s, (mollify (normalizedMollifiers.kernel n) (L2Representative v) x) i
        ∂(volume : Measure R3) := by
  have hμs : (volume : Measure R3) s ≠ ⊤ := hs.measure_lt_top.ne
  let test : Lp ℝ 2 (volume : Measure R3) :=
    MeasureTheory.indicatorConstLp 2 hs.measurableSet hμs (1 : ℝ)
  let Q : L2VectorField →L[ℝ] ℝ :=
    (innerSL ℝ test).comp (ContinuousLinearMap.proj i)
  have htest (u : L2VectorField) :
      Q u = ∫ x in s, (u i) x ∂(volume : Measure R3) := by
    change (inner test (u i) : ℝ) = _
    simpa only [RCLike.inner_apply, map_one, one_mul] using
      (L2.inner_indicatorConstLp_eq_setIntegral_inner ℝ (u i)
        hs.measurableSet (1 : ℝ) hμs)
  let t : Set R3 := (fun p : R3 × R3 => p.1 - p.2) ''
    (s ×ˢ tsupport (normalizedMollifiers.kernel n))
  have ht : IsCompact t :=
    (hs.prod (normalizedMollifiers.compact_support n)).image
      (continuous_fst.sub continuous_snd)
  let w : R3 → ℝ := t.indicator (fun x => v i x)
  have hloc : LocallyIntegrable (fun x => v i x) (volume : Measure R3) :=
    (Lp.memℒp (v i)).locallyIntegrable (by norm_num)
  have hw : Integrable w (volume : Measure R3) :=
    (hloc.integrableOn_isCompact ht).integrable_indicator ht.measurableSet
  have hcut (x : R3) (hxs : x ∈ s) (y : R3) :
      normalizedMollifiers.kernel n y * v i (x - y) =
        normalizedMollifiers.kernel n y * w (x - y) := by
    by_cases hy : normalizedMollifiers.kernel n y = 0
    · simp only [hy, zero_mul]
    · have hyt : y ∈ tsupport (normalizedMollifiers.kernel n) := by
        exact subset_closure hy
      have hxy : x - y ∈ t := ⟨(x, y), ⟨hxs, hyt⟩, rfl⟩
      simp only [w, Set.indicator_of_mem hxy]
  have hprod : Integrable
      (fun p : R3 × R3 => normalizedMollifiers.kernel n p.2 * w (p.1 - p.2))
      ((volume : Measure R3).prod (volume : Measure R3)) :=
    (mollifierKernel_integrable n).convolution_integrand
      (ContinuousLinearMap.lsmul ℝ ℝ) hw
  have hprod_s : Integrable
      (fun p : R3 × R3 => normalizedMollifiers.kernel n p.2 * w (p.1 - p.2))
      (((volume : Measure R3).restrict s).prod (volume : Measure R3)) := by
    have h : IntegrableOn
        (fun p : R3 × R3 => normalizedMollifiers.kernel n p.2 * w (p.1 - p.2))
        (s ×ˢ (Set.univ : Set R3))
        ((volume : Measure R3).prod (volume : Measure R3)) := hprod.integrableOn
    simpa only [IntegrableOn, ← Measure.prod_restrict, Measure.restrict_univ] using h
  calc
    (∫ x in s, (mollifierL2Average v n i) x ∂(volume : Measure R3)) =
        Q (mollifierL2Average v n) := (htest _).symm
    _ = ∫ y, Q (normalizedMollifiers.kernel n y • translateL2 v (-y))
        ∂(volume : Measure R3) := by
      rw [mollifierL2Average_integral]
      exact (Q.integral_comp_comm (mollifierL2Average_integrable v n)).symm
    _ = ∫ y, normalizedMollifiers.kernel n y *
        (∫ x in s, v i (x - y) ∂(volume : Measure R3))
        ∂(volume : Measure R3) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => by
        show Q (normalizedMollifiers.kernel n y • translateL2 v (-y)) = _
        rw [Q.map_smul, smul_eq_mul, htest (translateL2 v (-y))]
        change normalizedMollifiers.kernel n y *
          (∫ x in s, (translateL2 v (-y) i) x ∂(volume : Measure R3)) = _
        congr 1
        apply integral_congr_ae
        apply ae_restrict_of_ae
        simpa only [translateL2, Function.comp_def, sub_eq_add_neg] using
          (Lp.coeFn_compMeasurePreserving (v i)
            (measurePreserving_add_right (volume : Measure R3) (-y)))
    _ = ∫ y, ∫ x in s, normalizedMollifiers.kernel n y * w (x - y)
        ∂(volume : Measure R3) ∂(volume : Measure R3) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => by
        simp only [← integral_mul_left]
        apply setIntegral_congr_ae hs.measurableSet
        exact Filter.Eventually.of_forall fun x hxs => hcut x hxs y
    _ = ∫ x in s, ∫ y, normalizedMollifiers.kernel n y * w (x - y)
        ∂(volume : Measure R3) ∂(volume : Measure R3) :=
      (integral_integral_swap hprod_s).symm
    _ = ∫ x in s,
        (mollify (normalizedMollifiers.kernel n) (L2Representative v) x) i
        ∂(volume : Measure R3) := by
      apply setIntegral_congr_ae hs.measurableSet
      exact Filter.Eventually.of_forall fun x hxs => by
        rw [mollify_component_integral]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun y => (hcut x hxs y).symm

/-- The pointwise convolution agrees almost everywhere with the L2-valued
Bochner average. Evaluation of an arbitrary L2 representative is not a
bounded functional; compact-set integration is. Local integral uniqueness
turns the preceding bounded-functional identities into a.e. equality.
All arguments here are written proofs; compilation remains unverified. -/
theorem mollifierL2Average_representation (v : L2VectorField)
    (n : ℕ) (i : Fin 3) :
    (mollifierL2Average v n i : R3 → ℝ) =ᵐ[(volume : Measure R3)]
      (fun x => (mollify (normalizedMollifiers.kernel n) (L2Representative v) x) i) := by
  let f : R3 → ℝ := fun x =>
    (mollify (normalizedMollifiers.kernel n) (L2Representative v) x) i
  have havg : LocallyIntegrable
      (mollifierL2Average v n i : R3 → ℝ) (volume : Measure R3) :=
    (Lp.memℒp (mollifierL2Average v n i)).locallyIntegrable (by norm_num)
  have hsmooth : ContDiff ℝ ⊤
      (mollify (normalizedMollifiers.kernel n) (L2Representative v)) :=
    NS_ConvolutionSmooth_PROVED _ _ (normalizedMollifiers.compact_support n)
      (normalizedMollifiers.smooth n) (L2Representative_locallyIntegrable v)
  have hf : LocallyIntegrable f (volume : Measure R3) :=
    ((EuclideanSpace.proj i).continuous.comp hsmooth.continuous).locallyIntegrable
  have hzero : (fun x => (mollifierL2Average v n i) x - f x)
      =ᵐ[(volume : Measure R3)] 0 :=
    ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero' (havg.sub hf) (by
      intro s hs
      rw [integral_sub (havg.integrableOn_isCompact hs) (hf.integrableOn_isCompact hs),
        mollifierL2Average_setIntegral_eq v n i s hs]
      exact sub_self _)
  exact hzero.mono fun x hx => sub_eq_zero.mp hx

theorem mollifiedL2_component_mem (v : L2VectorField) (n : ℕ) (i : Fin 3) :
    Memℒp
      (fun x => (mollify (normalizedMollifiers.kernel n) (L2Representative v) x) i)
      2 (volume : Measure R3) :=
  (memℒp_congr_ae (mollifierL2Average_representation v n i)).1
    (Lp.memℒp (mollifierL2Average v n i))

/-- L2 equivalence classes of the very pointwise convolution used by
Phase104, with its membership now proved rather than assumed. -/
noncomputable def mollifiedL2 (v : L2VectorField) (n : ℕ) : L2VectorField :=
  convolutionL2 (normalizedMollifiers.kernel n) v (mollifiedL2_component_mem v n)

theorem mollifiedL2_eq_average (v : L2VectorField) (n : ℕ) :
    mollifiedL2 v n = mollifierL2Average v n := by
  funext i
  apply Lp.ext
  exact (mollifiedL2_component_mem v n i).coeFn_toLp.trans
    (mollifierL2Average_representation v n i).symm

theorem mollifiedL2_norm_le (v : L2VectorField) (n : ℕ) :
    ‖mollifiedL2 v n‖ ≤ ‖v‖ := by
  rw [mollifiedL2_eq_average]
  exact mollifierL2Average_norm_le v n

theorem mollifiedL2_norm_sub_tendsto (v : L2VectorField) :
    Tendsto (fun n => ‖mollifiedL2 v n - v‖) atTop (nhds (0 : ℝ)) := by
  simpa only [mollifiedL2_eq_average] using mollifierL2Average_norm_sub_tendsto v

/-- Path A common-sequence construction from explicit analytic witnesses.
Smoothness uses the written Mathlib proof, and both the weak-divergence and
L2 approximation witnesses have written proofs above. Phase104
assembles actual convolution fields from a single normalized kernel sequence,
whose support radii are 1 / (n + 1), and embeds their components into Lp.
This assembly alone proves neither hypothesis and introduces no new axiom. -/
theorem L2DivFree_dense_smooth_of_mollifier_bridges
    (hDivFree : NS_ConvolutionDivFree_OPEN)
    (hL2Conv : NS_ConvolutionL2Conv_OPEN) :
    ∀ v : L2DivFree, ∃ v_n : ℕ → TestVectorField,
      (∀ n, divClassical (v_n n) = 0) ∧
      Tendsto (fun n => ‖L2_of_smooth (v_n n) - v.val‖) atTop (nhds 0) :=
  NS_Carleman_SmoothApprox_PROVED NS_ConvolutionSmooth_PROVED hDivFree hL2Conv

-- Step 2a: written unconditional Path A density proof.
-- Smoothness, weak-divergence preservation and common-sequence assembly have
-- written proofs. Normalized kernels and L2-valued average estimates/convergence
-- and identification with pointwise convolution are written above.
-- Compilation has not been run; zero source admissions is not certification.
theorem L2DivFree_dense_smooth : ∀ v : L2DivFree,
  ∃ (v_n : ℕ → TestVectorField),
  (∀ n, divClassical (v_n n) = 0) ∧
  Tendsto (fun n => ‖L2_of_smooth (v_n n) - v.val‖) atTop (nhds 0) := by
  have hDivFree : NS_ConvolutionDivFree_OPEN := weak_div_preservation
  have hL2Conv : NS_ConvolutionL2Conv_OPEN := by
    intro v
    exact ⟨({
      mollifiers := normalizedMollifiers
      component_L2 := mollifiedL2_component_mem v
      converges := mollifiedL2_norm_sub_tendsto v
    } : L2MollifierApproximation v)⟩
  exact L2DivFree_dense_smooth_of_mollifier_bridges hDivFree hL2Conv

-- Step 2b: OPEN analytic extension of trilinearSmooth from a dense set.
noncomputable def trilinearForm : L2DivFree → L2DivFree → L2DivFree → ℝ :=
  fun u v w =>
    -- Intended analytic construction, not implemented:
    -- b(u,v,w) = lim_{n→∞} b_smooth(u_n, v_n, w_n) where u_n→u, v_n→v, w_n→w
    -- Limit exists because |b_smooth| ≤ C ‖u_n‖_{L²} ‖∇v_n‖_{L∞} ‖w_n‖_{L²}
    -- and ‖∇v_n‖_{L∞} ≤ C_S ‖v_n‖_{H⁴} ≤ C_S' ‖v‖_{H⁴} by Phase 97a
    0 -- Zero placeholder; no Cauchy-sequence extension is constructed here.
    -- OPEN: the analytic extension needs density and the appropriate norm estimates.

instance : TopologicalSpace L2DivFree := by
  unfold L2DivFree
  infer_instance

theorem trilinearForm_continuous (u v : L2DivFree) :
  Continuous (fun w : L2DivFree => trilinearForm u v w) := by
  simp [trilinearForm]
  exact continuous_const

-- Step 2c: Closed zero-form bound only: |0| ≤ C ‖w‖.
-- This is not a bound for the unconstructed analytic trilinear form.
theorem trilinearForm_bound (v : L2DivFree) (hSym : Is120CellSymmetric v) :
  ∃ C, C = H4_BKM_constant * sobolevConstant_H4 ∧
  ∀ w : L2DivFree, |trilinearForm v v w| ≤ C * ‖w‖ := by
  use H4_BKM_constant * sobolevConstant_H4
  constructor
  · rfl
  · intro w
    simp only [trilinearForm, abs_zero]
    -- Need 0 ≤ C * ‖w‖
    have hC_nonneg : 0 ≤ H4_BKM_constant * sobolevConstant_H4 :=
      mul_nonneg H4_BKM_constant_pos.le sobolevConstant_H4_pos.le
    have hnorm : 0 ≤ ‖w‖ := by
      change 0 ≤ ‖w.val‖
      exact norm_nonneg _
    exact mul_nonneg hC_nonneg hnorm

-- Step 2d: A derived constant estimate for the same zero placeholder only.
theorem H4_controls_trilinear_REAL (v : L2DivFree) (hSym : Is120CellSymmetric v) :
  ∃ C, C = H4_BKM_constant * sobolevConstant_H4 ∧ C < 11 * sobolevConstant_H4 ∧
  ∀ w : L2DivFree, |trilinearForm v v w| ≤ C * ‖w‖ := by
  have hBound := trilinearForm_bound v hSym
  obtain ⟨C, hCeq, hBound'⟩ := hBound
  use C
  constructor
  · exact hCeq
  constructor
  · calc C = H4_BKM_constant * sobolevConstant_H4 := hCeq
        _ < 11 * sobolevConstant_H4 := by
          have : H4_BKM_constant < 11 := H4_BKM_constant_lt_11
          have : 0 < sobolevConstant_H4 := sobolevConstant_H4_pos
          nlinarith
  · exact hBound'

end TheoremaAureum.Towers.NS.Wall266L2
