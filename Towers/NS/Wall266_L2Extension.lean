import Towers.NS.Wall266_TrilinearForm
import Towers.NS.NSPhase97aSobolevC2alphaClose
import Towers.NS.NSPhase104SmoothApprox -- L2 approximation remains conditional.
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.Tactic.Ring

namespace TheoremaAureum.Towers.NS.Wall266L2

open TheoremaAureum.Towers.NS.Wall266
open TheoremaAureum.Towers.NS.Phase97a
open TheoremaAureum.Towers.NS.Phase104SmoothApprox
open Filter Topology
open MeasureTheory
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
      ((EuclideanSpace.proj i).comp (fderiv ℝ w x)) x :=
    (EuclideanSpace.proj i).hasFDerivAt.comp x hw.hasFDerivAt
  rw [hi.fderiv]
  rfl

private theorem gradient_component (f : R3 → ℝ) (x : R3) (i : Fin 3) :
    (gradient f x) i = fderiv ℝ f x (EuclideanSpace.single i 1) := by
  simpa [gradient, EuclideanSpace.inner_single_right] using
    (InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := R3)
      (x := EuclideanSpace.single i 1) (y := fderiv ℝ f x))

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
  letI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  let shifts : C(R3, C(R3, R3)) :=
    (ContinuousMap.mk (fun p : R3 × R3 => p.2 + p.1)
      (continuous_snd.add continuous_fst)).curry
  apply continuous_pi
  intro i
  exact (continuous_const : Continuous (fun _ : R3 => v i)).compMeasurePreservingLp
    shifts.continuous
    (fun a => measurePreserving_add_right (volume : Measure R3) a) (by simp)

/-- Path A common-sequence construction from explicit analytic witnesses.
Smoothness uses the written Mathlib proof, and the weak-divergence witness
has a written proof above. L2 approximation is still OPEN. Phase104
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

-- Step 2a: unconditional Path A density is still OPEN.
-- Smoothness, weak-divergence preservation and common-sequence assembly have
-- written proofs. The L2 approximation obligation remains a genuine proof gap,
-- not merely an API name or a Bogovskii dependency.
-- Compilation has not been run; a smaller admission count is not certification.
theorem L2DivFree_dense_smooth : ∀ v : L2DivFree,
  ∃ (v_n : ℕ → TestVectorField),
  (∀ n, divClassical (v_n n) = 0) ∧
  Tendsto (fun n => ‖L2_of_smooth (v_n n) - v.val‖) atTop (nhds 0) := by
  have hDivFree : NS_ConvolutionDivFree_OPEN := weak_div_preservation
  have hL2Conv : NS_ConvolutionL2Conv_OPEN := by
    sorry -- OPEN: normalized kernel construction, L2 estimates and norm convergence.
    -- A bound by 2 * ‖v‖ is not convergence to zero.
    -- Pinned Mathlib has continuity of measure-preserving composition on Lp
    -- (ContinuousCompMeasurePreserving), but not the proposed named
    -- `tendsto_mollifier_approx_L2` or `Young_inequality_L2` wrappers.
    -- `translateL2_continuous` and `translateL2_component_norm` above supply
    -- the translation ingredients. Still needed: normalized kernel existence,
    -- identify actual convolution with an Lp-valued average, prove its L2
    -- estimates, and deduce convergence as the kernel supports shrink.
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

theorem trilinearForm_continuous (u v : L2DivFree) :
  Continuous (fun w : L2DivFree => trilinearForm u v w) := by
  -- trilinearForm currently = fun _ _ _ => 0, so Continuous trivially
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
    have hC_nonneg : 0 ≤ H4_BKM_constant * sobolevConstant_H4 := by
      -- H4_BKM_constant = (1+phi)/(2-phi)/5 >0, sobolevConstant_H4 = π/(4√2) >0
      unfold H4_BKM_constant sobolevConstant_H4
      positivity -- phi>0, 2-phi>0, pi>0, sqrt 2 >0
    have : 0 ≤ (H4_BKM_constant * sobolevConstant_H4) * ‖w‖ := by
      apply mul_nonneg hC_nonneg (norm_nonneg _)
    linarith

-- Step 2d: A derived constant estimate for the same zero placeholder only.
theorem H4_controls_trilinear_REAL (v : L2DivFree) (hSym : Is120CellSymmetric v) :
  ∃ C, C = H4_BKM_constant * sobolevConstant_H4 ∧ C < 11 * sobolevConstant_H4 ∧
  ∀ w : L2DivFree, |trilinearForm v v w| ≤ C * ‖w‖ := by
  have hBound := trilinearForm_bound v hSym
  obtain ⟨C, hCeq, hBound'⟩ := hBound
  use C
  constructor
  · rfl
  constructor
  · calc C = H4_BKM_constant * sobolevConstant_H4 := hCeq
        _ < 11 * sobolevConstant_H4 := by
          have : H4_BKM_constant < 11 := H4_BKM_constant_lt_11
          have : 0 < sobolevConstant_H4 := sobolevConstant_H4_pos
          nlinarith
  · exact hBound'

end TheoremaAureum.Towers.NS.Wall266L2
