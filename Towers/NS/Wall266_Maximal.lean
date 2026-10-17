/-
Wall266_Maximal — Hardy–Littlewood weak (1,1) from Mathlib's Vitali lemma.

Mathlib v4.12 has `Vitali.exists_disjoint_subfamily_covering_enlargment_closedBall`
and does not have the maximal inequality. The enlargement in that lemma is a
factor `τ > 3`, so the volume factor proved here is `4^3 = 64`, not `3^3`.

This file does not close `BogovskiiCZ_OPEN`. A weak (1,1) bound for the maximal
function, and Marcinkiewicz interpolation from weak (1,1) and weak (∞,∞), do
not bound `‖∇(Bogovskii ω R f)‖₂`. The truncated kernel `∇K 1_{|x-y|>ε}` has
Schur and `L∞` constants of order `log(R/ε)`.
-/

import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.Algebra.Group.Basic
import Towers.NS.Wall266_Bogovskii

open MeasureTheory Metric Set ENNReal Filter
open scoped NNReal Topology

noncomputable section

abbrev R3 := EuclideanSpace ℝ (Fin 3)

namespace TheoremaAureum.Towers.NS.Wall266Maximal

/-- Closed-ball volume scales by `τ^3` in `R3`. -/
lemma closedBall_volume_mul (x : R3) {r τ : ℝ} (_hr : 0 ≤ r) (hτ : 0 ≤ τ) :
    volume (closedBall x (τ * r)) =
      ENNReal.ofReal (τ ^ 3) * volume (closedBall x r) := by
  rw [EuclideanSpace.volume_closedBall (ι := Fin 3),
    EuclideanSpace.volume_closedBall (ι := Fin 3)]
  simp only [Fintype.card_fin]
  have hmul : ENNReal.ofReal (τ * r) = ENNReal.ofReal τ * ENNReal.ofReal r :=
    ENNReal.ofReal_mul hτ
  rw [hmul, mul_pow, ← ENNReal.ofReal_pow hτ, mul_assoc]

/-- Right translation preserves Lebesgue measure on `R3`. -/
lemma volume_map_add_right (x : R3) :
    Measure.map (fun y : R3 => y + x) (volume : Measure R3) = volume := by
  have hfun : (fun y : R3 => y + x) = fun y => x + y := by
    ext y
    exact add_comm _ _
  rw [hfun]
  exact Measure.IsAddLeftInvariant.map_add_left_eq_self (μ := (volume : Measure R3)) x

lemma preimage_add_right_closedBall (x : R3) (r : ℝ) :
    (fun y : R3 => y + x) ⁻¹' closedBall x r = closedBall 0 r := by
  ext y
  simp only [mem_preimage, mem_closedBall, dist_eq_norm, add_sub_cancel_right,
    dist_zero_right, sub_zero]

/-- Translating the center does not change the integral of an integrand. -/
lemma setIntegral_closedBall_translate (g : R3 → ℝ) (x : R3) (r : ℝ) :
    ∫ y in closedBall x r, g y ∂(volume : Measure R3) =
      ∫ y in closedBall 0 r, g (y + x) ∂(volume : Measure R3) := by
  have hA : MeasurableEmbedding (fun y : R3 => y + x) :=
    (Homeomorph.addRight x).closedEmbedding.measurableEmbedding
  have hmap := volume_map_add_right x
  calc
    ∫ y in closedBall x r, g y ∂(volume : Measure R3) =
        ∫ y in closedBall x r, g y ∂Measure.map (fun z : R3 => z + x) volume := by
          rw [hmap]
    _ = ∫ y in (fun z : R3 => z + x) ⁻¹' closedBall x r, g (y + x) ∂volume := by
          exact hA.setIntegral_map g (closedBall x r)
    _ = ∫ y in closedBall 0 r, g (y + x) ∂volume := by
          rw [preimage_add_right_closedBall]

lemma exists_abs_bound {f : R3 → ℝ} (hcont : Continuous f) (hsupp : HasCompactSupport f) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y, |f y| ≤ M := by
  have hbdd : BddAbove ((fun y => |f y|) '' tsupport f) :=
    (hsupp.image (continuous_abs.comp hcont)).bddAbove
  obtain ⟨M, hM⟩ := hbdd
  refine ⟨max M 0, le_max_right _ _, fun y => ?_⟩
  by_cases hy : y ∈ tsupport f
  · exact (hM (mem_image_of_mem _ hy)).trans (le_max_left _ _)
  · have hy0 : f y = 0 := by
      have hnot : y ∉ Function.support f := fun h => hy (subset_closure h)
      simpa [Function.mem_support] using hnot
    simp [hy0, abs_zero, le_max_right]

lemma continuous_setIntegral_closedBall_abs {f : R3 → ℝ} (hcont : Continuous f)
    (hsupp : HasCompactSupport f) {r : ℝ} (hr : 0 < r) :
    Continuous fun z : R3 => ∫ y in closedBall z r, |f y| ∂(volume : Measure R3) := by
  obtain ⟨M, hM0, hM⟩ := exists_abs_bound hcont hsupp
  have hfin : volume (closedBall (0 : R3) r) < ∞ :=
    (isCompact_closedBall (0 : R3) r).measure_lt_top
  have hbound : Integrable (fun _ : R3 => M) (volume.restrict (closedBall (0 : R3) r)) := by
    refine (integrable_const_iff).2 (Or.inr ?_)
    simpa [Measure.restrict_apply_univ] using hfin
  have hcont' : Continuous fun z : R3 =>
      ∫ y, |f (y + z)| ∂(volume.restrict (closedBall (0 : R3) r)) := by
    refine continuous_of_dominated
      (F := fun z y => |f (y + z)|)
      (bound := fun _ : R3 => M)
      (fun z => (continuous_abs.comp
        (hcont.comp ((continuous_id).add continuous_const))).aestronglyMeasurable)
      (fun z => ae_of_all _ fun y => by simpa using hM (y + z))
      hbound
      (ae_of_all _ fun y => continuous_abs.comp
        (hcont.comp (continuous_const.add continuous_id)))
  have htranslate : ∀ z, ∫ y in closedBall z r, |f y| ∂volume =
      ∫ y, |f (y + z)| ∂(volume.restrict (closedBall (0 : R3) r)) := by
    intro z
    rw [setIntegral_closedBall_translate (fun y => |f y|) z r]
  simpa [htranslate] using hcont'

/-- Points where some closed-ball average of `|f|` exceeds `lam`. -/
def HLExceeds (f : R3 → ℝ) (lam : ℝ) : Set R3 :=
  {x | ∃ r, 0 < r ∧ lam * (volume (closedBall x r)).toReal <
    ∫ y in closedBall x r, |f y| ∂(volume : Measure R3)}

lemma hlExceeds_isOpen {f : R3 → ℝ} (hcont : Continuous f) (hsupp : HasCompactSupport f)
    {lam : ℝ} : IsOpen (HLExceeds f lam) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rcases hx with ⟨r, hr, havg⟩
  let φ : R3 → ℝ := fun z => ∫ y in closedBall z r, |f y| ∂volume
  have hφ : Continuous φ := continuous_setIntegral_closedBall_abs hcont hsupp hr
  have hvol : ∀ z : R3, volume (closedBall z r) = volume (closedBall x r) := by
    intro z
    rw [EuclideanSpace.volume_closedBall (ι := Fin 3) z r,
      EuclideanSpace.volume_closedBall (ι := Fin 3) x r]
  let V : ℝ := (volume (closedBall x r)).toReal
  have hsub : φ ⁻¹' Ioi (lam * V) ⊆ HLExceeds f lam := by
    intro z hz
    refine ⟨r, hr, ?_⟩
    have hz' : lam * V < φ z := by simpa [φ] using hz
    simpa [φ, hvol z, V] using hz'
  have hmem : φ ⁻¹' Ioi (lam * V) ∈ 𝓝 x :=
    hφ.continuousAt.preimage_mem_nhds (Ioi_mem_nhds (by simpa [φ, V] using havg))
  exact mem_of_superset hmem hsub

/-- An average above `lam` bounds the ball's volume by the integral of `|f|`. -/
lemma volume_le_of_large_integral {x : R3} {r lam : ℝ} (hlam : 0 < lam) {f : R3 → ℝ}
    (hf : IntegrableOn (fun y => |f y|) (closedBall x r) (volume : Measure R3))
    (havg : lam * (volume (closedBall x r)).toReal <
      ∫ y in closedBall x r, |f y| ∂volume) :
    volume (closedBall x r) ≤
      ENNReal.ofReal lam⁻¹ *
        ∫⁻ y in closedBall x r, ENNReal.ofReal |f y| ∂volume := by
  have hfin : volume (closedBall x r) < ∞ := (isCompact_closedBall x r).measure_lt_top
  have hvle : (volume (closedBall x r)).toReal ≤
      (∫ y in closedBall x r, |f y| ∂volume) * lam⁻¹ := by
    have hlt : (volume (closedBall x r)).toReal <
        (∫ y in closedBall x r, |f y| ∂volume) / lam := by
      rw [lt_div_iff hlam]
      linarith [havg]
    simpa [div_eq_mul_inv] using (le_of_lt hlt)
  have hI : Integrable (fun y => |f y|) (volume.restrict (closedBall x r)) := hf
  have hnn : 0 ≤ᵐ[volume.restrict (closedBall x r)] fun y => |f y| :=
    ae_of_all _ fun _ => abs_nonneg _
  calc
    volume (closedBall x r) = ENNReal.ofReal (volume (closedBall x r)).toReal :=
      (ENNReal.ofReal_toReal hfin.ne).symm
    _ ≤ ENNReal.ofReal ((∫ y in closedBall x r, |f y| ∂volume) * lam⁻¹) :=
      ENNReal.ofReal_le_ofReal hvle
    _ = ENNReal.ofReal lam⁻¹ * ENNReal.ofReal (∫ y in closedBall x r, |f y| ∂volume) := by
      rw [mul_comm, ENNReal.ofReal_mul (inv_nonneg.2 hlam.le)]
    _ = ENNReal.ofReal lam⁻¹ *
        ∫⁻ y in closedBall x r, ENNReal.ofReal |f y| ∂volume := by
      rw [ofReal_integral_eq_lintegral_ofReal hI hnn]

/-- Finite Vitali bound. Every ball has closed-ball average of `|f|` above `lam`,
so the union has measure at most `64 / lam` times `∫ |f|`. -/
theorem finite_vitali_average_bound {ι : Type*} [Fintype ι] (f : R3 → ℝ) (hf : Integrable f)
    {lam : ℝ} (hlam : 0 < lam) (x : ι → R3) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (havg : ∀ i, lam * (volume (closedBall (x i) (r i))).toReal <
      ∫ y in closedBall (x i) (r i), |f y| ∂volume) :
    volume (⋃ i, closedBall (x i) (r i)) ≤
      ENNReal.ofReal ((4 : ℝ) ^ 3 / lam) * ∫⁻ y, ENNReal.ofReal |f y| ∂volume := by
  classical
  let R : ℝ := ∑ i : ι, r i + 1
  have hR : ∀ a ∈ (Set.univ : Set ι), r a ≤ R := by
    intro a _
    have hle : r a ≤ ∑ i : ι, r i :=
      Finset.single_le_sum (fun i _ => (hr i).le) (Finset.mem_univ a)
    change r a ≤ ∑ i : ι, r i + 1
    exact hle.trans (le_add_of_nonneg_right zero_le_one)
  obtain ⟨u, -, huDisj, hcover⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargment_closedBall
      (t := (Set.univ : Set ι)) (x := x) (r := r) (R := R) hR (τ := 4) (by norm_num)
  have huFin : u.Finite := Set.toFinite u
  let s : Finset ι := huFin.toFinset
  have hs_u : (s : Set ι) = u := huFin.coe_toFinset
  have hsub : (⋃ i, closedBall (x i) (r i)) ⊆
      ⋃ b ∈ s, closedBall (x b) (4 * r b) := by
    intro y hy
    obtain ⟨i, hyi⟩ := mem_iUnion.1 hy
    obtain ⟨b, hb, hbinc⟩ := hcover i (mem_univ i)
    exact mem_biUnion (huFin.mem_toFinset.2 hb) (hbinc hyi)
  have hsmall : ∀ b ∈ s, volume (closedBall (x b) (r b)) ≤
      ENNReal.ofReal lam⁻¹ * ∫⁻ y in closedBall (x b) (r b), ENNReal.ofReal |f y| ∂volume := by
    intro b _hb
    exact volume_le_of_large_integral hlam (hf.abs.integrableOn) (havg b)
  have hscale : ∀ b ∈ s, volume (closedBall (x b) (4 * r b)) =
      ENNReal.ofReal ((4 : ℝ) ^ 3) * volume (closedBall (x b) (r b)) := by
    intro b _hb
    exact closedBall_volume_mul (x b) (hr b).le (by norm_num : (0 : ℝ) ≤ 4)
  have hdisj : (s : Set ι).PairwiseDisjoint fun b => closedBall (x b) (r b) := by
    simpa [hs_u] using huDisj
  have hlint : ∑ b ∈ s, ∫⁻ y in closedBall (x b) (r b), ENNReal.ofReal |f y| ∂volume =
      ∫⁻ y in ⋃ b ∈ s, closedBall (x b) (r b), ENNReal.ofReal |f y| ∂volume := by
    symm
    exact lintegral_biUnion_finset hdisj (fun b _ => measurableSet_closedBall)
      (fun y => ENNReal.ofReal |f y|)
  calc
    volume (⋃ i, closedBall (x i) (r i)) ≤
        volume (⋃ b ∈ s, closedBall (x b) (4 * r b)) := measure_mono hsub
    _ ≤ ∑ b ∈ s, volume (closedBall (x b) (4 * r b)) := measure_biUnion_finset_le s _
    _ = ∑ b ∈ s, ENNReal.ofReal ((4 : ℝ) ^ 3) * volume (closedBall (x b) (r b)) := by
          refine Finset.sum_congr rfl hscale
    _ = ENNReal.ofReal ((4 : ℝ) ^ 3) * ∑ b ∈ s, volume (closedBall (x b) (r b)) := by
          rw [← Finset.mul_sum]
    _ ≤ ENNReal.ofReal ((4 : ℝ) ^ 3) * ∑ b ∈ s,
          ENNReal.ofReal lam⁻¹ *
            ∫⁻ y in closedBall (x b) (r b), ENNReal.ofReal |f y| ∂volume := by
          refine mul_le_mul_left' (Finset.sum_le_sum fun b hb => hsmall b hb) _
    _ = ENNReal.ofReal ((4 : ℝ) ^ 3) * ENNReal.ofReal lam⁻¹ *
          ∑ b ∈ s, ∫⁻ y in closedBall (x b) (r b), ENNReal.ofReal |f y| ∂volume := by
          rw [← Finset.mul_sum, mul_assoc]
    _ = ENNReal.ofReal ((4 : ℝ) ^ 3 / lam) *
          ∫⁻ y in ⋃ b ∈ s, closedBall (x b) (r b), ENNReal.ofReal |f y| ∂volume := by
          rw [hlint, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (4 : ℝ) ^ 3),
            show (4 : ℝ) ^ 3 * lam⁻¹ = (4 : ℝ) ^ 3 / lam by ring]
    _ ≤ ENNReal.ofReal ((4 : ℝ) ^ 3 / lam) * ∫⁻ y, ENNReal.ofReal |f y| ∂volume := by
          refine mul_le_mul_left' (setLIntegral_le_lintegral _ _) _

/-- Hardy–Littlewood weak (1,1), for continuous compactly supported scalars.
The level set is the set of centers with some closed-ball average above `lam`. -/
theorem hardy_littlewood_weak_1_1 {f : R3 → ℝ} (hcont : Continuous f)
    (hsupp : HasCompactSupport f) {lam : ℝ} (hlam : 0 < lam) :
    volume (HLExceeds f lam) ≤
      ENNReal.ofReal ((4 : ℝ) ^ 3 / lam) * ∫⁻ y, ENNReal.ofReal |f y| ∂volume := by
  have hf : Integrable f := hcont.integrable_of_hasCompactSupport hsupp
  have hopen : IsOpen (HLExceeds f lam) := hlExceeds_isOpen hcont hsupp
  have HcompactOpen : Measure.InnerRegularWRT (volume : Measure R3) IsCompact IsOpen :=
    (Measure.InnerRegularWRT.isCompact_isClosed (volume : Measure R3)).trans
      (Measure.InnerRegularWRT.of_pseudoMetrizableSpace (volume : Measure R3))
  rw [HcompactOpen.measure_eq_iSup hopen]
  refine iSup_le fun K => iSup_le fun hKU => iSup_le fun hK => ?_
  classical
  let r : {x // x ∈ K} → ℝ := fun i => Classical.choose (hKU i.2)
  have hr : ∀ i : {x // x ∈ K}, 0 < r i := fun i => (Classical.choose_spec (hKU i.2)).1
  have havg : ∀ i : {x // x ∈ K}, lam * (volume (closedBall (i : R3) (r i))).toReal <
      ∫ y in closedBall (i : R3) (r i), |f y| ∂volume :=
    fun i => (Classical.choose_spec (hKU i.2)).2
  have hcover : (K : Set R3) ⊆ ⋃ i : {x // x ∈ K}, ball (i : R3) (r i) := by
    intro y hy
    exact mem_iUnion.2 ⟨⟨y, hy⟩, mem_ball_self (hr ⟨y, hy⟩)⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun i : {x // x ∈ K} => ball (i : R3) (r i))
    (fun _ => isOpen_ball) hcover
  let ι := {i // i ∈ t}
  let xι : ι → R3 := fun i => i.1
  let rι : ι → ℝ := fun i => r i.1
  have hrι : ∀ i, 0 < rι i := fun i => hr i.1
  have havgι : ∀ i, lam * (volume (closedBall (xι i) (rι i))).toReal <
      ∫ y in closedBall (xι i) (rι i), |f y| ∂volume := fun i => havg i.1
  have hKsub : (K : Set R3) ⊆ ⋃ i : ι, closedBall (xι i) (rι i) := by
    intro y hy
    obtain ⟨i, hyi⟩ := mem_iUnion.1 (ht hy)
    obtain ⟨hi, hyball⟩ := mem_iUnion.1 hyi
    exact mem_iUnion.2 ⟨⟨i, hi⟩, ball_subset_closedBall hyball⟩
  calc
    volume K ≤ volume (⋃ i : ι, closedBall (xι i) (rι i)) := measure_mono hKsub
    _ ≤ ENNReal.ofReal ((4 : ℝ) ^ 3 / lam) * ∫⁻ y, ENNReal.ofReal |f y| ∂volume :=
      finite_vitali_average_bound f hf hlam xι rι hrι havgι

end TheoremaAureum.Towers.NS.Wall266Maximal
