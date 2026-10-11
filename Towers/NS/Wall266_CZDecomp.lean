/-
Wall266_CZDecomp — consequences of the closed-ball maximal inequality.

`hardy_littlewood_weak_1_1` bounds the set of centers where some closed-ball
average of `|f|` exceeds `lam`. For a continuous function, every point outside
that set satisfies `|f x| ≤ lam`, because shrinking-ball averages tend to
`|f x|`.

This is not a Calderón–Zygmund decomposition. Mathlib v4.12 has no dyadic
cubes and no Whitney covering, so there is no disjoint partition into cubes
`Q_j` with `∫_{Q_j} b = 0`. The gradient of `Bogovskii` is not estimated
here, and `BogovskiiCZ_OPEN` stays a proposition.
-/

import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.MeasureTheory.Measure.OpenPos
import Towers.NS.Wall266_Maximal

open MeasureTheory Metric Set ENNReal
open TheoremaAureum.Towers.NS.Wall266Maximal

namespace TheoremaAureum.Towers.NS.Wall266CZDecomp

/-- Outside the maximal level set, a continuous function is bounded by `lam`. -/
theorem abs_le_of_not_mem_HLExceeds {f : R3 → ℝ} (hcont : Continuous f) {lam : ℝ}
    (hlam : 0 < lam) {x : R3} (hx : x ∉ HLExceeds f lam) : |f x| ≤ lam := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp hcont.continuousAt ε hε
  set r : ℝ := δ / 2
  have hr : 0 < r := by positivity
  let s := closedBall x r
  have hs : MeasurableSet s := measurableSet_closedBall
  have hcompact : IsCompact s := isCompact_closedBall x r
  have hfin : volume s < ∞ := hcompact.measure_lt_top
  have hpos : 0 < volume s :=
    lt_of_lt_of_le (measure_ball_pos (volume : Measure R3) x hr) (measure_mono ball_subset_closedBall)
  set V : ℝ := (volume s).toReal
  have hV : 0 < V := ENNReal.toReal_pos hpos.ne' hfin.ne
  have hclose' : ∀ y ∈ s, |f y - f x| ≤ ε := by
    intro y hy
    have hdist : dist y x < δ := by
      have hle : dist y x ≤ δ / 2 := by simpa [s, r, mem_closedBall] using hy
      linarith
    exact (hclose hdist).le
  have hint_abs : IntegrableOn (fun y => |f y|) s volume :=
    (continuous_abs.comp hcont).continuousOn.integrableOn_compact hcompact
  have hint_sub : IntegrableOn (fun y => |f y - f x|) s volume :=
    (continuous_abs.comp (hcont.sub continuous_const)).continuousOn.integrableOn_compact hcompact
  have hint_const : IntegrableOn (fun _ : R3 => |f x|) s volume :=
    (integrableOn_const.2 (Or.inr hfin))
  have hnot : ¬ lam * V < ∫ y in s, |f y| ∂volume := by
    intro hlt
    exact hx ⟨r, hr, by simpa [s, V] using hlt⟩
  have hint_le : ∫ y in s, |f y| ∂volume ≤ lam * V := le_of_not_gt hnot
  have hpoint : ∀ y ∈ s, |f x| ≤ |f y| + |f y - f x| := by
    intro y _
    have habs : abs (abs (f y) - abs (f x)) ≤ |f y - f x| :=
      abs_abs_sub_abs_le_abs_sub (f y) (f x)
    calc
      |f x| ≤ |f y| + abs (abs (f x) - abs (f y)) := by
        simpa using (abs_add_le (abs (f y)) (abs (f x) - abs (f y)))
      _ = |f y| + abs (abs (f y) - abs (f x)) := by rw [abs_sub_comm]
      _ ≤ |f y| + |f y - f x| := by gcongr
  have hint_fx : ∫ y in s, |f x| ∂volume ≤
      ∫ y in s, |f y| ∂volume + ∫ y in s, |f y - f x| ∂volume := by
    have hsplit : ∀ y ∈ s, |f x| ≤ |f y| + |f y - f x| := hpoint
    have hsum : IntegrableOn (fun y => |f y| + |f y - f x|) s volume := hint_abs.add hint_sub
    exact (setIntegral_mono_on hint_const hsum hs hsplit).trans (integral_add hint_abs hint_sub).le
  have hsub_le : ∫ y in s, |f y - f x| ∂volume ≤ ε * V := by
    have hεint : IntegrableOn (fun _ : R3 => ε) s volume :=
      (integrableOn_const.2 (Or.inr hfin))
    have hle : ∀ y ∈ s, |f y - f x| ≤ ε := hclose'
    have hmono := setIntegral_mono_on hint_sub hεint hs hle
    simpa [setIntegral_const, smul_eq_mul, mul_comm] using hmono
  have hconst_int : ∫ y in s, |f x| ∂volume = |f x| * V := by
    simp [setIntegral_const, smul_eq_mul, mul_comm, V]
  have hmul : |f x| * V ≤ (lam + ε) * V := by
    calc
      |f x| * V = ∫ y in s, |f x| ∂volume := hconst_int.symm
      _ ≤ ∫ y in s, |f y| ∂volume + ∫ y in s, |f y - f x| ∂volume := hint_fx
      _ ≤ lam * V + ε * V := add_le_add hint_le hsub_le
      _ = (lam + ε) * V := by ring
  exact (le_of_mul_le_mul_right hmul hV).trans_eq (by ring)

/-- The maximal level set has measure at most `64 / lam` times `∫ |f|`. -/
theorem hlExceeds_measure_le {f : R3 → ℝ} (hcont : Continuous f) (hsupp : HasCompactSupport f)
    {lam : ℝ} (hlam : 0 < lam) :
    volume (HLExceeds f lam) ≤
      ENNReal.ofReal ((4 : ℝ) ^ 3 / lam) * ∫⁻ y, ENNReal.ofReal |f y| ∂volume :=
  hardy_littlewood_weak_1_1 hcont hsupp hlam

end TheoremaAureum.Towers.NS.Wall266CZDecomp
