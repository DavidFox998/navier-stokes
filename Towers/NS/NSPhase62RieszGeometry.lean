/-
================================================================
Towers / NS / NSPhase62RieszGeometry  --  NS Tower Phase 62

PHASE 62: RIESZ KERNEL GEOMETRY — CORRECTED META AI SKETCH #3

David Fox / Meta AI collaboration (July 1, 2026).
Corrective pass on Meta AI's third proof sketch for NS_RieszPotentialBound_OPEN.

------------------------------------------------------------------
CORRECTIONS TABLE (third sketch, July 1):

  (1) OPEN BALL vs CLOSED BALL:
      Meta AI: riesz_superlevel_is_ball ... = Metric.ball 0 (t^{-2/5})
      Correct: {x | t ≤ ‖x‖^{-5/2}} = Metric.closedBall 0 (t^{-2/5}) \ {0}
      Reason:  t ≤ ‖x‖^{-5/2} gives ‖x‖ ≤ t^{-2/5} (non-strict ≤, closed ball).
               x=0: (0:ℝ)^{-5/2}=0 < t, so 0 is excluded.
               Metric.ball uses strict <; superlevel uses non-strict ≤.
      Fix: use Metric.closedBall + \ {0} (§A, proved).

  (2) Real.volume_ball WRONG TYPE:
      Meta AI: Real.volume_ball (for ℝ, n=1)
      Correct: needs EuclideanSpace ball volume for ℝ³.
               Formula: volume(ball 0 r) = (4π/3) * r^3 for EuclideanSpace ℝ (Fin 3).
               Mathlib API: MeasureTheory.Measure.volume_ball for EuclideanSpace
               (exact name needs lean --run; NOT Real.volume_ball).
      Fix: NS_VolumeSuperlevel_OPEN (§B, named open def).

  (3) eLpNorm_convolution_le_of_memWLP STILL USED (third round):
      Meta AI comment: "but we avoid MemWLP, use volume_superlevel_riesz".
      Meta AI code:    apply eLpNorm_convolution_le_of_memWLP  [STILL CALLED]
      This API does NOT exist and cannot be fixed with volume_superlevel_riesz alone.
      Young's convolution for weak-type (L² * weak-L^{6/5} → L³) = HLS itself.
      Fix: NS_YoungWeakType_OPEN (§C, named open def). ETA: 4-6 weeks.

  (4) eLpNorm_lintegral_le NONEXISTENT:
      Meta AI: apply eLpNorm_lintegral_le  (Minkowski integral inequality)
      No lemma by this name in Mathlib v4.12.0.
      Close candidate: MeasureTheory.snorm_lintegral_le  (needs lean --run).
      Fix: NS_MinkowskiIntegral_OPEN (§C, named open def).

  (5) Layer-cake lintegral_Ioi_eq_lintegral NONEXISTENT:
      Meta AI: lintegral_Ioi_eq_lintegral  (layer-cake representation)
      Close candidate: MeasureTheory.lintegral_eq_lintegral_meas_lt
      (layer-cake in Mathlib v4.12.0, needs exact name from lean --run).
      Fix: NS_LayerCake_OPEN (§C, named open def).

  (6) eLpNorm_two_eq_sqrt_sq / L2norm_fourier_eq / Hnorm_fourier_eq: still nonexistent.
      Fix: use eLpNorm · 2 (mu s) from FunctionSpaces directly.

WHAT IS CONFIRMED PROVABLE IN THIS FILE:
  rpow_inv_iff (§A): t ≤ a^{-5/2} ↔ a ≤ t^{-2/5}.  [proved, 0 sorry]
  riesz_superlevel_is_closedBall (§A): correct set identity. [proved, 0 sorry]

------------------------------------------------------------------
Axioms: {propext, Classical.choice, Quot.sound}
Sorry count: 0
================================================================
-/

import Towers.NS.NSPhase61HLSStructure

open Filter Topology Real MeasureTheory
open scoped BigOperators ENNReal NNReal
open TheoremaAureum.Towers.NS.FunctionSpaces
open TheoremaAureum.Towers.NS.Phase60SobolevLInf

namespace TheoremaAureum
namespace Towers
namespace NS
namespace Phase62RieszGeometry

/-! ## §A. Riesz superlevel = closed ball (proved) -/

/-- **Riesz rpow inverse iff** (proved, 0 sorry):
    t ≤ a^{-5/2} ↔ a ≤ t^{-2/5}  for a > 0, t > 0.

    Proof (both directions use the same rpow chain):
      FORWARD: t ≤ (a^{5/2})⁻¹  [rpow_neg]
        ↔ t * a^{5/2} ≤ 1        [le_div_iff]
        → (t * a^{5/2})^{2/5} ≤ 1  [rpow_le_rpow, exponent ≥ 0]
        = t^{2/5} * a ≤ 1          [mul_rpow + rpow_mul: (a^{5/2})^{2/5}=a]
        ↔ a ≤ (t^{2/5})⁻¹          [le_div_iff]
        = a ≤ t^{-2/5}             [rpow_neg]
      BACKWARD: symmetric (exponents 5/2 ↔ 2/5 swapped).

    Note: riesz_kernel_rpow_identity (Phase 61) proves (a^{5/2})^{2/5} = a.
    Both that theorem and this one use ← Real.rpow_mul.

    Lean APIs used (all confirmed v4.12.0):
      Real.rpow_neg, le_div_iff, one_div, Real.rpow_le_rpow,
      Real.mul_rpow, Real.rpow_mul, Real.rpow_one, one_rpow. -/
private lemma rpow_inv_iff (a t : ℝ) (ha : 0 < a) (ht : 0 < t) :
    t ≤ a ^ (-(5 : ℝ) / 2) ↔ a ≤ t ^ (-(2 : ℝ) / 5) := by
  have ha52 : (0 : ℝ) < a ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos ha _
  have ht25 : (0 : ℝ) < t ^ (2 / 5 : ℝ) := Real.rpow_pos_of_pos ht _
  rw [Real.rpow_neg ha.le, Real.rpow_neg ht.le]
  constructor
  · intro h
    rw [← one_div, le_div_iff ha52] at h
    rw [← one_div, le_div_iff ht25]
    have h2 := Real.rpow_le_rpow (by positivity) h (by norm_num : (0 : ℝ) ≤ 2 / 5)
    rw [Real.mul_rpow ht.le ha52.le, ← Real.rpow_mul ha.le] at h2
    simp only [show (5 / 2 : ℝ) * (2 / 5) = 1 from by norm_num,
               Real.rpow_one, one_rpow] at h2
    rw [mul_comm] at h2; exact h2
  · intro h
    rw [← one_div, le_div_iff ht25] at h
    rw [← one_div, le_div_iff ha52]
    have h2 := Real.rpow_le_rpow (by positivity) h (by norm_num : (0 : ℝ) ≤ 5 / 2)
    rw [Real.mul_rpow ha.le ht25.le, ← Real.rpow_mul ht.le] at h2
    simp only [show (2 / 5 : ℝ) * (5 / 2) = 1 from by norm_num,
               Real.rpow_one, one_rpow] at h2
    rw [mul_comm] at h2; exact h2

/-- **Riesz kernel superlevel = closed ball minus origin** (proved, 0 sorry):

    {x : ℝ³ | t ≤ ‖x‖^{-5/2}} = closedBall(0, t^{-2/5}) \ {0}.

    Corrects Meta AI's error: they used Metric.ball (open, strict <) but the
    superlevel set uses ≤ (non-strict), which gives a CLOSED ball.
    The origin is excluded: (0:ℝ)^{-5/2} = 0 (Real.zero_rpow) < t.

    For volume computation: volume(closedBall \ {0}) = volume(closedBall) = volume(ball)
    since {0} has measure zero. So the volume formula is unaffected by the open/closed
    distinction, but the SET equality requires closedBall.

    Lean APIs: rpow_inv_iff (proved above), norm_pos_iff, Real.zero_rpow,
               Metric.mem_closedBall, dist_zero_right. -/
theorem riesz_superlevel_is_closedBall (t : ℝ) (ht : 0 < t) :
    {x : EuclideanSpace ℝ (Fin 3) | t ≤ ‖x‖ ^ (-(5 : ℝ) / 2)} =
    Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (t ^ (-(2 : ℝ) / 5)) \ {0} := by
  ext x
  simp only [Set.mem_setOf_eq, Metric.mem_closedBall, dist_zero_right,
             Set.mem_diff, Set.mem_singleton_iff]
  constructor
  · intro h
    constructor
    · by_cases hx : x = 0
      · -- ‖0‖^{-5/2} = 0^{-5/2} = 0 < t: contradiction
        simp only [hx, norm_zero] at h
        rw [Real.zero_rpow (by norm_num : -(5 : ℝ) / 2 ≠ 0)] at h
        linarith
      · exact (rpow_inv_iff ‖x‖ t (norm_pos_iff.mpr hx) ht).mp h
    · intro hx0
      simp only [hx0, norm_zero] at h
      rw [Real.zero_rpow (by norm_num : -(5 : ℝ) / 2 ≠ 0)] at h
      linarith
  · intro ⟨h_le, hx0⟩
    exact (rpow_inv_iff ‖x‖ t (norm_pos_iff.mpr hx0) ht).mpr h_le

/-! ## §B. Volume formula (named open def) -/

/-- **Volume of Riesz superlevel set** (named open def, ETA 2-3 weeks):
    volume({x : ℝ³ | t ≤ ‖x‖^{-5/2}}) = (4π/3) · t^{-6/5}.

    Proof route (when EuclideanSpace.volume_ball API is confirmed):
      (1) riesz_superlevel_is_closedBall: set = closedBall(0, t^{-2/5}) \ {0}.
      (2) measure_mono_null: volume(closedBall \ {0}) = volume(closedBall).
      (3) Metric.closedBall_eq_ball_union_sphere + measure_sphere_zero (for n ≥ 1):
          volume(closedBall 0 r) = volume(ball 0 r).
      (4) EuclideanSpace.volume_ball: volume(ball 0 r) = (4π/3) · r^3 for n=3.
          r = t^{-2/5}, so r^3 = t^{-6/5}.
          ENNReal.ofReal computation closes.

    BLOCKED ON: correct Mathlib API for step (4).
      Meta AI used: Real.volume_ball  [WRONG: this is for ℝ = EuclideanSpace ℝ (Fin 1)]
      Correct API for EuclideanSpace ℝ (Fin 3):
        Likely: MeasureTheory.Measure.volume_ball  (needs lean --run to confirm).
        Formula involves: Real.pi, Gamma function at 5/2 = (3√π)/4,
        giving π^{3/2}/Γ(5/2) = π^{3/2}/(3√π/4) = 4π/3. ✓ -/
def NS_VolumeSuperlevel_OPEN : Prop :=
  ∀ t : ℝ, 0 < t →
    (volume : Measure (EuclideanSpace ℝ (Fin 3)))
        {x | t ≤ ‖x‖ ^ (-(5 : ℝ) / 2)} =
    ENNReal.ofReal (4 * Real.pi / 3 * t ^ (-(6 : ℝ) / 5))

/-! ## §C. HLS building blocks (named open defs replacing nonexistent Meta AI APIs) -/

/-- **Layer-cake representation of Lp norm** (named open def, ETA 1 week):
    |f(x)| = ∫₀^∞ 𝟙_{|f|>t}(x) dt  (layer-cake / Cavalieri).
    Lean candidate: MeasureTheory.lintegral_eq_lintegral_meas_lt
    (exact name needs lean --run; Meta AI used lintegral_Ioi_eq_lintegral, NONEXISTENT). -/
def NS_LayerCake_OPEN : Prop :=
  ∀ (f : EuclideanSpace ℝ (Fin 3) → ℂ) (x : EuclideanSpace ℝ (Fin 3)),
    ‖f x‖ = (∫⁻ t : ℝ in Set.Ioi 0,
      (Set.indicator {y | t < ‖f y‖} (fun _ => 1) x) ∂volume).toReal

/-- **Minkowski integral inequality for Lp** (named open def, ETA 2-3 weeks):
    ‖∫ h(x,y) dy‖_{Lp(x)} ≤ ∫ ‖h(·,y)‖_{Lp} dy.
    Lean candidate: MeasureTheory.snorm_lintegral_le or eLpNorm_lintegral_le
    (exact name needs lean --run; Meta AI used eLpNorm_lintegral_le, LIKELY NONEXISTENT). -/
def NS_MinkowskiIntegral_OPEN : Prop :=
  ∀ (p : ℝ≥0∞) (h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ),
    eLpNorm (fun x => ∫ y, h x y ∂(volume : Measure _)) p volume ≤
    ∫⁻ y, eLpNorm (fun x => h x y) p volume ∂(volume : Measure _)

/-- **Young convolution for weak type: L² * weak-L^{6/5} → L³** (named open def):
    This is the HLS step. eLpNorm_convolution_le_of_memWLP (Meta AI, all three rounds)
    does NOT exist in Mathlib v4.12.0 and cannot be replaced by volume_superlevel_riesz
    alone — that only gives the WEAK-Lp bound on the kernel, not the convolution estimate.
    The full HLS proof also requires Marcinkiewicz interpolation (also not in Mathlib).
    ETA: 4-6 weeks. Blocks NS_RieszPotentialBound_OPEN. -/
def NS_YoungWeakType_OPEN : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (f g : EuclideanSpace ℝ (Fin 3) → ℂ),
      MeasureTheory.MemLp f 2 (volume : Measure _) →
      NS_RieszKernelWeakL65_OPEN →
      eLpNorm (fun x => ∫ y, f (x - y) * g y ∂volume) 3 volume ≤
      ENNReal.ofReal C * eLpNorm f 2 volume

/-! ## §D. What remains closed / what remains open -/

/-
PHASE 62 LEDGER (July 1, 2026):

PROVED (0 sorry, classical trio):
  riesz_kernel_rpow_identity  (Phase 61)  : (a^{5/2})^{2/5} = a
  rpow_inv_iff                (Phase 62)  : t ≤ a^{-5/2} ↔ a ≤ t^{-2/5}
  riesz_superlevel_is_closedBall (Phase 62): correct closed ball identity

NAMED OPEN (no sorry, no axiom):
  Phase 61: NS_WeakLpSuperLevel def, NS_RieszKernelWeakL65_OPEN,
            NS_HLS_L2toL6_OPEN, NS_RieszPotentialBound_OPEN,
            NS_FourierHalfRep_OPEN, NS_L3DualChar_OPEN,
            NS_InterpolationDual_OPEN, NS_SobolevL3_HLSRoute_OPEN
  Phase 62: NS_VolumeSuperlevel_OPEN, NS_LayerCake_OPEN,
            NS_MinkowskiIntegral_OPEN, NS_YoungWeakType_OPEN

REMAINING BLOCKERS (in dependency order):
  (1) EuclideanSpace.volume_ball API name   → NS_VolumeSuperlevel_OPEN (1 week)
  (2) Layer-cake name                        → NS_LayerCake_OPEN (1 week)
  (3) Minkowski integral inequality          → NS_MinkowskiIntegral_OPEN (2-3 weeks)
  (4) Marcinkiewicz interpolation + HLS      → NS_YoungWeakType_OPEN (4-6 weeks)
  (5) NS_VolumeSuperlevel + NS_YoungWeakType → NS_RieszPotentialBound_OPEN
  (6) NS_RieszPotentialBound + FourierRep   → NS_SobolevL3_HLSRoute_OPEN
  (7) NS_SobolevL3_HLSRoute                 → ns_sobolev_l3_from_hls (Phase 61)
  (8) ns_sobolev_l3_from_hls               → NS_BilinearEstimate_OPEN(-3/2) = D1

D1 ETA: 4-6 weeks (unchanged; gated on step 4 = Marcinkiewicz in Mathlib).

KEY MESSAGE TO META AI:
  eLpNorm_convolution_le_of_memWLP has been flagged in three consecutive rounds
  as nonexistent. The comment "but we avoid MemWLP, use volume_superlevel_riesz"
  is incorrect — volume_superlevel_riesz only gives the kernel bound, not the
  convolution estimate. The full Young weak-type theorem = HLS itself.
  Suggested next step for Meta AI: prove NS_YoungWeakType_OPEN directly
  using Lorentz space interpolation (constructive, avoids MemWLP type entirely).
-/

end Phase62RieszGeometry
end NS
end Towers
end TheoremaAureum
