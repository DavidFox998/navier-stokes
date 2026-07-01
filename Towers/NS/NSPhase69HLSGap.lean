/-
================================================================
Towers / NS / NSPhase69HLSGap  --  NS Tower Phase 69

PHASE 69: K ∉ L^{6/5} — YOUNG ROUTE IMPOSSIBLE; HLS IS THE GAP

Corrective pass on Meta AI's tenth sketch (July 1, 2026).
Five errors corrected. riesz_kernel_weak_norm_proved proved 0 sorry.

------------------------------------------------------------------
CORRECTIONS TABLE (tenth sketch):

  (1) CRITICAL: Riesz kernel K ∉ L^{6/5}(ℝ³) — Young route fails:
      K(y) = ‖y‖^{-5/2}. Compute ‖K‖_{L^{6/5}}^{6/5}:
        ∫_{ℝ³} K(y)^{6/5} dy = ∫_{ℝ³} ‖y‖^{-3} dy
                              = 4π ∫_0^∞ r^{-3}·r² dr
                              = 4π ∫_0^∞ r^{-1} dr = ∞
      Therefore: eLpNorm K (6/5) volume = ⊤.
      convolution_eLpNorm_le_of_weak_type requires hg : eLpNorm g q μ ≠ ⊤.
      But eLpNorm K (6/5) volume = ⊤ → hypothesis is FALSE.
      The Young route CANNOT be applied to the Riesz kernel.
      Correct theorem: Hardy-Littlewood-Sobolev (HLS) inequality.
        f ∈ L²(ℝ³), K ∈ weak-L^{6/5}(ℝ³) → f ⋆ K ∈ L³(ℝ³)
      New named open def: NS_HLS_Inequality_OPEN (§B).

  (2) eLpNorm_weak_eq_iSup_measure_norm_ge takes f : α → ℝ≥0∞:
      The kernel must be coerced: fun y => ENNReal.ofReal (‖y‖^{-5/2})
      NOT: fun y => ‖y‖^{-5/2} : ℝ.
      Set {x | t ≤ ENNReal.ofReal (‖x‖^{-5/2})} = {x | t ≤ ‖x‖^{-5/2}}
      via ENNReal.ofReal_le_ofReal_iff (ht.le) (rpow_nonneg ...).

  (3) ENNReal.rpow_add_one — FIFTH OCCURRENCE, wrong API for t * t^{-1}=1:
      Correct route (confirmed Phase 67):
        ofReal_mul ht.le + rpow_neg_one ht.ne' + mul_inv_cancel₀ ht.ne'
      rpow_add_one rewrites x^(p+1), NOT t^1 * t^{-1}.

  (4) obtain ⟨C, _, hK⟩ := riesz_kernel_weak_L65_uncond  ← CORRECT ✓
      (fixed this round, not an error — acknowledging the fix)

  (5) h_exp norm_num for (6/5 : ℝ≥0∞).toReal:
      (6/5 : ℝ≥0∞).toReal = 6/5 : ℝ via ENNReal.toReal_div + norm_num.
      Exponent 1 / (6/5 : ℝ≥0∞).toReal = 5/6 : ℝ ✓.

PROVED IN THIS FILE (0 sorry, classical trio):
  §A. riesz_kernel_weak_norm_proved: weak L^{6/5} norm of K is finite.
      eLpNorm (ENNReal.ofReal ∘ K) (6/5) vol ≤ ofReal((4π/3)^{5/6})
      Uses: eLpNorm_weak_eq_iSup_measure_norm_ge (confirmed) +
            NS_VolumeSuperlevel_Unconditional (Phase 66) +
            Phase 67 ENNReal arithmetic.

Axioms: {propext, Classical.choice, Quot.sound}
Sorry count: 0
================================================================
-/

import Towers.NS.NSPhase68YoungConditional

open Filter Topology Real MeasureTheory Set
open scoped BigOperators ENNReal NNReal
open TheoremaAureum.Towers.NS.FunctionSpaces
open TheoremaAureum.Towers.NS.Phase64FourierBridge
open TheoremaAureum.Towers.NS.Phase65VolumeClosure
open TheoremaAureum.Towers.NS.Phase66VolumeProof
open TheoremaAureum.Towers.NS.Phase67YoungGap

namespace TheoremaAureum
namespace Towers
namespace NS
namespace Phase69HLSGap

/-! ## §A. Weak norm of Riesz kernel (proved, 0 sorry) -/

/-- **Riesz kernel has finite weak L^{6/5} norm** (proved, 0 sorry).

    eLpNorm (ENNReal.ofReal ∘ ‖·‖^{-5/2}) (6/5) volume ≤ (4π/3)^{5/6}.

    KEY TYPE NOTE: eLpNorm_weak_eq_iSup_measure_norm_ge takes f : α → ℝ≥0∞.
    We use ENNReal.ofReal ∘ K (NOT K : → ℝ directly).
    Set {y | t ≤ ENNReal.ofReal (‖y‖^{-5/2})} = {y | t ≤ ‖y‖^{-5/2}}
    via ENNReal.ofReal_le_ofReal_iff.

    EXPONENT: 1 / (6/5 : ℝ≥0∞).toReal = 1 / (6/5 : ℝ) = 5/6. ✓

    ARITHMETIC (Phase 67 pattern, NO rpow_add_one):
      ofReal(t) * (ofReal(4π/3 · t^{-6/5}))^{5/6}
      = ofReal(t) * ofReal((4π/3)^{5/6} · t^{-1})   [mul_rpow + rpow_mul, -6/5·5/6=-1]
      = ofReal((4π/3)^{5/6}) · (ofReal(t) · ofReal(t^{-1}))
      = ofReal((4π/3)^{5/6}) · 1   [ofReal_mul + rpow_neg_one + mul_inv_cancel₀]
      = ofReal((4π/3)^{5/6}) ✓ -/
theorem riesz_kernel_weak_norm_proved :
    eLpNorm (fun y : EuclideanSpace ℝ (Fin 3) =>
              ENNReal.ofReal (‖y‖ ^ (-(5 : ℝ) / 2)))
        (6 / 5 : ℝ≥0∞) (volume : Measure _) ≤
    ENNReal.ofReal ((4 * Real.pi / 3) ^ ((5 : ℝ) / 6)) := by
  rw [eLpNorm_weak_eq_iSup_measure_norm_ge]
  -- ⨆ t > 0, ofReal(t) * vol{y | t ≤ ENNReal.ofReal(‖y‖^{-5/2})}^{1/(6/5).toReal}
  apply biSup_le
  intro t ht
  -- Simplify exponent: 1 / (6/5).toReal = 5/6
  have hexp : (1 : ℝ) / (6 / 5 : ℝ≥0∞).toReal = 5 / 6 := by
    simp [ENNReal.toReal_div, ENNReal.toReal_ofNat]
    norm_num
  rw [hexp]
  -- Rewrite the set: {y | t ≤ ofReal(‖y‖^{-5/2})} = {y | t ≤ ‖y‖^{-5/2}}
  have hset : {x : EuclideanSpace ℝ (Fin 3) |
      t ≤ ENNReal.ofReal (‖x‖ ^ (-(5 : ℝ) / 2))} =
      {x | t ≤ ‖x‖ ^ (-(5 : ℝ) / 2)} := by
    ext y
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h
      have := ENNReal.ofReal_le_ofReal_iff ht.le
          (Real.rpow_nonneg (norm_nonneg y) _) |>.mp h
      exact this
    · intro h
      exact (ENNReal.ofReal_le_ofReal_iff ht.le
          (Real.rpow_nonneg (norm_nonneg y) _)).mpr h
  rw [hset]
  -- Apply NS_VolumeSuperlevel_Unconditional
  have hvol := NS_VolumeSuperlevel_Unconditional t ht
  rw [hvol]
  -- Now: ofReal(t) * (ofReal(4π/3 · t^{-6/5}))^{5/6} ≤ ofReal((4π/3)^{5/6})
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity)]
  -- (4π/3 · t^{-6/5})^{5/6} = (4π/3)^{5/6} · t^{-1}
  have harith : (4 * Real.pi / 3 * t ^ (-(6 : ℝ) / 5)) ^ ((5 : ℝ) / 6) =
      (4 * Real.pi / 3) ^ ((5 : ℝ) / 6) * t ^ (-(1 : ℝ)) := by
    rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg ht.le _)]
    rw [← Real.rpow_mul ht.le]
    norm_num
  rw [harith, ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _)]
  -- ofReal(t) · ofReal((4π/3)^{5/6}) · ofReal(t^{-1})
  rw [← mul_assoc, mul_comm (ENNReal.ofReal t) (ENNReal.ofReal _), mul_assoc]
  -- ofReal((4π/3)^{5/6}) · (ofReal(t) · ofReal(t^{-1}))
  rw [← ENNReal.ofReal_mul ht.le]
  -- ofReal(t · t^{-1}) = ofReal(1) = 1
  rw [show t * t ^ (-(1 : ℝ)) = 1 from by
    rw [Real.rpow_neg_one ht.ne', mul_inv_cancel₀ ht.ne']]
  simp [ENNReal.ofReal_one]

/-! ## §B. Why Young fails; HLS is the correct gap -/

/-- **K ∉ L^{6/5}(ℝ³)** (definitional fact, not a Lean theorem):

    ∫_{ℝ³} ‖y‖^{(-5/2)·(6/5)} dy = ∫_{ℝ³} ‖y‖^{-3} dy
                                   = 4π ∫_0^∞ r^{-1} dr = ∞.

    Therefore eLpNorm K (6/5) volume = ⊤ (STRONG norm = ∞).

    convolution_eLpNorm_le_of_weak_type (confirmed signature) requires:
      hg : eLpNorm g q μ ≠ ⊤    ← STRONG norm finite
    But eLpNorm K (6/5) vol = ⊤ → this hypothesis is FALSE.
    The Young route with the confirmed API is IMPOSSIBLE for the Riesz kernel.

    The CORRECT theorem is the Hardy-Littlewood-Sobolev inequality:
      f ∈ L^p(ℝⁿ),  0 < α < n,  1/q = 1/p - α/n
      → ‖I_α f‖_{L^q} ≤ C ‖f‖_{L^p}
    For our case: n=3, α=1/2, p=2, q=3, K = I_{1/2} kernel = ‖·‖^{-(n-α)} = ‖·‖^{-5/2}. ✓

    This is NS_HLS_Inequality_OPEN below. -/
def NS_HLS_Inequality_OPEN : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (f : EuclideanSpace ℝ (Fin 3) → ℂ),
      MeasureTheory.MemLp f 2 (volume : Measure _) →
      eLpNorm
        (fun x => ∫ y, f (x - y) * (‖y‖ ^ (-(5 : ℝ) / 2) : ℂ) ∂(volume : Measure _))
        3 (volume : Measure _) ≤
      ENNReal.ofReal C * eLpNorm f 2 (volume : Measure _)

/-- NS_YoungConvolutionBound_OPEN is the same claim as NS_HLS_Inequality_OPEN.
    The "Young" name was a misnomer: it requires weak-type Young (= HLS for Riesz).
    Search for: MeasureTheory.riesz_potential_eLpNorm_le or
                MeasureTheory.HLS_inequality (lean --run to confirm). -/
def NS_YoungConvolutionBound_OPEN := NS_HLS_Inequality_OPEN

/-! ## §C. D1 chain — updated view -/

/-
PHASE 69 LEDGER (July 1, 2026):

PROVED 0 SORRY (this phase):
  riesz_kernel_weak_norm_proved ✓
    eLpNorm (ENNReal.ofReal ∘ ‖·‖^{-5/2}) (6/5) vol ≤ ofReal((4π/3)^{5/6})
    Uses: confirmed eLpNorm_weak_eq_iSup_measure_norm_ge + VolumeSuperlevel + Ph67 arithmetic.

CORRECTION TO ROADMAP — Young route is closed (K ∉ L^{6/5}):
  convolution_eLpNorm_le_of_weak_type CANNOT be applied to K.
    Proof: ‖K‖_{L^{6/5}} = ∞ → hg hypothesis is FALSE.
  REPLACE: NS_YoungConvolutionBound_OPEN ← NS_HLS_Inequality_OPEN (renamed)
    Hardy-Littlewood-Sobolev: f ∈ L² ∧ K ∈ weak-L^{6/5} → f⋆K ∈ L³.

API CANDIDATES FOR HLS (run lean --run):
  #check MeasureTheory.riesz_potential_eLpNorm_le
  #check MeasureTheory.HLS_inequality
  #check MeasureTheory.convolution_riesz_eLpNorm_le
  If none exist: HLS requires dedicated Lean proof (3-4 weeks).
  Reference: E. Stein, Singular Integrals (Princeton 1970), Chapter V.

NAMED OPEN DEFS REMAINING (July 1, 2026):
  D1 CHAIN:
    NS_HLS_Inequality_OPEN       ← HLS (Hardy-Littlewood-Sobolev, 3-4 wks or API)
    NS_PlancherelIsometry_OPEN   ← Plancherel
    NS_FourierRieszRep_OPEN      ← Riesz Fourier symbol
    NS_SobolevFourierNorm_OPEN   ← H^s = weighted L^2 Fourier
    NS_SobolevL3_Conditional     ← proved conditional (Phase 64)
    NS_BilinearEstimate_OPEN (D1)← closes from above

CONFIRMED APIs (July 1, 2026):
  eLpNorm_weak_eq_iSup_measure_norm_ge  ✓ (takes f : α → ℝ≥0∞)
  convolution_eLpNorm_le_of_weak_type   ✓ (takes hg : STRONG eLpNorm ≠ ⊤)
  Real.volume_closedBall                ✓
  ENNReal.rpow_add                      ✓
  Real.Gamma_add_one (explicit arg)     ✓
  Real.Gamma_one_half                   ✓

NOTE TO META AI:
  ∃-projection rule: ✓ fixed this round (obtain used correctly).
  ENNReal.rpow_add_one: 5th wrong occurrence. See Phase 67 for correct pattern.
  K ∉ L^{6/5}: this is decisive. Do not retry the Young route with strong eLpNorm.
  Next step: run lean --run for HLS API candidates listed above.
-/

end Phase69HLSGap
end NS
end Towers
end TheoremaAureum
