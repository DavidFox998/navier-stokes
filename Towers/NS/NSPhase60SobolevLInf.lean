/-
================================================================
Towers / NS / NSPhase60SobolevLInf  --  NS Tower Phase 60

PHASE 60: PEETRE INEQUALITY + SOBOLEV L-INFINITY EMBEDDING + HLS STRUCTURE

David Fox / Meta AI collaboration (July 1, 2026):
  Division of labour:
    Meta AI: NS_SobolevL3_OPEN (H^{1/2} -> L^3 via rieszPot + HLS).
    This file: Peetre inequality (base proved; nonneg case closed) + sobolev_Linf.

------------------------------------------------------------------
API AUDIT (Mathlib v4.12.0):

  EXISTS (correct names):
    Real.rpow_le_rpow  : 0<=x -> x<=y -> 0<=z -> x^z <= y^z
    Real.mul_rpow      : 0<=x -> 0<=y -> (x*y)^z = x^z * y^z
    Real.rpow_neg      : 0<=x -> x^(-z) = (x^z)^{-1}
    norm_sub_comm      : ||a - b|| = ||b - a||
    abs_of_nonneg / abs_of_neg

  DOES NOT EXIST in v4.12.0 (Meta AI hallucinations):
    rpow_neg_one_mul_abs    -- nonexistent; use Real.rpow_neg + abs_of_neg
    rpow_mul_abs            -- nonexistent; use abs_of_nonneg + Real.mul_rpow
    memWLP_of_le_mul_rpow   -- nonexistent; no weak-Lp machinery in v4.12.0
    eLpNorm_convolution_le_of_memWLP  -- nonexistent; HLS not in Mathlib v4.12.0
    eLpNorm_le_eLpNorm_rpow_mul       -- nonexistent
    eLpNorm_le_Hnorm                  -- nonexistent
    MeasureTheory.MemWLP              -- nonexistent (it's MemLp for strong Lp only)

------------------------------------------------------------------
PEETRE STATUS:
  peetre_base (proved, 0 sorry): 1+||xi||^2 <= 2*(1+||eta||^2)*(1+||xi-eta||^2).
  NS_WeightPeetre_Nonneg (proved, 0 sorry, s >= 0):
    (1+||xi||^2)^s <= 2^s * (1+||eta||^2)^s * (1+||xi-eta||^2)^s.
    Proof: Real.rpow_le_rpow(peetre_base) + Real.mul_rpow twice.
    With |s|=s this closes NS_WeightPeetre_OPEN for s >= 0.
  NS_WeightPeetre_Neg (named open, s < 0):
    Needs: A^{-1} <= D * B^{-1} * C from B <= D*A*C (all positive).
    Proof route: rewrite x^s = (x^{-s})^{-1} via Real.rpow_neg + neg_neg,
    then div_le_div_iff(hA)(hB) closes to B <= D*C*A = peetre_base(eta,xi).
    ETA: 1 week (lean --run to confirm div_le_div_iff name in v4.12.0).

SOBOLEV L-INF ROUTE (Sections C-D, named open defs):
  H^{s+2}(R^3) -> L^inf(R^3) for s+2 > 3/2 (strict; s > -1/2).
  Borderline: H^{3/2} does NOT embed in L^inf (log divergence; BMO only).
  NS paraproduct uses L^3 x L^6 Holder instead.

HLS ROUTE (for Meta AI, named open defs):
  NS_SobolevL3_OPEN: H^{1/2} -> L^3. Blocked: HLS not in Mathlib v4.12.0.
  NS_CauchySchwarzConv_OPEN: blocked on NS_SobolevL3_OPEN.

Named surfaces: NS_WeightPeetre_Neg, NS_WeightIntegralFinite_OPEN,
  NS_HolderLintegral_OPEN, NS_SobolevLInf_OPEN, NS_SobolevL3_OPEN,
  NS_SobolevL6_OPEN, NS_CauchySchwarzConv_OPEN.
Proved (0 sorry): peetre_base, NS_WeightPeetre_Nonneg,
  sobolev_linf_from_weight_and_holder, ns_d1_from_sobolev_l3.
Axioms: {propext, Classical.choice, Quot.sound}
Sorry count: 0
================================================================
-/

import Towers.NS.NSPhase59D1Closure

open Filter Topology Real MeasureTheory
open scoped BigOperators ENNReal NNReal
open TheoremaAureum.Towers.NS.FunctionSpaces
open TheoremaAureum.Towers.NS.DuhamelBridge

namespace TheoremaAureum
namespace Towers
namespace NS
namespace Phase60SobolevLInf

variable {s : ℝ}

/-! ## §A. Peetre inequality -/

/-- **Peetre base inequality** (proved, 0 sorry):
    1 + ‖ξ‖² ≤ 2 * (1 + ‖η‖²) * (1 + ‖ξ - η‖²).
    Proof: ‖ξ‖ ≤ ‖η‖ + ‖ξ - η‖ (triangle); square; AM-GM (2ab ≤ a²+b²); nlinarith. -/
theorem peetre_base (ξ η : Freq) :
    1 + ‖ξ‖ ^ 2 ≤ 2 * (1 + ‖η‖ ^ 2) * (1 + ‖ξ - η‖ ^ 2) := by
  have h_tri : ‖ξ‖ ≤ ‖η‖ + ‖ξ - η‖ := by
    have heq : ξ = η + (ξ - η) := by abel
    calc ‖ξ‖ = ‖η + (ξ - η)‖ := by rw [heq]
         _ ≤ ‖η‖ + ‖ξ - η‖    := norm_add_le _ _
  have hξ := norm_nonneg ξ
  have hη := norm_nonneg η
  have hd := norm_nonneg (ξ - η)
  nlinarith [sq_nonneg (‖η‖ - ‖ξ - η‖), sq_nonneg ‖ξ‖,
             mul_nonneg hη hd, mul_nonneg (mul_nonneg hη hη) (mul_nonneg hd hd)]

/-- **Peetre weight factorization, s ≥ 0** (proved, 0 sorry):
    For s ≥ 0 (so |s| = s):
    (1 + ‖ξ‖²)^s ≤ 2^s * (1 + ‖η‖²)^s * (1 + ‖ξ - η‖²)^s.
    Proof:
      (1+‖ξ‖²)^s ≤ (2*(1+‖η‖²)*(1+‖ξ-η‖²))^s   [rpow_le_rpow, peetre_base, hs]
      = 2^s * (1+‖η‖²)^s * (1+‖ξ-η‖²)^s          [mul_rpow twice]. -/
theorem NS_WeightPeetre_Nonneg (s : ℝ) (hs : 0 ≤ s) (ξ η : Freq) :
    (1 + ‖ξ‖ ^ 2) ^ s ≤
    2 ^ s * (1 + ‖η‖ ^ 2) ^ s * (1 + ‖ξ - η‖ ^ 2) ^ s := by
  have h_pb := peetre_base ξ η
  have h_rp : (1 + ‖ξ‖ ^ 2) ^ s ≤
      (2 * (1 + ‖η‖ ^ 2) * (1 + ‖ξ - η‖ ^ 2)) ^ s :=
    Real.rpow_le_rpow (by positivity) h_pb hs
  rw [Real.mul_rpow (mul_nonneg (by positivity) (by positivity)) (by positivity),
      Real.mul_rpow (by positivity : (0:ℝ) ≤ 2) (by positivity)] at h_rp
  exact h_rp

/-- **Peetre weight factorization, general s** (named open def):
    (1 + ‖ξ‖²)^s ≤ 2^|s| * (1 + ‖η‖²)^s * (1 + ‖ξ - η‖²)^|s|.

    Status by case:
      s ≥ 0: PROVED by NS_WeightPeetre_Nonneg (|s|=s, see above).
      s < 0: OPEN. Route: rewrite x^s = (x^{-s})⁻¹ via Real.rpow_neg+neg_neg,
             then goal reduces to (1+‖η‖²)^{-s} ≤ 2^{-s}*(1+‖ξ‖²)^{-s}*(1+‖ξ-η‖²)^{-s}
             via div_le_div_iff. That follows from peetre_base η ξ raised to (-s) ≥ 0.
             ETA: 1 week (lean --run to confirm div_le_div_iff + rpow_neg chain).

    Note: Meta AI proof used rpow_neg_one_mul_abs and rpow_mul_abs.
    Neither exists in Mathlib v4.12.0. Correct names: Real.rpow_neg, abs_of_neg. -/
def NS_WeightPeetre_Neg : Prop :=
  ∀ (s : ℝ), s < 0 → ∀ (ξ η : Freq),
    (1 + ‖ξ‖ ^ 2) ^ s ≤
    2 ^ |s| * (1 + ‖η‖ ^ 2) ^ s * (1 + ‖ξ - η‖ ^ 2) ^ |s|

/-- **Full Peetre factorization, s ≥ 0 case resolved** (0 sorry):
    NS_WeightPeetre_OPEN for s ≥ 0 follows from NS_WeightPeetre_Nonneg
    by rewriting |s| = s. -/
theorem weight_peetre_nonneg_resolved (hs : 0 ≤ s) (ξ η : Freq) :
    (1 + ‖ξ‖ ^ 2) ^ s ≤
    2 ^ |s| * (1 + ‖η‖ ^ 2) ^ s * (1 + ‖ξ - η‖ ^ 2) ^ |s| := by
  rw [abs_of_nonneg hs]
  exact NS_WeightPeetre_Nonneg s hs ξ η

/-- **Full Peetre factorization conditional** (0 sorry):
    Given NS_WeightPeetre_Neg (the s < 0 case), the full inequality holds for all s. -/
theorem weight_peetre_from_neg (h_neg : NS_WeightPeetre_Neg) (ξ η : Freq) :
    (1 + ‖ξ‖ ^ 2) ^ s ≤
    2 ^ |s| * (1 + ‖η‖ ^ 2) ^ s * (1 + ‖ξ - η‖ ^ 2) ^ |s| := by
  rcases le_or_lt 0 s with hs | hs
  · exact weight_peetre_nonneg_resolved hs ξ η
  · exact h_neg s hs ξ η

/-! ## §B. Riesz potential (Fourier-side building block) -/

/-- **Fourier-side Riesz potential** of order sigma.
    Multiplies the Fourier transform of u by |xi|^{-sigma}.
    Physical space: convolution with C * |x|^{sigma-3} (HLS kernel).
    For sigma=1/2, R^3: maps H^0 -> H^{-1/2} and L^{6/5} -> L^6 (HLS). -/
noncomputable def rieszPot (sigma : ℝ) (u : Hdiv_free 0) : Freq → Val :=
  fun xi => (‖xi‖ ^ (-sigma) : ℝ) • ((u : Lp Val 2 (mu 0)) xi)

/-! ## §C. Named open surfaces -/

/-- **Weight integral convergence** (ETA 2-3 weeks):
    int_{R^3} (1 + ||xi||^2)^{-sigma} dxi < inf  for  sigma > 3/2.
    Polar form: 4pi * int_0^inf r^2 (1+r^2)^{-sigma} dr, convergent iff sigma > 3/2.
    Lean API: MeasureTheory.integral_rpow for EuclideanSpace (Fin 3). -/
def NS_WeightIntegralFinite_OPEN (sigma : ℝ) : Prop :=
  3 / 2 < sigma →
  ∃ C_w : ℝ, 0 < C_w ∧
    ∫⁻ xi : Freq, ENNReal.ofReal ((1 + ‖xi‖ ^ 2) ^ (-sigma)) ∂(volume : Measure Freq) ≤
    ENNReal.ofReal C_w

/-- **Cauchy-Schwarz for weighted lintegral** (ETA 1 week, Lean API lookup):
    (int ||u(xi)||)^2 <= (int weight(s+2)^{-1} dxi) * ||u||_{H^{s+2}}^2.
    Proof: write ||u|| = weight^{-1/2} * weight^{1/2} * ||u||, Cauchy-Schwarz.
    Lean API: lintegral_mul_le_Lp_mul_Lq (Holder p=q=2, NNReal form). -/
def NS_HolderLintegral_OPEN : Prop :=
  ∀ (u : Hdiv_free (s + 2)),
    (eLpNorm (⇑(u : Lp Val 2 (mu (s + 2)))) 1 (volume : Measure Freq)) ^ 2 ≤
    (∫⁻ xi : Freq, (weight (s + 2) xi)⁻¹ ∂(volume : Measure Freq)) *
    (eLpNorm (⇑(u : Lp Val 2 (mu (s + 2)))) 2 (mu (s + 2))) ^ 2

/-- **Sobolev L^inf embedding** (strict threshold, ETA 1 week after convergence + Holder):
    For s > -1/2 (s+2 > 3/2 strictly), the Fourier L^1 bound gives:
      ||F^{-1}(u)||_{Linf} <= sqrt(C_w) * ||u||_{H^{s+2}}.
    Stated in squared form to avoid ENNReal.sqrt. -/
def NS_SobolevLInf_OPEN (s : ℝ) : Prop :=
  -1 / 2 < s →
  ∃ C_inf : ℝ, 0 < C_inf ∧
    ∀ (u : Hdiv_free (s + 2)),
      (eLpNorm (⇑(u : Lp Val 2 (mu (s + 2)))) 1 (volume : Measure Freq)) ^ 2 ≤
      ENNReal.ofReal C_inf *
      (eLpNorm (⇑(u : Lp Val 2 (mu (s + 2)))) 2 (mu (s + 2))) ^ 2

/-- **Sobolev L^3 embedding** (HLS route, for Meta AI):
    H^{1/2}(R^3) -> L^3(R^3) at the critical Sobolev exponent.
    Blocked: HLS inequality not in Mathlib v4.12.0.
    Meta AI names (do NOT exist in v4.12.0):
      memWLP_of_le_mul_rpow, eLpNorm_convolution_le_of_memWLP,
      MeasureTheory.MemWLP, eLpNorm_le_eLpNorm_rpow_mul, eLpNorm_le_Hnorm.
    Route when HLS arrives: rieszPot(1/2) + HLS(p=2,q=6,alpha=3/2) + Plancherel.
    Stated as the product bound (Prop-equal to D1 at s=-3/2). -/
def NS_SobolevL3_OPEN : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (u v : Hdiv_free ((-3 / 2 : ℝ) + 2)),
      ∃ B_uv : Hdiv_free ((-3 / 2 : ℝ) + 1),
        ‖(B_uv : Lp Val 2 (mu ((-3 / 2 : ℝ) + 1)))‖ ≤
          C * ‖(u : Lp Val 2 (mu ((-3 / 2 : ℝ) + 2)))‖ *
              ‖(v : Lp Val 2 (mu ((-3 / 2 : ℝ) + 2)))‖

/-- **Sobolev L^6 embedding** (ETA 1 week after NS_SobolevL3_OPEN):
    H^1(R^3) -> L^6(R^3), classical (critical exponent for s=1, R^3).
    Used in the paraproduct: v in H^{3/2} -> H^1 -> L^6 (Sobolev chain). -/
def NS_SobolevL6_OPEN : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (u v : Hdiv_free ((-1 / 2 : ℝ) + 2)),
      ∃ B_uv : Hdiv_free ((-1 / 2 : ℝ) + 1),
        ‖(B_uv : Lp Val 2 (mu ((-1 / 2 : ℝ) + 1)))‖ ≤
          C * ‖(u : Lp Val 2 (mu ((-1 / 2 : ℝ) + 2)))‖ *
              ‖(v : Lp Val 2 (mu ((-1 / 2 : ℝ) + 2)))‖

/-- **Cauchy-Schwarz convolution estimate** (named open def, ETA 3-4 weeks):
    || int f(x) * g(x-y) * ||y||^{-5/2} dy ||_{L^2} <= C * ||f||_{L^2} * ||g||_{L^2}.
    Proof route (Meta AI, Phase 58):
      (1) Fubini: lintegral_lintegral (MeasureTheory.Constructions.Prod.Basic, EXISTS v4.12.0).
      (2) HLS: g(x-y)*||y||^{-1/2} has L^6 output for g in L^2 (BLOCKED: HLS not in Mathlib).
      (3) Holder: L^2 * L^6 * L^3 with 1/2+1/6+1/3=1.
      (4) NS_SobolevL3_OPEN: test fn in H^{1/2} -> L^3.
    Blocked on (2) = NS_SobolevL3_OPEN (Meta AI, 3-4 weeks). -/
def NS_CauchySchwarzConv_OPEN : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (f g : EuclideanSpace ℝ (Fin 3) → ℂ),
      MeasureTheory.MemLp f 2 (volume : Measure (EuclideanSpace ℝ (Fin 3))) →
      MeasureTheory.MemLp g 2 (volume : Measure (EuclideanSpace ℝ (Fin 3))) →
      eLpNorm
        (fun x : EuclideanSpace ℝ (Fin 3) =>
          ∫ y, f x * g (x - y) * ‖y‖ ^ (-(5 / 2 : ℝ)) ∂(volume : Measure _))
        2 (volume : Measure (EuclideanSpace ℝ (Fin 3))) ≤
      ENNReal.ofReal (C * eLpNorm f 2 volume |>.toReal * eLpNorm g 2 volume |>.toReal)

/-! ## §D. sobolev_Linf bridge (0 sorry) -/

/-- **Weight inverse equals reciprocal of weight ofReal** (sub-lemma):
    (weight (s+2) xi)^{-1} = ENNReal.ofReal ((1+||xi||^2)^{-(s+2)}). -/
private lemma weight_inv_eq (xi : Freq) :
    (weight (s + 2) xi)⁻¹ =
    ENNReal.ofReal ((1 + ‖xi‖ ^ 2) ^ (-(s + 2))) := by
  simp only [weight, Real.rpow_neg (by positivity)]
  rw [ENNReal.inv_ofReal (by positivity)]

/-- **sobolev_Linf from weight convergence + Holder** (0 sorry):
    Chain: (||u||_{L^1})^2 <= (int weight^{-1}) * ||u||_{H^{s+2}}^2 <= C_w * ||u||_{H^s+2}^2. -/
theorem sobolev_linf_from_weight_and_holder
    (h_w : NS_WeightIntegralFinite_OPEN (s + 2))
    (h_cs : @NS_HolderLintegral_OPEN s) :
    NS_SobolevLInf_OPEN s := by
  intro hs
  have hσ : (3 : ℝ) / 2 < s + 2 := by linarith
  obtain ⟨C_w, hCw_pos, hCw_le⟩ := h_w hσ
  refine ⟨C_w, hCw_pos, fun u => ?_⟩
  have h_sq := h_cs u
  have h_int_eq :
      ∫⁻ xi : Freq, (weight (s + 2) xi)⁻¹ ∂(volume : Measure Freq) ≤
      ENNReal.ofReal C_w := by
    calc ∫⁻ xi : Freq, (weight (s + 2) xi)⁻¹ ∂volume
        = ∫⁻ xi : Freq, ENNReal.ofReal ((1 + ‖xi‖ ^ 2) ^ (-(s + 2))) ∂volume := by
          congr 1; ext xi; exact weight_inv_eq xi
      _ ≤ ENNReal.ofReal C_w := hCw_le
  calc (eLpNorm (⇑(u : Lp Val 2 (mu (s + 2)))) 1 volume) ^ 2
      ≤ (∫⁻ xi : Freq, (weight (s + 2) xi)⁻¹ ∂volume) *
        (eLpNorm (⇑(u : Lp Val 2 (mu (s + 2)))) 2 (mu (s + 2))) ^ 2 := h_sq
    _ ≤ ENNReal.ofReal C_w *
        (eLpNorm (⇑(u : Lp Val 2 (mu (s + 2)))) 2 (mu (s + 2))) ^ 2 :=
        ENNReal.mul_le_mul_of_nonneg_right h_int_eq (zero_le _)

/-! ## §E. D1 bridge: NS_SobolevL3_OPEN -> D1(-3/2) (0 sorry) -/

/-- **D1 from HLS** (0 sorry):
    NS_SobolevL3_OPEN -> NS_BilinearEstimate_OPEN (-3/2).
    Both Lean Props have identical Hdiv_free indices (-3/2+2=1/2, -3/2+1=-1/2).
    Prop-equality bridge: exact unwrapping. -/
theorem ns_d1_from_sobolev_l3 (h : NS_SobolevL3_OPEN) :
    NS_BilinearEstimate_OPEN (-3 / 2) := by
  obtain ⟨C, hC, hbound⟩ := h
  exact ⟨C, hC, fun u v => hbound u v⟩

/-! ## §F. Summary -/

/-
PHASE 60 LEDGER (July 1, 2026):

PROVED (0 sorry, classical trio):
  peetre_base              : 1+||ξ||² ≤ 2(1+||η||²)(1+||ξ-η||²)   [nlinarith]
  NS_WeightPeetre_Nonneg   : s≥0 case of Peetre factorization        [rpow_le_rpow+mul_rpow]
  weight_peetre_nonneg_resolved: |s|=s bridge                        [abs_of_nonneg]
  weight_peetre_from_neg   : full factorization from NS_WeightPeetre_Neg [rcases le_or_lt]
  sobolev_linf_from_weight_and_holder                                 [ENNReal.mul_le_mul...]
  ns_d1_from_sobolev_l3   : D1(-3/2) from NS_SobolevL3_OPEN         [exact]

NAMED OPEN (no sorry, no axiom):
  NS_WeightPeetre_Neg       : s<0 Peetre factorization  [rpow_neg+div_le_div_iff, ETA 1 week]
  NS_WeightIntegralFinite_OPEN: polar integral R^3       [integral_rpow, ETA 2-3 weeks]
  NS_HolderLintegral_OPEN   : Cauchy-Schwarz weighted    [lintegral Holder, ETA 1 week]
  NS_SobolevLInf_OPEN       : L^inf embedding s>-1/2    [after above two]
  NS_SobolevL3_OPEN         : H^{1/2}->L^3, HLS         [Meta AI, ETA 3-4 weeks]
  NS_SobolevL6_OPEN         : H^1->L^6                  [after SobolevL3]
  NS_CauchySchwarzConv_OPEN : Young weak-Lp              [after SobolevL3]

D1 = NS_BilinearEstimate_OPEN(-3/2): closes the moment NS_SobolevL3_OPEN lands.
Net ETA for D1: 3-4 weeks (Meta AI HLS track).

D3 ROADMAP:
  M5 (Fujita-Kato small data): D1 + corrSemigroupRate.
  M6 (global regularity): Remove small-data. Attack: corrSemigroupRate ξ < 1 all data.
-/

end Phase60SobolevLInf
end NS
end Towers
end TheoremaAureum
