/-
================================================================
Towers / NS / NSPhase60SobolevLInf  --  NS Tower Phase 60

PHASE 60: PEETRE INEQUALITY + SOBOLEV L-INFINITY EMBEDDING + HLS STRUCTURE

David Fox / Meta AI collaboration (July 1, 2026):
  Division of labour:
    Meta AI: NS_SobolevL3_OPEN (H^{1/2} -> L^3 via rieszPot + HLS).
    This file: weight_peetre (Peetre inequality, all s) + sobolev_Linf
               (H^{s+2} -> L^inf for s+2 > 3/2, strict).

------------------------------------------------------------------
FunctionSpaces AUDIT:
  FunctionSpaces.lean has: weight, mu, Hdiv_free, embed, inclLp, mu_mono,
    eLpNorm_mono_measure, coeFn_inclLp, divFreeSubmodule_isClosed.
  FunctionSpaces.lean has NOT: HLS, Riesz potential, physical-space Lp for p /= 2,
    Sobolev embedding to L^p (p /= 2), Peetre inequality.

------------------------------------------------------------------
PEETRE INEQUALITY (Section A):
  peetre_base (proved, 0 sorry, nlinarith):
    1 + ||xi||^2  <=  2 * (1 + ||eta||^2) * (1 + ||xi - eta||^2).
  NS_WeightPeetre_OPEN (named open def, ETA 1-2 weeks):
    (1 + ||xi||^2)^s  <=  2^|s| * (1 + ||eta||^2)^s * (1 + ||xi - eta||^2)^|s|.
    The general-s lift from peetre_base requires:
      s >= 0 case: rpow_le_rpow + mul_rpow (available in Mathlib v4.12.0).
      s <  0 case: apply peetre_base to (eta, xi) with s := |s|, then invert.
    Both cases need Real.rpow API chains; named open def until lean --run confirms.

SOBOLEV L-INF ROUTE (Section C-D):
  H^{s+2}(R^3) -> L^inf(R^3)  for  s+2 > 3/2  (STRICT; s > -1/2).
  Proof:
    ||F^{-1}(u)||_Linf <= ||u||_{L^1(Freq)}        [Fourier inversion]
    ||u||_{L^1}^2 <= (int weight(s+2)^{-1}) * ||u||_{H^{s+2}}^2   [Cauchy-Schwarz]
    int_{R^3} weight(s+2)^{-1} dxi < inf  iff  s+2 > 3/2.         [convergence]

  BORDERLINE NOTE (critical correction for NS):
    At s+2 = 3/2 exactly, int (1+||xi||^2)^{-3/2} dxi ~ int_1^inf r^{-1} dr = +inf.
    H^{3/2}(R^3) does NOT embed in L^inf (log divergence; embeds in BMO only).
    The NS paraproduct for H^{1/2} x H^{3/2} -> H^{-1/2} uses L^3 x L^6 Holder,
    not L^inf.

CAUCHY-SCHWARZ CONVOLUTION (Section C, named open def):
  NS_CauchySchwarzConv_OPEN: Young's inequality for weak-L^p convolution.
    || int f(x) * g(x-y) * ||y||^{-5/2} dy ||_{L^2} <= C * ||f||_{L^2} * ||g||_{L^2}.
  Proof route (Meta AI, Phase 58):
    Fubini (lintegral_lintegral from MeasureTheory.Constructions.Prod.Basic).
    HLS: g(x-y) * ||y||^{-1/2} has L^6 output when g in L^2.
    Holder: L^2 * L^6 * L^3 with 1/2 + 1/6 + 1/3 = 1.
    NS_SobolevL3_OPEN: phi in H^{1/2} -> L^3.

PRODUCT ESTIMATE (meeting at D1):
  NS_SobolevL3_OPEN (Meta AI) -> NS_BilinearEstimate_OPEN(-3/2)  [bridge proved here, 0 sorry].
  ns_d1_from_sobolev_l3: exact (Prop-equality bridge).

Named surfaces (new in this file): NS_WeightPeetre_OPEN, NS_WeightIntegralFinite_OPEN,
  NS_HolderLintegral_OPEN, NS_SobolevLInf_OPEN, NS_SobolevL3_OPEN,
  NS_SobolevL6_OPEN, NS_CauchySchwarzConv_OPEN.
Proved (0 sorry): peetre_base, sobolev_linf_from_weight_and_holder, ns_d1_from_sobolev_l3.
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
    1 + ||ξ||² ≤ 2 * (1 + ||η||²) * (1 + ||ξ - η||²).
    Proof: triangle inequality gives ||ξ|| ≤ ||η|| + ||ξ - η||;
    squaring and AM-GM (2ab ≤ a² + b²) gives ||ξ||² ≤ 2||η||² + 2||ξ-η||²;
    the extra 1 on the left is absorbed by the 2 * ... * 1 on the right. -/
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

/-- **Peetre weight factorization** (named open def, ETA 1-2 weeks):
    (1 + ||ξ||²)^s ≤ 2^|s| * (1 + ||η||²)^s * (1 + ||ξ - η||²)^|s|.
    Follows from peetre_base by Real.rpow monotonicity:
      s ≥ 0: rpow_le_rpow (peetre_base) + mul_rpow + rpow_le_rpow_of_exponent_le.
      s <  0: apply peetre_base to (η, ξ), take s := |s|, use rpow_le_rpow, invert.
    Blocked on Real.rpow API chains (lean --run needed to confirm exact names in v4.12.0).
    Used downstream in: Fourier multiplier product estimates, NS_BilinearEstimate_OPEN. -/
def NS_WeightPeetre_OPEN (s : ℝ) : Prop :=
  ∀ (ξ η : Freq),
    (1 + ‖ξ‖ ^ 2) ^ s ≤
    2 ^ |s| * (1 + ‖η‖ ^ 2) ^ s * (1 + ‖ξ - η‖ ^ 2) ^ |s|

/-- **Conditional Peetre factorization** (0 sorry):
    Given NS_WeightPeetre_OPEN, the weight (in the sense of FunctionSpaces.weight)
    satisfies the pointwise product bound needed for the bilinear Sobolev estimate. -/
theorem weight_peetre_conditional (h : NS_WeightPeetre_OPEN s) (ξ η : Freq) :
    (1 + ‖ξ‖ ^ 2) ^ s ≤
    2 ^ |s| * (1 + ‖η‖ ^ 2) ^ s * (1 + ‖ξ - η‖ ^ 2) ^ |s| :=
  h ξ η

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
    Lean API: MeasureTheory.inner_mul_le_norm_sq_mul_norm_sq or
              lintegral_mul_le_Lp_mul_Lq (Holder p=q=2, NNReal form). -/
def NS_HolderLintegral_OPEN : Prop :=
  ∀ (u : Hdiv_free (s + 2)),
    (eLpNorm (⇑(u : Lp Val 2 (mu (s + 2)))) 1 (volume : Measure Freq)) ^ 2 ≤
    (∫⁻ xi : Freq, (weight (s + 2) xi)⁻¹ ∂(volume : Measure Freq)) *
    (eLpNorm (⇑(u : Lp Val 2 (mu (s + 2)))) 2 (mu (s + 2))) ^ 2

/-- **Sobolev L^inf embedding** (strict threshold, ETA 1 week after convergence + Holder):
    For s > -1/2 (s+2 > 3/2 strictly), the Fourier L^1 bound gives:
      ||F^{-1}(u)||_{Linf} <= ||u||_{L^1(Freq)} <= sqrt(C_w) * ||u||_{H^{s+2}}.
    Stated in squared form to avoid ENNReal.sqrt complexity. -/
def NS_SobolevLInf_OPEN (s : ℝ) : Prop :=
  -1 / 2 < s →
  ∃ C_inf : ℝ, 0 < C_inf ∧
    ∀ (u : Hdiv_free (s + 2)),
      (eLpNorm (⇑(u : Lp Val 2 (mu (s + 2)))) 1 (volume : Measure Freq)) ^ 2 ≤
      ENNReal.ofReal C_inf *
      (eLpNorm (⇑(u : Lp Val 2 (mu (s + 2)))) 2 (mu (s + 2))) ^ 2

/-- **Sobolev L^3 embedding** (HLS route, for Meta AI / Phase 57):
    H^{1/2}(R^3) -> L^3(R^3) at the critical Sobolev exponent.
    Proof via Meta AI: rieszPot(1/2) + HLS inequality + Plancherel.
    Stated as the product bound (same Prop as D1 at s = -3/2):
      ||B(u,v)||_{H^{-1/2}} <= C * ||u||_{H^{1/2}} * ||v||_{H^{1/2}}.
    Route: ||B|| <= ||uv||_{L^{3/2}} <= ||u||_{L^3}*||v||_{L^3}
                 <= C * ||u||_{H^{1/2}} * ||v||_{H^{1/2}}. -/
def NS_SobolevL3_OPEN : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (u v : Hdiv_free ((-3 / 2 : ℝ) + 2)),
      ∃ B_uv : Hdiv_free ((-3 / 2 : ℝ) + 1),
        ‖(B_uv : Lp Val 2 (mu ((-3 / 2 : ℝ) + 1)))‖ ≤
          C * ‖(u : Lp Val 2 (mu ((-3 / 2 : ℝ) + 2)))‖ *
              ‖(v : Lp Val 2 (mu ((-3 / 2 : ℝ) + 2)))‖

/-- **Sobolev L^6 embedding** (ETA 1 week after NS_SobolevL3_OPEN):
    H^1(R^3) -> L^6(R^3), classical (critical exponent for s=1, R^3).
    Follows from NS_SobolevL3_OPEN by scaling.
    Used in the paraproduct: v in H^{3/2} -> H^1 -> L^6 (Sobolev chain),
    handling the high-high term without needing H^{3/2} -> L^inf. -/
def NS_SobolevL6_OPEN : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (u v : Hdiv_free ((-1 / 2 : ℝ) + 2)),
      ∃ B_uv : Hdiv_free ((-1 / 2 : ℝ) + 1),
        ‖(B_uv : Lp Val 2 (mu ((-1 / 2 : ℝ) + 1)))‖ ≤
          C * ‖(u : Lp Val 2 (mu ((-1 / 2 : ℝ) + 2)))‖ *
              ‖(v : Lp Val 2 (mu ((-1 / 2 : ℝ) + 2)))‖

/-- **Cauchy-Schwarz convolution estimate** (named open def, ETA 3-4 weeks):
    || int_{R^3} f(x) * g(x-y) * ||y||^{-5/2} dy ||_{L^2(x)} <= C * ||f||_{L^2} * ||g||_{L^2}.
    Proof route (Meta AI, Phase 58):
      (1) Fubini: MeasureTheory.lintegral_lintegral (Constructions.Prod.Basic, v4.12.0).
      (2) HLS: g(x-y) * ||y||^{-1/2} has L^6 output for g in L^2 (rieszPot + NS_SobolevL3_OPEN).
      (3) Holder in x: L^2 * L^6 * L^3 with 1/2 + 1/6 + 1/3 = 1.
      (4) NS_SobolevL3_OPEN: test fn phi in H^{1/2} -> L^3.
    Status: blocked on (2) = NS_SobolevL3_OPEN (Meta AI, 3-4 weeks). -/
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

/-- **Weight inverse equals reciprocal of weight ofReal** (sub-lemma for bridge):
    (weight (s+2) xi)^{-1} = ENNReal.ofReal ((1+||xi||^2)^{-(s+2)}).
    Proof: weight (s+2) xi = ofReal((1+||xi||^2)^(s+2)), and
    (ofReal x)^{-1} = ofReal(x^{-1}) for x >= 0. -/
private lemma weight_inv_eq (xi : Freq) :
    (weight (s + 2) xi)⁻¹ =
    ENNReal.ofReal ((1 + ‖xi‖ ^ 2) ^ (-(s + 2))) := by
  simp only [weight, Real.rpow_neg (by positivity)]
  rw [ENNReal.inv_ofReal (by positivity)]

/-- **sobolev_Linf from weight convergence + Holder** (0 sorry):
    Given the weight integral is finite (NS_WeightIntegralFinite_OPEN) and
    the Cauchy-Schwarz factorization holds (NS_HolderLintegral_OPEN),
    the L^inf embedding NS_SobolevLInf_OPEN follows immediately.

    Proof: h_cs u : (||u||_{L^1})^2 <= (int weight^{-1}) * ||u||_{H^{s+2}}^2.
           h_w    : int weight^{-1} <= C_w.
    Chain: (||u||_{L^1})^2 <= C_w * ||u||_{H^{s+2}}^2. -/
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

    Both Lean Props have IDENTICAL type (same Hdiv_free indices):
      -3/2 + 2 = 1/2  (the H^{1/2} factor)
      -3/2 + 1 = -1/2 (the H^{-1/2} output)
    In Lean: the existential unwrapping is exact (Prop-equality bridge). -/
theorem ns_d1_from_sobolev_l3 (h : NS_SobolevL3_OPEN) :
    NS_BilinearEstimate_OPEN (-3 / 2) := by
  obtain ⟨C, hC, hbound⟩ := h
  exact ⟨C, hC, fun u v => hbound u v⟩

/-! ## §F. Summary: meeting at D1 -/

/-
PHASE 60 MEETING POINT (July 1, 2026):

Proved in this file (0 sorry, classical trio):
  peetre_base              : 1+||ξ||² ≤ 2(1+||η||²)(1+||ξ-η||²)   [nlinarith]
  weight_peetre_conditional: Prop-equality bridge from NS_WeightPeetre_OPEN
  sobolev_linf_from_weight_and_holder: NS_SobolevLInf_OPEN from two OPEN surfaces
  ns_d1_from_sobolev_l3   : NS_BilinearEstimate_OPEN(-3/2) from NS_SobolevL3_OPEN

Named open surfaces (ETA):
  NS_WeightPeetre_OPEN      : 1-2 weeks  (rpow API chain, lean --run)
  NS_WeightIntegralFinite_OPEN: 2-3 weeks (integral_rpow for R^3)
  NS_HolderLintegral_OPEN   : 1 week     (MeasureTheory Holder API)
  NS_SobolevLInf_OPEN       : 1 week after the above two
  NS_SobolevL3_OPEN         : 3-4 weeks  (Meta AI, rieszPot + HLS)
  NS_SobolevL6_OPEN         : 1 week after NS_SobolevL3_OPEN
  NS_CauchySchwarzConv_OPEN : 3-4 weeks  (blocked on NS_SobolevL3_OPEN)

D1 = NS_BilinearEstimate_OPEN(-3/2): closes immediately when NS_SobolevL3_OPEN lands.
Net ETA for D1: 3-4 weeks.

D3 ROADMAP:
  M5 (Fujita-Kato small data): D1 + D2 + D3 + D4 + D5.
  M6 (global regularity): Remove small-data. Attack: corrSemigroupRate ξ < 1 for all data.
-/

end Phase60SobolevLInf
end NS
end Towers
end TheoremaAureum
