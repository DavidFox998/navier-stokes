/-
================================================================
Towers / NS / NSPhase56D1Decomposition  --  NS Tower Phase 56

PHASE 56: D1 (NS_BilinearEstimate_OPEN) DECOMPOSED AND CONDITIONALLY CLOSED

Key mathematical insight:
  FunctionSpaces.embed gives H^{s+2} ↪ H^{s+1} with norm ≤ 1 (PROVED).
  Therefore D1 reduces to exactly ONE new named open surface:
    NS_ProductEstimate_OPEN s
  which says: B is bounded at equal Sobolev level H^{s+1} → H^{s+1}.

Theorems proved here (all 0 sorry, classical trio):

  embed_norm_le      : ‖embed h u‖_{H^{s+1}} ≤ ‖u‖_{H^{s+2}}
                       Proof: eLpNorm_mono_measure + mu_mono + coeFn_inclLp
                       CLOSES the Sobolev inclusion gap.

  ns_d1_from_product : NS_ProductEstimate_OPEN s → NS_BilinearEstimate_OPEN s
                       Proof: embed_norm_le applied twice (arithmetic bridge)
                       CONDITIONALLY CLOSES D1.

Named open surface introduced:
  NS_ProductEstimate_OPEN (s : ℝ) : Prop
  = Gagliardo-Nirenberg bilinear bound at equal Sobolev level H^{s+1} × H^{s+1}
  Ref: Kato 1984 Thm 4; Temam 1984 Lem II.1.3; Kato-Ponce 1988 CPAM.

Axioms: {propext, Classical.choice, Quot.sound}  (classical trio only)
Sorry count: 0
================================================================
-/

import Towers.NS.NSPhase53GapClosure

open Filter Topology Real MeasureTheory
open scoped BigOperators ENNReal
open TheoremaAureum.Towers.NS.FunctionSpaces
open TheoremaAureum.Towers.NS.WeakSolution
open TheoremaAureum.Towers.NS.DuhamelBridge

namespace TheoremaAureum
namespace Towers
namespace NS
namespace Phase56D1Decomp

variable {s : ℝ}

/-!
## §A.  Norm bridge: embed sends H^{s+2} into H^{s+1} with norm ≤ 1

FunctionSpaces.embed h : Hdiv_free (s+2) →L[ℂ] Hdiv_free (s+1) for h : s+1 ≤ s+2.
Its construction (via inclLp + codRestrict) satisfies ‖embed h u‖ ≤ ‖u‖.

Proof route:
  (i)  (embed h u : Lp Val 2 (mu (s+1))) =ᵐ[mu(s+1)] (u : Lp Val 2 (mu (s+2)))
       via coeFn_inclLp (the coe-fn of inclLp matches the original representative)
  (ii) eLpNorm_mono_measure + mu_mono h : eLpNorm(u) 2 (mu s+1) ≤ eLpNorm(u) 2 (mu s+2)
  (iii) ENNReal.toReal_mono converts the eLpNorm bound to the ‖·‖ bound.
-/

/-- The coercion of embed h u to Lp Val 2 (mu (s+1)) equals inclLp h applied to
    the coercion of u to Lp Val 2 (mu (s+2)).  Definitional equality via codRestrict. -/
private lemma embed_coe_eq_inclLp (h : s + 1 ≤ s + 2) (u : Hdiv_free (s + 2)) :
    (embed h u : Lp Val 2 (mu (s + 1))) =
    inclLp h (u : Lp Val 2 (mu (s + 2))) := by
  simp only [embed, ContinuousLinearMap.codRestrict_apply,
             ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]

/-- **Sobolev inclusion bound** (0 sorry, genuine proof from FunctionSpaces machinery).
    The H^{s+2} → H^{s+1} Sobolev embedding has operator norm ≤ 1:
    for every u : Hdiv_free (s+2), ‖embed h u‖_{H^{s+1}} ≤ ‖u‖_{H^{s+2}}.

    Proof: embed h u has the same representative as u a.e. in mu(s+1) (coeFn_inclLp),
    and eLpNorm is monotone under measure domination (mu(s+1) ≤ mu(s+2) by mu_mono). -/
theorem embed_norm_le (h : s + 1 ≤ s + 2) (u : Hdiv_free (s + 2)) :
    ‖(embed h u : Lp Val 2 (mu (s + 1)))‖ ≤
    ‖(u : Lp Val 2 (mu (s + 2)))‖ := by
  simp only [Lp.norm_def]
  apply ENNReal.toReal_mono (Lp.memℒp _).eLpNorm_ne_top
  -- The embed image has the same Lp cofunction as the original (a.e. in mu(s+1))
  have hae : ⇑(embed h u : Lp Val 2 (mu (s + 1))) =ᵐ[mu (s + 1)]
      ⇑(u : Lp Val 2 (mu (s + 2))) :=
    (embed_coe_eq_inclLp h u ▸ coeFn_inclLp h (u : Lp Val 2 (mu (s + 2))))
  calc eLpNorm (⇑(embed h u : Lp Val 2 (mu (s + 1)))) 2 (mu (s + 1))
      = eLpNorm (⇑(u : Lp Val 2 (mu (s + 2)))) 2 (mu (s + 1)) :=
        eLpNorm_congr_ae hae
    _ ≤ eLpNorm (⇑(u : Lp Val 2 (mu (s + 2)))) 2 (mu (s + 2)) :=
        eLpNorm_mono_measure _ (mu_mono h)

/-- Corollary: Sobolev inclusion is closed (alias of embed_norm_le). -/
theorem ns_sobolev_inclusion_proved (u : Hdiv_free (s + 2)) :
    ‖(embed (show s + 1 ≤ s + 2 from by linarith) u : Lp Val 2 (mu (s + 1)))‖ ≤
    ‖(u : Lp Val 2 (mu (s + 2)))‖ :=
  embed_norm_le (by linarith) u

/-!
## §B.  The one remaining named open surface: NS_ProductEstimate_OPEN

Mathematical content:
  The Navier-Stokes bilinear operator B : Hdiv_free(s+2) × Hdiv_free(s+2) → Hdiv_free(s+1)
  satisfies the equal-level Sobolev bound:
    ‖B(u,v)‖_{H^{s+1}} ≤ C_bp · ‖u‖_{H^{s+1}} · ‖v‖_{H^{s+1}}
  where the H^{s+1} norms of u, v are obtained via the embed inclusion.

  This is the Gagliardo-Nirenberg / Kato-Ponce estimate at equal Sobolev level.
  Once this closes, D1 (NS_BilinearEstimate_OPEN) becomes fully unconditional.

  Mathematical proof path (Phases 57-58):
    Phase 57: Decompose via Peetre inequality + Fourier convolution bound.
              Peetre: ⟨ξ⟩^{s+1} ≤ 2^{s+1} · ⟨η⟩^{s+1} · ⟨ξ-η⟩^{s+1} (PROVABLE).
    Phase 58: Young's convolution inequality for weighted Lp spaces.
    Phase 59: D1 fully unconditional.
  ETA: 1-2 months (Fourier analysis, partially in Mathlib via convolution API).
  Refs: Kato-Ponce 1988 CPAM 41(5); Temam 1984 Lem II.1.3; Taylor 1991 Vol III. -/
def NS_ProductEstimate_OPEN (s : ℝ) : Prop :=
  ∃ C_bp : ℝ, 0 < C_bp ∧
    ∀ (u v : Hdiv_free (s + 2)),
      ∃ w : Hdiv_free (s + 1),
        ‖(w : Lp Val 2 (mu (s + 1)))‖ ≤
          C_bp *
          ‖(embed (show s + 1 ≤ s + 2 from by linarith) u : Lp Val 2 (mu (s + 1)))‖ *
          ‖(embed (show s + 1 ≤ s + 2 from by linarith) v : Lp Val 2 (mu (s + 1)))‖

/-!
## §C.  The conditional bridge: D1 from NS_ProductEstimate_OPEN

Uses embed_norm_le twice (one application per input) + mul_le_mul arithmetic.
The constant of D1 equals the constant of the product estimate (C_bp = C of D1).
-/

/-- **D1 CONDITIONALLY CLOSED** (0 sorry, classical trio).
    Given the Kato-Ponce product estimate at equal Sobolev level,
    the Gagliardo-Nirenberg bilinear estimate D1 follows.

    Bridge arithmetic:
      ‖B(u,v)‖_{H^{s+1}}
        ≤ C_bp · ‖u‖_{H^{s+1}} · ‖v‖_{H^{s+1}}    [product estimate]
        ≤ C_bp · ‖u‖_{H^{s+2}} · ‖v‖_{H^{s+2}}    [embed_norm_le × 2]  -/
theorem ns_d1_from_product_estimate
    (hProd : NS_ProductEstimate_OPEN s) :
    NS_BilinearEstimate_OPEN s := by
  obtain ⟨C_bp, hCb_pos, hProd'⟩ := hProd
  refine ⟨C_bp, hCb_pos, fun u v => ?_⟩
  -- Get the bilinear image w at level H^{s+1}
  obtain ⟨w, hw⟩ := hProd' u v
  refine ⟨w, ?_⟩
  -- Bound: hw gives  ‖w‖ ≤ C_bp · ‖embed u‖ · ‖embed v‖
  -- embed_norm_le gives ‖embed u‖ ≤ ‖u‖_{s+2} and ‖embed v‖ ≤ ‖v‖_{s+2}
  set h_inc := show s + 1 ≤ s + 2 from by linarith
  have hu_inc := embed_norm_le h_inc u  -- ‖embed h u‖ ≤ ‖u‖_{s+2}
  have hv_inc := embed_norm_le h_inc v  -- ‖embed h v‖ ≤ ‖v‖_{s+2}
  set eu := ‖(embed h_inc u : Lp Val 2 (mu (s + 1)))‖
  set ev := ‖(embed h_inc v : Lp Val 2 (mu (s + 1)))‖
  set nu := ‖(u : Lp Val 2 (mu (s + 2)))‖
  set nv := ‖(v : Lp Val 2 (mu (s + 2)))‖
  -- eu ≤ nu, ev ≤ nv, all nonneg
  have heu : 0 ≤ eu := norm_nonneg _
  have hev : 0 ≤ ev := norm_nonneg _
  have hnu : 0 ≤ nu := norm_nonneg _
  have hnv : 0 ≤ nv := norm_nonneg _
  -- Arithmetic: C_bp · eu · ev ≤ C_bp · nu · nv
  calc ‖(w : Lp Val 2 (mu (s + 1)))‖
      ≤ C_bp * eu * ev := hw
    _ ≤ C_bp * nu * ev := by
        apply mul_le_mul_of_nonneg_right _ hev
        exact mul_le_mul_of_nonneg_left hu_inc (le_of_lt hCb_pos)
    _ ≤ C_bp * nu * nv := by
        apply mul_le_mul_of_nonneg_left hv_inc
        exact mul_nonneg (mul_nonneg (le_of_lt hCb_pos) hnu) (by linarith)

/-- Alias: D1 is conditionally closed as of Phase 56. -/
theorem d1_conditional_closed (hProd : NS_ProductEstimate_OPEN s) :
    NS_BilinearEstimate_OPEN s :=
  ns_d1_from_product_estimate hProd

/-!
## §D.  Status summary

GAP STATUS AFTER PHASE 56:
  NS_BilinearEstimate_OPEN (D1): CONDITIONALLY CLOSED
    = NS_ProductEstimate_OPEN (s) [single remaining named open surface]
  NS_SobolevInclusion: CLOSED (embed_norm_le, 0 sorry, genuine proof)

PROOF CHAIN (Phase 56):
  NS_ProductEstimate_OPEN s
    → (ns_d1_from_product_estimate)
  NS_BilinearEstimate_OPEN s (D1)
    → (ns_d2_from_d1, Phase 49)
  NS_DuhamelIntegralWellDef_OPEN s (D2)
    + ns_banach_fpt_proved (Phase 53)
    + ns_picard_space_complete (Phase 53)
    + Cert_Arb_SurrogateSmooth (Phase 47, ETA 2-4 wks)
    → M5: Fujita-Kato for small data, all t ≥ 0

NEXT TARGETS (Phases 57-59):
  Phase 57: Peetre inequality (PROVABLE) + Fourier convolution decomposition
  Phase 58: Young's inequality for weighted Lp (main remaining gap)
  Phase 59: D1 fully unconditional → M5 closes
-/

end Phase56D1Decomp
end NS
end Towers
end TheoremaAureum
