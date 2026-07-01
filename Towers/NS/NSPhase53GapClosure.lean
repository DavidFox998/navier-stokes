/-
================================================================
Towers / NS / NSPhase53GapClosure  --  NS Tower 540, Phase 53

CLOSING GAPS 1 AND 2 FROM PHASE 52 D5 MASTER BRIDGE

Gap 1: NS_PicardSpaceComplete_OPEN  -- CLOSED here (0 sorry, classical trio)
Gap 2: NS_BanachFPT_OPEN            -- CLOSED here (0 sorry, classical trio)

Gap 3 (NS_ContinuationPrinciple_OPEN): ILL-FORMED — missing WeakNS hypothesis.
  Corrected formulation NS_ContinuationPrincipleV2_OPEN in Phase 54.
Gap 4 (NS_MildToWeak_OPEN): REDUCES to D4 (trivial bridge).
Gap 5 (NS_PicardMapWellDef_OPEN): REDUCES to D2 + corrSem contraction.

STRATEGY GAP 1:
  Hdiv_free (s+2) has CompleteSpace (proved in FunctionSpaces.lean via
  divFreeSubmodule_isComplete + instCompleteSpaceDivFree).
  A pointwise Cauchy sequence has a pointwise limit by
  cauchySeq_tendsto_of_complete. Classical.choice picks the limit function.

STRATEGY GAP 2:
  Picard iterates u₀ = 0, u_{n+1} = Φ(u_n).
  (A) Inductive bound:  ‖u_{n+1}(t) - u_n(t)‖_{Lp} ≤ (1/2)^n · D(t)
  (B) Triangle bound:   ‖u_{m+k}(t) - u_m(t)‖_{Lp} ≤ Σ_{j<k} (1/2)^{m+j} · D(t)
  (C) Geometric bound:  Σ_{j<k} (1/2)^{m+j} ≤ 2 · (1/2)^m
  (D) Pointwise Cauchy: (1/2)^m → 0 via tendsto_pow_atTop_nhds_zero_of_lt_one
  (E) Limit:            CompleteSpace (Hdiv_free (s+2)) → limit u* pointwise
  (F) Fixed point:      Lipschitz continuity + tendsto_nhds_unique

KEY FIX vs prior draft:
  Triangle inequality uses norm_add_le after writing difference as a sum,
  NOT norm_sub_le (which is ‖a−b‖ ≤ ‖a‖+‖b‖, not the triangle inequality).

Axioms: {propext, Classical.choice, Quot.sound}   (classical trio only)
Sorry count: 0
================================================================
-/

import Towers.NS.NSPhase52D5MasterBridge

open Filter Topology Real MeasureTheory
open scoped BigOperators ENNReal
open TheoremaAureum.Towers.NS.FunctionSpaces
open TheoremaAureum.Towers.NS.WeakSolution
open TheoremaAureum.Towers.NS.Regularity
open TheoremaAureum.Towers.NS.D5MasterBridge

namespace TheoremaAureum
namespace Towers
namespace NS
namespace Phase53GapClosure

variable {s : ℝ}

/-!
## §A.  Norm / coercion bridge: Hdiv_free ↪ Lp (isometric embedding)

Hdiv_free (s) = ↥(divFreeSubmodule s) is a Submodule of Lp Val 2 (mu s).
Its NormedAddCommGroup instance is `inferInstanceAs (NormedAddCommGroup (↥M))`,
so every norm in Hdiv_free equals the ambient Lp norm.
-/

/-- Coercion of subtraction: (u − v : Hdiv_free) → (u : Lp) − (v : Lp). -/
private lemma hdiv_coe_sub (s : ℝ) (u v : Hdiv_free s) :
    ((u - v : Hdiv_free s) : Lp Val 2 (mu s)) =
    (u : Lp Val 2 (mu s)) - (v : Lp Val 2 (mu s)) :=
  AddSubgroupClass.coe_sub u v

/-- Norm in Hdiv_free = Lp norm of the coercion (inherited norm). -/
private lemma hdiv_norm_eq_lp (s : ℝ) (u : Hdiv_free s) :
    ‖u‖ = ‖(u : Lp Val 2 (mu s))‖ := rfl

/-- Distance in Hdiv_free = Lp norm of the coerced difference. -/
private lemma hdiv_dist_eq_lp (s : ℝ) (u v : Hdiv_free s) :
    dist u v =
    ‖(u : Lp Val 2 (mu s)) - (v : Lp Val 2 (mu s))‖ := by
  rw [dist_eq_norm, hdiv_norm_eq_lp, hdiv_coe_sub]

/-!
## §B.  Geometric series lemmas
-/

/-- ∑_{j<k} (1/2)^j ≤ 2  (partial sum ≤ tsum). -/
private lemma geom_partial_le_two (k : ℕ) :
    ∑ j ∈ Finset.range k, (1 / 2 : ℝ) ^ j ≤ 2 := by
  have hsum : Summable (fun j : ℕ => (1 / 2 : ℝ) ^ j) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  calc ∑ j ∈ Finset.range k, (1 / 2 : ℝ) ^ j
      ≤ ∑' j : ℕ, (1 / 2 : ℝ) ^ j :=
        sum_le_tsum (Finset.range k) (fun j _ => by positivity) hsum
    _ = (1 - 1 / 2)⁻¹ :=
        tsum_geometric_of_lt_one (by norm_num) (by norm_num)
    _ = 2 := by norm_num

/-- ∑_{j<k} (1/2)^(m+j) ≤ 2 · (1/2)^m. -/
private lemma geom_shifted_le (m k : ℕ) :
    ∑ j ∈ Finset.range k, (1 / 2 : ℝ) ^ (m + j) ≤ 2 * (1 / 2 : ℝ) ^ m := by
  have h1 : ∑ j ∈ Finset.range k, (1 / 2 : ℝ) ^ (m + j) =
      (1 / 2 : ℝ) ^ m * ∑ j ∈ Finset.range k, (1 / 2 : ℝ) ^ j := by
    simp_rw [pow_add, Finset.mul_sum]
  rw [h1]
  have h2 := geom_partial_le_two k
  have hpos : 0 ≤ (1 / 2 : ℝ) ^ m := by positivity
  nlinarith

/-!
## §C.  Triangle inequality for Lp norms

  ‖a − c‖ ≤ ‖a − b‖ + ‖b − c‖

  Written via a - c = (a - b) + (b - c) and norm_add_le.
-/

private lemma norm_sub_triangle {E : Type*} [SeminormedAddCommGroup E]
    (a b c : E) :
    ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := by
  calc ‖a - c‖ = ‖(a - b) + (b - c)‖ := by ring_nf
    _ ≤ ‖a - b‖ + ‖b - c‖ := norm_add_le _ _

/-!
## §D.  Gap 1: NS_PicardSpaceComplete_OPEN  (0 sorry)

CompleteSpace (Hdiv_free (s+2)) is proved in FunctionSpaces.lean.
Every pointwise Cauchy sequence has a pointwise limit.
-/

/-- **GAP 1 CLOSED** (0 sorry, classical trio).
    A pointwise-Cauchy sequence u_seq : ℕ → (ℝ → Hdiv_free (s+2)) has
    a pointwise limit u_lim with ‖u_seq n t − u_lim t‖_{Lp} → 0. -/
theorem ns_picard_space_complete (T : ℝ) :
    NS_PicardSpaceComplete_OPEN s T := by
  intro u_seq hCauchy
  -- Step 1: each n ↦ u_seq n t is Cauchy in the metric of Hdiv_free (s+2)
  have h_ptCauchy : ∀ t, 0 ≤ t → t ≤ T →
      CauchySeq (fun n => u_seq n t) := by
    intro t ht0 htT
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N₀, hN₀⟩ := hCauchy ε hε
    exact ⟨N₀, fun m n hm hn => by
      rw [hdiv_dist_eq_lp]
      exact hN₀ m n hm hn t ht0 htT⟩
  -- Step 2: CompleteSpace gives a limit
  have h_lim : ∀ t, 0 ≤ t → t ≤ T →
      ∃ l : Hdiv_free (s + 2),
        Filter.Tendsto (fun n => u_seq n t) Filter.atTop (nhds l) :=
    fun t ht0 htT =>
      cauchySeq_tendsto_of_complete (h_ptCauchy t ht0 htT)
  -- Step 3: pick limits classically
  refine ⟨fun t =>
      if ht : 0 ≤ t ∧ t ≤ T
      then Classical.choose (h_lim t ht.1 ht.2)
      else 0,
      fun t ht0 htT => ?_⟩
  simp only [dif_pos ⟨ht0, htT⟩]
  set l := Classical.choose (h_lim t ht0 htT)
  have htend : Filter.Tendsto (fun n => u_seq n t) Filter.atTop (nhds l) :=
    Classical.choose_spec (h_lim t ht0 htT)
  -- Step 4: norm convergence in Lp from Tendsto in Hdiv_free
  have hsub : Filter.Tendsto (fun n => u_seq n t - l)
      Filter.atTop (nhds (0 : Hdiv_free (s + 2))) := by
    have := htend.sub_const l; simpa using this
  have hnorm : Filter.Tendsto (fun n => ‖u_seq n t - l‖)
      Filter.atTop (nhds 0) := by
    simpa using hsub.norm
  refine hnorm.congr (fun n => ?_)
  rw [hdiv_norm_eq_lp, hdiv_coe_sub]

/-!
## §E.  Gap 2: NS_BanachFPT_OPEN  (0 sorry)

Explicit Picard iteration + CompleteSpace + Lipschitz squeeze.
-/

/-- **GAP 2 CLOSED** (0 sorry, classical trio).
    A (1/2)-contracting map on ℝ → Hdiv_free (s+2) has a pointwise fixed point.
    Proof: Picard iterates + geometric series + CompleteSpace + Lipschitz limit. -/
theorem ns_banach_fpt_proved (T₀ : ℝ) (hT₀ : 0 < T₀) :
    NS_BanachFPT_OPEN s T₀ := by
  intro Φ hΦ
  -- Define Picard iterates: u₀ = 0, u_{n+1} = Φ(u_n)
  let u : ℕ → ℝ → Hdiv_free (s + 2)
    | 0 => fun _ => 0
    | n + 1 => Φ (u n)
  -- The "step size" at time t: D(t) = ‖u 1 t − u 0 t‖_{Lp}
  -- (Note u 0 t = 0, so D(t) = ‖Φ(0) t‖_{Lp})
  /-──────────────────────────────────────────────
    Step A. Inductive difference bound (induction on n):
      ‖u (n+1) t − u n t‖_{Lp} ≤ (1/2)^n · D(t)
  ──────────────────────────────────────────────-/
  have h_diff : ∀ n t, 0 ≤ t → t ≤ T₀ →
      ‖(u (n + 1) t : Lp Val 2 (mu (s + 2))) - (u n t : Lp Val 2 (mu (s + 2)))‖ ≤
      (1 / 2) ^ n *
        ‖(u 1 t : Lp Val 2 (mu (s + 2))) - (u 0 t : Lp Val 2 (mu (s + 2)))‖ := by
    intro n
    induction n with
    | zero => intro t _ _; simp [u]
    | succ n ih =>
      intro t ht0 htT₀
      -- u (n+2) t = Φ(u (n+1)) t,  u (n+1) t = Φ(u n) t
      calc ‖(u (n + 2) t : Lp Val 2 (mu (s + 2))) -
            (u (n + 1) t : Lp Val 2 (mu (s + 2)))‖
          = ‖(Φ (u (n + 1)) t : Lp Val 2 (mu (s + 2))) -
             (Φ (u n) t : Lp Val 2 (mu (s + 2)))‖ := rfl
        _ ≤ (1 / 2) * ‖(u (n + 1) t : Lp Val 2 (mu (s + 2))) -
                       (u n t : Lp Val 2 (mu (s + 2)))‖ :=
            hΦ (u (n + 1)) (u n) t ht0 htT₀
        _ ≤ (1 / 2) * ((1 / 2) ^ n *
              ‖(u 1 t : Lp Val 2 (mu (s + 2))) - (u 0 t : Lp Val 2 (mu (s + 2)))‖) :=
            mul_le_mul_of_nonneg_left (ih t ht0 htT₀) (by norm_num)
        _ = (1 / 2) ^ (n + 1) *
              ‖(u 1 t : Lp Val 2 (mu (s + 2))) - (u 0 t : Lp Val 2 (mu (s + 2)))‖ := by ring
  /-──────────────────────────────────────────────
    Step B. Triangle bound by induction on k:
      ‖u (m+k) t − u m t‖_{Lp} ≤ [Σ_{j<k} (1/2)^{m+j}] · D(t)
    Uses norm_sub_triangle (= norm_add_le after rewrite).
  ──────────────────────────────────────────────-/
  have h_tri_bd : ∀ m k t, 0 ≤ t → t ≤ T₀ →
      ‖(u (m + k) t : Lp Val 2 (mu (s + 2))) - (u m t : Lp Val 2 (mu (s + 2)))‖ ≤
      (∑ j ∈ Finset.range k, (1 / 2 : ℝ) ^ (m + j)) *
        ‖(u 1 t : Lp Val 2 (mu (s + 2))) - (u 0 t : Lp Val 2 (mu (s + 2)))‖ := by
    intro m k
    induction k with
    | zero => intro t _ _; simp
    | succ k ihk =>
      intro t ht0 htT₀
      -- u(m+k+1) t − u m t = [u(m+k+1) t − u(m+k) t] + [u(m+k) t − u m t]
      have htri := norm_sub_triangle
        (u (m + (k + 1)) t : Lp Val 2 (mu (s + 2)))
        (u (m + k) t : Lp Val 2 (mu (s + 2)))
        (u m t : Lp Val 2 (mu (s + 2)))
      -- Bound each piece
      have hstep : ‖(u (m + (k + 1)) t : Lp Val 2 (mu (s + 2))) -
          (u (m + k) t : Lp Val 2 (mu (s + 2)))‖ ≤
          (1 / 2) ^ (m + k) *
            ‖(u 1 t : Lp Val 2 (mu (s + 2))) - (u 0 t : Lp Val 2 (mu (s + 2)))‖ := by
        have : m + (k + 1) = m + k + 1 := by ring
        rw [this]; exact h_diff (m + k) t ht0 htT₀
      have hprev := ihk t ht0 htT₀
      calc ‖(u (m + (k + 1)) t : Lp Val 2 (mu (s + 2))) -
            (u m t : Lp Val 2 (mu (s + 2)))‖
          ≤ ‖(u (m + (k + 1)) t : Lp Val 2 (mu (s + 2))) -
             (u (m + k) t : Lp Val 2 (mu (s + 2)))‖ +
            ‖(u (m + k) t : Lp Val 2 (mu (s + 2))) -
             (u m t : Lp Val 2 (mu (s + 2)))‖ := htri
        _ ≤ (1 / 2) ^ (m + k) *
                ‖(u 1 t : Lp Val 2 (mu (s + 2))) - (u 0 t : Lp Val 2 (mu (s + 2)))‖ +
            (∑ j ∈ Finset.range k, (1 / 2 : ℝ) ^ (m + j)) *
                ‖(u 1 t : Lp Val 2 (mu (s + 2))) - (u 0 t : Lp Val 2 (mu (s + 2)))‖ :=
            add_le_add hstep hprev
        _ = (∑ j ∈ Finset.range (k + 1), (1 / 2 : ℝ) ^ (m + j)) *
                ‖(u 1 t : Lp Val 2 (mu (s + 2))) - (u 0 t : Lp Val 2 (mu (s + 2)))‖ := by
            rw [Finset.sum_range_succ]; ring
  /-──────────────────────────────────────────────
    Step C. Geometric bound: geom_shifted_le gives
      ‖u (m+k) t − u m t‖ ≤ 2 · (1/2)^m · D(t)
  ──────────────────────────────────────────────-/
  have h_geo : ∀ m k t, 0 ≤ t → t ≤ T₀ →
      ‖(u (m + k) t : Lp Val 2 (mu (s + 2))) - (u m t : Lp Val 2 (mu (s + 2)))‖ ≤
      2 * (1 / 2 : ℝ) ^ m *
        ‖(u 1 t : Lp Val 2 (mu (s + 2))) - (u 0 t : Lp Val 2 (mu (s + 2)))‖ := by
    intro m k t ht0 htT₀
    calc ‖(u (m + k) t : Lp Val 2 (mu (s + 2))) - (u m t : Lp Val 2 (mu (s + 2)))‖
        ≤ (∑ j ∈ Finset.range k, (1 / 2 : ℝ) ^ (m + j)) *
            ‖(u 1 t : Lp Val 2 (mu (s + 2))) - (u 0 t : Lp Val 2 (mu (s + 2)))‖ :=
          h_tri_bd m k t ht0 htT₀
      _ ≤ 2 * (1 / 2 : ℝ) ^ m *
            ‖(u 1 t : Lp Val 2 (mu (s + 2))) - (u 0 t : Lp Val 2 (mu (s + 2)))‖ :=
          mul_le_mul_of_nonneg_right (geom_shifted_le m k) (norm_nonneg _)
  /-──────────────────────────────────────────────
    Step D. Pointwise Cauchy: for each fixed t, n ↦ u n t is Cauchy.
    (1/2)^m → 0, so for m,n ≥ N₀: ‖u m t − u n t‖ < ε.
  ──────────────────────────────────────────────-/
  have h_ptCauchy : ∀ t, 0 ≤ t → t ≤ T₀ → CauchySeq (fun n => u n t) := by
    intro t ht0 htT₀
    rw [Metric.cauchySeq_iff]
    intro ε hε
    set D_t := ‖(u 1 t : Lp Val 2 (mu (s + 2))) - (u 0 t : Lp Val 2 (mu (s + 2)))‖
    -- Case D_t = 0: all iterates coincide with u 0 t = 0, distance is 0
    by_cases hDt : D_t = 0
    · refine ⟨0, fun m n _ _ => ?_⟩
      rw [hdiv_dist_eq_lp]
      -- ‖u m t − u n t‖ ≤ ‖u m t − u 0 t‖ + ‖u n t − u 0 t‖
      -- and ‖u k t − u 0 t‖ ≤ 2·(1/2)^0·D_t = 2·0 = 0
      have hm_zero : ‖(u m t : Lp Val 2 (mu (s + 2))) -
          (u 0 t : Lp Val 2 (mu (s + 2)))‖ = 0 := by
        have := h_geo 0 m t ht0 htT₀
        simp only [pow_zero, mul_one, Nat.zero_add] at this
        linarith [norm_nonneg ((u m t : Lp Val 2 (mu (s + 2))) -
          (u 0 t : Lp Val 2 (mu (s + 2)))),
          mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (norm_nonneg _)]
      have hn_zero : ‖(u n t : Lp Val 2 (mu (s + 2))) -
          (u 0 t : Lp Val 2 (mu (s + 2)))‖ = 0 := by
        have := h_geo 0 n t ht0 htT₀
        simp only [pow_zero, mul_one, Nat.zero_add] at this
        linarith [norm_nonneg ((u n t : Lp Val 2 (mu (s + 2))) -
          (u 0 t : Lp Val 2 (mu (s + 2)))),
          mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (norm_nonneg _)]
      -- ‖u m t − u n t‖ ≤ ‖u m t − 0‖ + ‖0 − u n t‖ = 0
      have htri := norm_sub_triangle
        (u m t : Lp Val 2 (mu (s + 2)))
        (u 0 t : Lp Val 2 (mu (s + 2)))
        (u n t : Lp Val 2 (mu (s + 2)))
      simp only [u, show (0 : Hdiv_free (s + 2)) = ⟨0, (divFreeSubmodule (s + 2)).zero_mem⟩
        from rfl] at hm_zero hn_zero ⊢
      linarith [norm_nonneg ((u m t : Lp Val 2 (mu (s + 2))) -
        (u n t : Lp Val 2 (mu (s + 2))))]
    · -- D_t > 0: use (1/2)^m → 0
      have hDt_pos : 0 < D_t := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hDt)
      -- (1/2)^N · 2 · D_t < ε  iff  (1/2)^N < ε / (2 · D_t)
      have hpow_zero :
          Filter.Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) Filter.atTop (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      have hε' : 0 < ε / (2 * D_t) := div_pos hε (mul_pos two_pos hDt_pos)
      obtain ⟨N₀, hN₀⟩ := (Metric.tendsto_atTop.mp hpow_zero) _ hε'
      refine ⟨N₀, fun m n hm hn => ?_⟩
      rw [hdiv_dist_eq_lp]
      -- WLOG m ≤ n (use symmetry otherwise)
      rcases le_or_lt m n with hmn | hmn
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
        calc ‖(u (m + k) t : Lp Val 2 (mu (s + 2))) -
              (u m t : Lp Val 2 (mu (s + 2)))‖
            ≤ 2 * (1 / 2 : ℝ) ^ m * D_t := h_geo m k t ht0 htT₀
          _ < ε := by
              have hN := hN₀ m hm
              simp only [Real.dist_eq, abs_of_nonneg (pow_nonneg (by norm_num) m)] at hN
              have hpow_pos : 0 < (1 / 2 : ℝ) ^ m := by positivity
              rw [div_lt_iff (mul_pos two_pos hDt_pos)] at hN
              linarith
      · -- n < m: use norm_sub_comm
        rw [norm_sub_comm]
        obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (le_of_lt hmn)
        calc ‖(u (n + k) t : Lp Val 2 (mu (s + 2))) -
              (u n t : Lp Val 2 (mu (s + 2)))‖
            ≤ 2 * (1 / 2 : ℝ) ^ n * D_t := h_geo n k t ht0 htT₀
          _ < ε := by
              have hN := hN₀ n hn
              simp only [Real.dist_eq, abs_of_nonneg (pow_nonneg (by norm_num) n)] at hN
              have hpow_pos : 0 < (1 / 2 : ℝ) ^ n := by positivity
              rw [div_lt_iff (mul_pos two_pos hDt_pos)] at hN
              linarith
  /-──────────────────────────────────────────────
    Step E. Completeness: get pointwise limit u_star.
  ──────────────────────────────────────────────-/
  have h_lim : ∀ t, 0 ≤ t → t ≤ T₀ →
      ∃ l : Hdiv_free (s + 2),
        Filter.Tendsto (fun n => u n t) Filter.atTop (nhds l) :=
    fun t ht0 htT₀ =>
      cauchySeq_tendsto_of_complete (h_ptCauchy t ht0 htT₀)
  -- Pick the limit function classically
  let u_star : ℝ → Hdiv_free (s + 2) :=
    fun t =>
      if ht : 0 ≤ t ∧ t ≤ T₀
      then Classical.choose (h_lim t ht.1 ht.2)
      else 0
  /-──────────────────────────────────────────────
    Step F. Fixed-point: Φ(u_star)(t) = u_star(t) for t ∈ [0,T₀].

    From:
      u n t → u_star t       (completeness, call this htend)
      Φ(u n)(t) → Φ(u_star)(t)  (Lipschitz squeeze: ‖Φ(u n)t − Φ(u*) t‖
                                 ≤ (1/2)·‖u n t − u* t‖ → 0)
      Φ(u n)(t) = u (n+1)(t) → u_star t  (shift)
    Uniqueness: Φ(u_star)(t) = u_star t.
  ──────────────────────────────────────────────-/
  refine ⟨u_star, fun t ht0 htT₀ => ?_⟩
  simp only [u_star, dif_pos ⟨ht0, htT₀⟩]
  set l := Classical.choose (h_lim t ht0 htT₀)
  have htend : Filter.Tendsto (fun n => u n t) Filter.atTop (nhds l) :=
    Classical.choose_spec (h_lim t ht0 htT₀)
  -- Norm convergence: ‖u n t − l‖_{Lp} → 0
  have htend_lp : Filter.Tendsto
      (fun n => ‖(u n t : Lp Val 2 (mu (s + 2))) - (l : Lp Val 2 (mu (s + 2)))‖)
      Filter.atTop (nhds 0) := by
    have hsub : Filter.Tendsto (fun n => u n t - l) Filter.atTop
        (nhds (0 : Hdiv_free (s + 2))) := by
      have := htend.sub_const l; simpa using this
    exact (hsub.norm.congr (fun n => by rw [hdiv_norm_eq_lp, hdiv_coe_sub])
        (by simp)).symm.mp (by simpa using hsub.norm)
  -- u_star t = l in Lp (by construction)
  have hstar_eq : (u_star t : Lp Val 2 (mu (s + 2))) = (l : Lp Val 2 (mu (s + 2))) := by
    simp [u_star, dif_pos ⟨ht0, htT₀⟩]
  -- ‖Φ(u n)(t) − Φ(u_star)(t)‖_{Lp} ≤ (1/2)·‖u n t − l‖_{Lp} → 0
  have hΦ_squeeze : Filter.Tendsto
      (fun n => ‖(Φ (u n) t : Lp Val 2 (mu (s + 2))) -
                 (Φ u_star t : Lp Val 2 (mu (s + 2)))‖)
      Filter.atTop (nhds 0) :=
    squeeze_zero (fun n => norm_nonneg _)
      (fun n => by
        have h := hΦ (u n) u_star t ht0 htT₀
        rwa [hstar_eq] at h)
      (htend_lp.const_mul (1 / 2) |>.congr (fun n => by ring) (by simp))
  -- Φ(u n)(t) → Φ(u_star)(t) in Lp
  have hΦ_tend : Filter.Tendsto
      (fun n => (Φ (u n) t : Lp Val 2 (mu (s + 2))))
      Filter.atTop (nhds (Φ u_star t : Lp Val 2 (mu (s + 2)))) := by
    rw [tendsto_iff_norm_tendsto_zero]
    exact hΦ_squeeze
  -- Φ(u n)(t) = u (n+1)(t), so Φ(u n)(t) → l (same limit, shifted index)
  have hshift : Filter.Tendsto
      (fun n => (u (n + 1) t : Lp Val 2 (mu (s + 2))))
      Filter.atTop (nhds (l : Lp Val 2 (mu (s + 2)))) := by
    -- (fun n => u (n+1) t) = (fun n => u n t) ∘ (· + 1), which still → l
    have hcomp := htend.comp
      (tendsto_atTop_atTop.mpr (fun N => ⟨N, fun n hn => Nat.le_add_right n 1 |>.trans (by omega)⟩))
    convert hcomp using 1
    · ext n; rfl
    · simp [Function.comp]
  -- u (n+1)(t) = Φ(u n)(t), so Φ(u n)(t) → l
  have hΦ_to_l : Filter.Tendsto
      (fun n => (Φ (u n) t : Lp Val 2 (mu (s + 2))))
      Filter.atTop (nhds (l : Lp Val 2 (mu (s + 2)))) :=
    hshift.congr (fun n => rfl)
  -- Uniqueness: Φ(u_star)(t) = l
  exact (tendsto_nhds_unique hΦ_tend hΦ_to_l).symm

/-!
## §F.  Certification aliases
-/

/-- Gap 1 closed. -/
theorem gap1_closed (T : ℝ) : NS_PicardSpaceComplete_OPEN s T :=
  ns_picard_space_complete T

/-- Gap 2 closed (given T₀ > 0, which is always the case for Fujita-Kato T₀). -/
theorem gap2_closed (T₀ : ℝ) (hT₀ : 0 < T₀) : NS_BanachFPT_OPEN s T₀ :=
  ns_banach_fpt_proved T₀ hT₀

end Phase53GapClosure
end NS
end Towers
end TheoremaAureum
