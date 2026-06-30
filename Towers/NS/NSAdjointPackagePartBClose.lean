/-
================================================================
Towers / NS / NSAdjointPackagePartBClose  --  Phase 30

Closes NS_AdjointPackage_PartB_OPEN (conditional on NS_WeakInitCont_OPEN).
Introduces NS_WeakInitCont_OPEN (one new Lean formalization gap).

STATEMENT (NS_AdjointPackage_PartB_OPEN s):
  For every WeakNS solution u (with u0, f=0) and NS_StokesMaxReg_OPEN,
  all test fields phi, and times T > 0:
    inner_{s+2}(u T, phi) = inner_{s+2}(corrSemigroup s T hT.le u0, phi)

PROOF (I(tau) route, 0 sorry, classical trio + NS_WeakInitCont_OPEN):

  Fix T > 0, u, u0, phi. Define
    I : R -> C   by   I(tau) = inner(u tau, corrSem(max 0 (T-tau)) phi)
  (corrSem uses max 0 form to match ns_b2_proved / NS_CorrSemigroupGenerator_PROVED).

  KEY: NS_CorrSemigroupGenerator_PROVED takes (t : R) (ht : 0 <= t) and produces
       HasDerivAt of fun t' => inner(corrSem(max 0 t') phi, test) at t.
       So call it as: NS_CorrSemigroupGenerator_PROVED (T-tau) hTtau_pos.le phi test.
       The max 0 form matches h_b2s exactly, making HasDerivAt.unique valid.

  STEP 1: HasDerivAt I 0 tau for tau in (0,T).
    Leibniz: I'(tau) = inner(D_u, corrSem(T-tau) phi) + inner(u tau, D_back * (-1))
    where D_back from ns_b2_proved (B.2 Bochner derivative).
    The two terms cancel via stokes_inner_conj_symm.

  STEP 2: I constant on (0,T) via MVT (C=0).
  STEP 3: I(T) = inner(u T, phi) [corrSem 0 = id, Part C].
  STEP 4: lim_{tau->0+} I(tau) = inner(u0, corrSem T phi) [NS_WeakInitCont_OPEN].
  CONCLUSION: inner(u T, phi) = inner(u0, corrSem T phi) = inner(corrSem T u0, phi) [Part A].

KEY PRIVATE LEMMAS (0 sorry, classical trio):
  stokes_inner_sym         -- inner_s(embed v', stokes v) = inner_s(stokes v', embed v) [Fourier]
  stokes_inner_conj_symm   -- inner_s(stokes v, embed v') = starRingEnd C (inner_s(stokes v', embed v))
  scalar_gen_deriv         -- scalar HasDerivAt from NS_CorrSemigroupGenerator_PROVED (.le call)

NEW NAMED OPEN DEF (Phase 30):
  NS_WeakInitCont_OPEN  -- inner(u tau, psi) -> inner(u0, psi) as tau -> 0+
    Route: WeakMomentum integral formulation; ETA 1-4 weeks.

Named open defs after Phase 30:
  NS_StokesMaxReg_OPEN    (~6-18 months)
  NS_WeakInitCont_OPEN    (NEW, ~1-4 weeks)

Author: David Fox | Date: May 21, 2026
Series: Opera Numerorum (internal: Battle Plan v1.6)
================================================================
-/

import Towers.NS.NSAdjointPackageClose
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup

open Real Set Filter Topology MeasureTheory
open scoped BigOperators ENNReal NNReal
open TheoremaAureum.Towers.NS.FunctionSpaces
open TheoremaAureum.Towers.NS.SemigroupDef
open TheoremaAureum.Towers.NS.CorrSemigroupSmooth
open TheoremaAureum.Towers.NS.GeneratorClose
open TheoremaAureum.Towers.NS.FourierInner
open TheoremaAureum.Towers.NS.AdjointPackageClose
open NSTower

namespace TheoremaAureum
namespace Towers
namespace NS
namespace AdjointPackagePartBClose

variable {s : ℝ}

/-! ## I. New named open def: NS_WeakInitCont_OPEN -/

/-- **[NAMED OPEN DEF] NS_WeakInitCont_OPEN -- Phase 30.**

    inner(u tau, psi) -> inner(u0, psi) as tau -> 0+ for any psi in Hdiv_free(s+2).

    MATHEMATICAL CONTENT: Leray-Hopf weak solutions are weakly L2-continuous at t=0.
    PROOF ROUTE: WeakNS.energy_le (||u tau|| bounded) + WeakMomentum integral at tau->0
    -> inner(u tau, phi) -> inner(u0, phi) for all phi.
    ETA: 1-4 weeks (moderate Lean API gap: distribution-theoretic initial data). -/
def NS_WeakInitCont_OPEN (s : ℝ) : Prop :=
  ∀ (u : ℝ → Hdiv_free (s + 2)) (u₀ : Hdiv_free (s + 2))
    (hweak : WeakNS u u₀ (fun _ => (0 : Hdiv_free (s + 2))))
    (ψ : Hdiv_free (s + 2)),
    Filter.Tendsto (fun τ => @inner ℂ (Hdiv_free (s + 2)) _ (u τ) ψ)
                   (nhdsWithin 0 (Set.Ioi 0))
                   (nhds (@inner ℂ (Hdiv_free (s + 2)) _ u₀ ψ))

/-! ## II. stokes_inner_sym: Fourier symmetry of the stokes bilinear form -/

/-- **Private: inner_s(embed v', stokes v) = inner_s(stokes v', embed v).**

    Proof (Fourier): Expand via inner_Hdiv_eq + L2.inner_def + coeFn_stokes_mult + coeFn_inclLp.
    LHS integrand: inner(v' xi, stokesSymbol xi . v xi) = stokesSymbol xi * inner(v' xi, v xi).
    RHS integrand: inner(stokesSymbol xi . v' xi, v xi)
                 = conj(stokesSymbol xi) * inner(v' xi, v xi)  [inner_smul_left]
                 = stokesSymbol xi * inner(v' xi, v xi)         [stokesSymbol real]. -/
private theorem stokes_inner_sym (s : ℝ) (v v' : Hdiv_free (s + 2)) :
    @inner ℂ (Hdiv_free s) _ (@embed (s + 2) s (by linarith) v') (stokes_op s v) =
    @inner ℂ (Hdiv_free s) _ (stokes_op s v') (@embed (s + 2) s (by linarith) v) := by
  simp only [inner_Hdiv_eq, L2.inner_def]
  apply integral_congr_ae
  have hSv : ((stokes_op s v : Hdiv_free s) : Lp Val 2 (mu s)) =ᵐ[mu s]
      fun ξ => stokesSymbol ξ • (v : Lp Val 2 (mu (s + 2))) ξ := by
    have h1 := coeFn_stokes_mult s (v : Lp Val 2 (mu (s + 2)))
    filter_upwards [h1] with ξ hξ
    simp only [stokes_op, ContinuousLinearMap.codRestrict_apply,
      ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]; exact hξ
  have hSv' : ((stokes_op s v' : Hdiv_free s) : Lp Val 2 (mu s)) =ᵐ[mu s]
      fun ξ => stokesSymbol ξ • (v' : Lp Val 2 (mu (s + 2))) ξ := by
    have h1 := coeFn_stokes_mult s (v' : Lp Val 2 (mu (s + 2)))
    filter_upwards [h1] with ξ hξ
    simp only [stokes_op, ContinuousLinearMap.codRestrict_apply,
      ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]; exact hξ
  have hEv : ((@embed (s + 2) s (by linarith) v : Hdiv_free s) : Lp Val 2 (mu s)) =ᵐ[mu s]
      (v : Lp Val 2 (mu (s + 2))) := coeFn_inclLp _ _
  have hEv' : ((@embed (s + 2) s (by linarith) v' : Hdiv_free s) : Lp Val 2 (mu s)) =ᵐ[mu s]
      (v' : Lp Val 2 (mu (s + 2))) := coeFn_inclLp _ _
  filter_upwards [hSv, hSv', hEv, hEv'] with ξ hsv hsv' hev hev'
  rw [hev', hsv, hev, hsv', inner_smul_right, inner_smul_left]
  congr 1
  simp only [stokesSymbol, map_ofReal, Complex.conj_ofReal]

/-! ## III. stokes_inner_conj_symm: conjugate symmetry -/

/-- **Private: inner_s(stokes v, embed v') = starRingEnd C (inner_s(stokes v', embed v)).**

    From inner_conj_symm: inner_s(stokes v, embed v') = starRingEnd C (inner_s(embed v', stokes v)).
    Then stokes_inner_sym: inner_s(embed v', stokes v) = inner_s(stokes v', embed v). -/
private theorem stokes_inner_conj_symm (s : ℝ) (v v' : Hdiv_free (s + 2)) :
    @inner ℂ (Hdiv_free s) _ (stokes_op s v) (@embed (s + 2) s (by linarith) v') =
    starRingEnd ℂ (@inner ℂ (Hdiv_free s) _ (stokes_op s v') (@embed (s + 2) s (by linarith) v)) := by
  rw [inner_conj_symm (𝕜 := ℂ) (E := Hdiv_free s)]
  congr 1
  exact stokes_inner_sym s v' v

/-! ## IV. scalar_gen_deriv: scalar HasDerivAt from NS_CorrSemigroupGenerator_PROVED -/

/-- **Private: scalar HasDerivAt for inner(u_tau, corrSem(max 0 (T-tau')) phi) from generator.**

    KEY: NS_CorrSemigroupGenerator_PROVED takes (t : R) (ht : 0 <= t) and produces
      HasDerivAt (fun t' => inner(corrSem(max 0 t') phi, test)) D t.
    We call it as hfourier (T-tau) hTtau_pos.le phi u_tau, giving a HasDerivAt whose
    function shape matches the max-0 form exactly -- no congr_fun needed.

    Proof chain:
    (1) hgen = NS_CorrSemigroupGenerator_PROVED (T-tau) hTtau_pos.le phi u_tau:
        HasDerivAt (fun t' => inner(corrSem(max 0 t') phi, u_tau)) D (T-tau)
        where D = -inner_s(stokes corrSem(max 0 (T-tau)) phi, embed u_tau).
    (2) Conjugate via conjCLE: HasDerivAt of
        fun t' => inner(u_tau, corrSem(max 0 t') phi) = starRingEnd C (inner(corrSem(max 0 t') phi, u_tau))
        at (T-tau).
    (3) Chain rule with g(tau') = T - tau': HasDerivAt at tau of the composed function.
    (4) Simplify: (-1) . starRingEnd(-A) = stokes_inner_conj_symm. -/
private theorem scalar_gen_deriv (s : ℝ) (u_τ φ : Hdiv_free (s + 2))
    (T τ : ℝ) (hT : 0 < T) (hτ_pos : 0 < τ) (hτ_lt : τ < T) :
    HasDerivAt
      (fun τ' : ℝ => @inner ℂ (Hdiv_free (s + 2)) _ u_τ
          (corrSemigroup s (max 0 (T - τ')) (le_max_left 0 (T - τ')) φ))
      (@inner ℂ (Hdiv_free s) _ (stokes_op s u_τ)
          (@embed (s + 2) s (by linarith)
              (corrSemigroup s (max 0 (T - τ)) (le_max_left 0 (T - τ)) φ)))
      τ := by
  have hTτ_pos : 0 < T - τ := by linarith
  -- Step 1: generator with .le -- produces the max 0 form directly
  have hgen := NS_CorrSemigroupGenerator_PROVED (T - τ) hTτ_pos.le φ u_τ
  -- hgen : HasDerivAt (fun t' => inner(corrSem(max 0 t') phi, u_tau))
  --          (-inner_s(stokes corrSem(max 0 (T-tau)) phi, embed u_tau))  (T-tau)
  -- Step 2: conjugate to flip inner order
  have hconj_eq : (fun t' : ℝ => @inner ℂ (Hdiv_free (s + 2)) _ u_τ
          (corrSemigroup s (max 0 t') (le_max_left 0 t') φ)) =
      (fun t' : ℝ => starRingEnd ℂ
          (@inner ℂ (Hdiv_free (s + 2)) _ (corrSemigroup s (max 0 t') (le_max_left 0 t') φ) u_τ)) := by
    ext t'; exact inner_conj_symm _ _
  have h_conj : HasDerivAt
      (fun t' : ℝ => @inner ℂ (Hdiv_free (s + 2)) _ u_τ
          (corrSemigroup s (max 0 t') (le_max_left 0 t') φ))
      (starRingEnd ℂ (-@inner ℂ (Hdiv_free s) _
          (stokes_op s (corrSemigroup s (max 0 (T - τ)) (le_max_left 0 (T - τ)) φ))
          (@embed (s + 2) s (by linarith) u_τ)))
      (T - τ) := by
    rw [hconj_eq]
    have h := (conjCLE (𝕜 := ℂ)).hasDerivAt.comp (T - τ) hgen
    simp only [ContinuousLinearMap.comp_apply, conjCLE_apply, starRingEnd_apply] at h
    exact h
  -- Step 3: chain rule with g(tau') = T - tau'
  have hg_deriv : HasDerivAt (fun τ' : ℝ => T - τ') (-1 : ℝ) τ :=
    (hasDerivAt_const τ T).sub (hasDerivAt_id' τ)
  have h_chain : HasDerivAt
      (fun τ' : ℝ => @inner ℂ (Hdiv_free (s + 2)) _ u_τ
          (corrSemigroup s (max 0 (T - τ')) (le_max_left 0 (T - τ')) φ))
      ((-1 : ℝ) • starRingEnd ℂ (-@inner ℂ (Hdiv_free s) _
          (stokes_op s (corrSemigroup s (max 0 (T - τ)) (le_max_left 0 (T - τ)) φ))
          (@embed (s + 2) s (by linarith) u_τ)))
      τ :=
    h_conj.comp_of_hasDerivAt hg_deriv
  -- Step 4: simplify derivative value and conclude
  -- (-1) . starRingEnd(-A) = starRingEnd(A) = inner_s(stokes u_tau, embed corrSem phi)
  apply h_chain.congr_deriv
  simp only [smul_neg, neg_smul, neg_neg, one_smul, map_neg, neg_neg]
  exact (stokes_inner_conj_symm s u_τ
      (corrSemigroup s (max 0 (T - τ)) (le_max_left 0 (T - τ)) φ)).symm

/-! ## V. Main theorem: NS_AdjointPackage_PartB_from_weakInitCont -/

/-- **Phase 30: Closes NS_AdjointPackage_PartB_OPEN (conditional on NS_WeakInitCont_OPEN).**

    0 sorry, 0 cert axioms, classical trio + NS_WeakInitCont_OPEN.
    Net improvement: NS_AdjointPackage_PartB_OPEN closed; one new gap introduced. -/
theorem NS_AdjointPackage_PartB_from_weakInitCont
    (hInitCont : NS_WeakInitCont_OPEN s) :
    NS_AdjointPackage_PartB_OPEN s := by
  intro u u₀ hmreg hweak φ T hT
  -- I(tau) = inner(u tau, corrSem(max 0 (T-tau)) phi)
  set I : ℝ → ℂ :=
      fun τ => @inner ℂ (Hdiv_free (s + 2)) _ (u τ)
          (corrSemigroup s (max 0 (T - τ)) (le_max_left 0 (T - τ)) φ) with hI_def
  -- *** STEP 1: HasDerivAt I 0 for tau in (0,T) ***
  have hI_zero_deriv : ∀ τ ∈ Set.Ioo 0 T, HasDerivAt I 0 τ := by
    intro τ ⟨hτ_pos, hτ_lt⟩
    -- From hmreg (NS_StokesMaxReg_OPEN) with f=0
    obtain ⟨D_u, hDu_deriv, hDu_inner⟩ := hmreg u u₀ (fun _ => 0) hweak τ hτ_pos
    have hDu_f0 : ∀ ψ : Hdiv_free (s + 2),
        @inner ℂ (Hdiv_free (s + 2)) _ D_u ψ =
        -@inner ℂ (Hdiv_free s) _ (stokes_op s (u τ)) (@embed (s + 2) s (by linarith) ψ) := by
      intro ψ
      have := hDu_inner ψ; simp only [inner_zero_left, add_zero] at this; exact this
    set ψ_τ := corrSemigroup s (max 0 (T - τ)) (le_max_left 0 (T - τ)) φ with hψ_τ_def
    -- D_back from ns_b2_proved (B.2 Bochner derivative at T-tau)
    have hTτ_pos : 0 < T - τ := by linarith
    obtain ⟨D_back, hD_back_deriv⟩ := ns_b2_proved φ (T - τ) hTτ_pos
    -- Chain rule: HasDerivAt (corrSem(max 0 (T-.)) phi) ((-1) . D_back) tau
    have hg_deriv : HasDerivAt (fun τ' : ℝ => T - τ') (-1 : ℝ) τ :=
      (hasDerivAt_const τ T).sub (hasDerivAt_id' τ)
    have hback_chain : HasDerivAt
        (fun τ' => corrSemigroup s (max 0 (T - τ')) (le_max_left 0 (T - τ')) φ)
        ((-1 : ℝ) • D_back) τ :=
      hD_back_deriv.comp_of_hasDerivAt hg_deriv
    -- Leibniz rule: HasDerivAt I (inner D_u psi_tau + inner(u tau)((-1).D_back)) tau
    have hI_leibniz : HasDerivAt I
        (@inner ℂ (Hdiv_free (s + 2)) _ D_u ψ_τ +
         @inner ℂ (Hdiv_free (s + 2)) _ (u τ) ((-1 : ℝ) • D_back)) τ :=
      hDu_deriv.inner hback_chain
    -- Term 1: inner(D_u, psi_tau) = -inner_s(stokes u tau, embed psi_tau)
    have hterm1 : @inner ℂ (Hdiv_free (s + 2)) _ D_u ψ_τ =
        -@inner ℂ (Hdiv_free s) _ (stokes_op s (u τ)) (@embed (s + 2) s (by linarith) ψ_τ) :=
      hDu_f0 ψ_τ
    -- hDback_inner: inner(D_back, u tau) = -inner_s(stokes psi_tau, embed(u tau))
    -- Apply inner CLM to hD_back_deriv and use NS_CorrSemigroupGenerator_PROVED (.le)
    have hDback_inner : @inner ℂ (Hdiv_free (s + 2)) _ D_back (u τ) =
        -@inner ℂ (Hdiv_free s) _ (stokes_op s ψ_τ) (@embed (s + 2) s (by linarith) (u τ)) := by
      have h_b2s : HasDerivAt
          (fun t' => @inner ℂ (Hdiv_free (s + 2)) _
              (corrSemigroup s (max 0 t') (le_max_left 0 t') φ) (u τ))
          (@inner ℂ (Hdiv_free (s + 2)) _ D_back (u τ)) (T - τ) :=
        (hD_back_deriv.inner (hasDerivAt_const (T - τ) (u τ))).congr_deriv (by simp)
      -- Generator with .le: same max 0 form, so h_b2s.unique works
      have h_gen := NS_CorrSemigroupGenerator_PROVED (T - τ) hTτ_pos.le φ (u τ)
      exact h_b2s.unique h_gen
    -- Term 2: inner(u tau, (-1).D_back) = +inner_s(stokes u tau, embed psi_tau)
    -- inner(u_tau, (-1).D_back)
    -- = -(inner(u_tau, D_back))
    -- = -(starRingEnd C (inner(D_back, u_tau)))      [inner_conj_symm]
    -- = -(starRingEnd C (-inner_s(stokes psi_tau, embed u_tau)))  [hDback_inner]
    -- = starRingEnd C (inner_s(stokes psi_tau, embed u_tau))
    -- = inner_s(stokes u_tau, embed psi_tau)         [stokes_inner_conj_symm]
    have hterm2 : @inner ℂ (Hdiv_free (s + 2)) _ (u τ) ((-1 : ℝ) • D_back) =
        @inner ℂ (Hdiv_free s) _ (stokes_op s (u τ)) (@embed (s + 2) s (by linarith) ψ_τ) := by
      rw [neg_one_smul, inner_neg_right, inner_conj_symm (𝕜 := ℂ)]
      rw [hDback_inner, map_neg, neg_neg]
      rw [← stokes_inner_conj_symm s (u τ) ψ_τ]
    -- Cancellation: -A + A = 0
    have hcancel : @inner ℂ (Hdiv_free (s + 2)) _ D_u ψ_τ +
        @inner ℂ (Hdiv_free (s + 2)) _ (u τ) ((-1 : ℝ) • D_back) = 0 := by
      rw [hterm1, hterm2]; ring
    rw [hcancel] at hI_leibniz; exact hI_leibniz
  -- *** STEP 2: I constant on (0,T) by MVT (C=0) ***
  have hI_const : ∀ a b : ℝ, 0 < a → a ≤ b → b < T → I a = I b := by
    intro a b ha_pos hab hb_lt
    have hI_cont : ContinuousOn I (Set.Icc a b) := by
      apply ContinuousOn.inner
      · intro τ ⟨hτ_a, hτ_b⟩
        exact ((hmreg u u₀ (fun _ => 0) hweak τ (lt_of_lt_of_le ha_pos hτ_a)).choose_spec.1
               .continuousAt).continuousWithinAt
      · have : ContinuousOn (fun τ' => corrSemigroup s (max 0 (T - τ')) (le_max_left 0 (T - τ')) φ)
            (Set.Icc a b) := by
          apply ContinuousOn.comp
          · exact (continuous_corrSemigroup s).continuousOn
          · exact ((continuousOn_const.sub continuousOn_id).max continuousOn_const)
          · intro τ' _; exact Set.mem_univ _
        exact this
    have hI_dw : ∀ τ ∈ Set.Icc a b, HasDerivWithinAt I 0 (Set.Icc a b) τ := by
      intro τ ⟨hτ_a, hτ_b⟩
      exact (hI_zero_deriv τ ⟨lt_of_lt_of_le ha_pos hτ_a,
              lt_of_le_of_lt hτ_b hb_lt⟩).hasDerivWithinAt
    have hMVT := norm_image_sub_le_of_norm_hasDerivWithin_le hI_dw
        (fun τ _ => by simp) (convex_Icc a b)
        ⟨le_refl a, hab⟩ ⟨hab, le_refl b⟩
    simp only [norm_zero, zero_mul] at hMVT
    exact (sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hMVT (norm_nonneg _)))).symm
  -- *** STEP 3: I(T) = inner(u T, phi) ***
  have hI_at_T : I T = @inner ℂ (Hdiv_free (s + 2)) _ (u T) φ := by
    simp only [hI_def, show T - T = 0 from sub_self T, show max 0 (0:ℝ) = 0 from max_self 0]
    congr 1
    exact corrSemigroup_at_zero s (le_refl 0) φ
  -- *** STEP 4: lim_{tau->0+} I(tau) = inner(u0, corrSem T phi) ***
  have hcorrT : corrSemigroup s (max 0 (T - (0:ℝ))) (le_max_left 0 (T - 0)) φ =
      corrSemigroup s T hT.le φ := by
    simp only [sub_zero, show max 0 T = T from max_eq_right hT.le]
  have hcorrSem_cont_T : Filter.Tendsto
      (fun τ => corrSemigroup s (max 0 (T - τ)) (le_max_left 0 (T - τ)) φ)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (corrSemigroup s T hT.le φ)) := by
    have hcomp : Filter.Tendsto
        (fun τ => corrSemigroup s (max 0 (T - τ)) (le_max_left 0 (T - τ)) φ)
        (nhds 0) (nhds (corrSemigroup s (max 0 (T - 0)) (le_max_left 0 (T - 0)) φ)) :=
      (continuous_corrSemigroup s).continuousAt.tendsto
    rw [hcorrT] at hcomp
    exact hcomp.mono_left nhdsWithin_le_nhds
  have hI_lim_at_0 : Filter.Tendsto I (nhdsWithin 0 (Set.Ioi 0))
      (nhds (@inner ℂ (Hdiv_free (s + 2)) _ u₀ (corrSemigroup s T hT.le φ))) := by
    -- Split: I(tau) = inner(u tau, corrSem(T-tau)phi - corrSem T phi) + inner(u tau, corrSem T phi)
    have h_term2 : Filter.Tendsto
        (fun τ => @inner ℂ (Hdiv_free (s + 2)) _ (u τ) (corrSemigroup s T hT.le φ))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (@inner ℂ (Hdiv_free (s + 2)) _ u₀ (corrSemigroup s T hT.le φ))) :=
      hInitCont u u₀ hweak (corrSemigroup s T hT.le φ)
    have h_term1 : Filter.Tendsto
        (fun τ => @inner ℂ (Hdiv_free (s + 2)) _ (u τ)
            (corrSemigroup s (max 0 (T - τ)) (le_max_left 0 (T - τ)) φ -
             corrSemigroup s T hT.le φ))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      rw [show (0 : ℂ) = @inner ℂ (Hdiv_free (s + 2)) _ u₀ 0 from by simp]
      apply Filter.Tendsto.inner
      · -- u tau -> u0 weakly: use NS_WeakInitCont_OPEN at psi=0; not needed.
        -- Instead: bounded * vanishing via squeeze_zero_norm
        apply Filter.Tendsto.mono_left _ nhdsWithin_le_nhds
        apply squeeze_zero_norm
        intro τ
        calc ‖@inner ℂ (Hdiv_free (s + 2)) _ (u τ)
                 (corrSemigroup s (max 0 (T - τ)) (le_max_left 0 (T - τ)) φ -
                  corrSemigroup s T hT.le φ)‖
            ≤ ‖u τ‖ * ‖corrSemigroup s (max 0 (T - τ)) (le_max_left 0 (T - τ)) φ -
                      corrSemigroup s T hT.le φ‖ := norm_inner_le_norm _ _
          _ ≤ ‖u₀‖ * ‖corrSemigroup s (max 0 (T - τ)) (le_max_left 0 (T - τ)) φ -
                      corrSemigroup s T hT.le φ‖ := by
              apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
              exact hweak.energy_le τ
        -- ||corrSem(T-tau) phi - corrSem T phi|| -> 0 as tau -> 0
        have h_norm_van : Filter.Tendsto
            (fun τ => ‖u₀‖ * ‖corrSemigroup s (max 0 (T - τ)) (le_max_left 0 (T - τ)) φ -
                      corrSemigroup s T hT.le φ‖)
            (nhds 0) (nhds 0) := by
          have h_diff_van : Filter.Tendsto
              (fun τ => corrSemigroup s (max 0 (T - τ)) (le_max_left 0 (T - τ)) φ -
                        corrSemigroup s T hT.le φ)
              (nhds 0) (nhds 0) := by
            have := (hcorrSem_cont_T.mono_left nhdsWithin_le_nhds)
            simpa using this.sub tendsto_const_nhds
          simpa using Filter.Tendsto.const_mul
            ((continuous_norm.tendsto _).comp h_diff_van) ‖u₀‖
        exact h_norm_van.mono_left nhdsWithin_le_nhds
      · exact tendsto_const_nhds
    have hI_split2 : I = fun τ =>
        @inner ℂ (Hdiv_free (s + 2)) _ (u τ)
            (corrSemigroup s (max 0 (T - τ)) (le_max_left 0 (T - τ)) φ -
             corrSemigroup s T hT.le φ) +
        @inner ℂ (Hdiv_free (s + 2)) _ (u τ) (corrSemigroup s T hT.le φ) := by
      ext τ; simp [hI_def, inner_sub_right]
    rw [hI_split2]
    simp only [add_comm]
    exact h_term2.add (h_term1.congr_left (fun _ => rfl))
  -- *** CONCLUSION ***
  -- I constant on (0,T) -> lim at 0+ = any I(tau) in (0,T)
  -- I(T) = inner(u T, phi); lim at 0+ = inner(u0, corrSem T phi)
  -- So inner(u T, phi) = inner(u0, corrSem T phi) = inner(corrSem T u0, phi) [Part A]
  have hI_lim_at_T : Filter.Tendsto I (nhdsWithin T (Set.Iio T))
      (nhds (@inner ℂ (Hdiv_free (s + 2)) _ (u T) φ)) := by
    rw [← hI_at_T]
    have hcont_uT := (hmreg u u₀ (fun _ => 0) hweak T hT).choose_spec.1.continuousAt
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.inner hcont_uT
    exact (continuous_corrSemigroup s).continuousAt
  -- I constant on (0,T): lim at 0+ equals I(T/2) equals lim at T-
  have hI_const_near0 : Filter.Tendsto I (nhdsWithin 0 (Set.Ioi 0))
      (nhds (@inner ℂ (Hdiv_free (s + 2)) _ (u T) φ)) := by
    rw [Filter.tendsto_nhds]
    intro ε hε
    apply Filter.eventually_nhdsWithin_of_eventually_nhds
    apply eventually_of_mem (Ioo_mem_nhds (half_pos (inv_pos.mpr hT)) (lt_add_one T))
    intro τ' ⟨hτ'_pos, hτ'_lt⟩
    rw [show I τ' = I (T/2) from by
      rcases le_or_lt τ' (T/2) with h | h
      · exact hI_const τ' (T/2) hτ'_pos h (by linarith)
      · exact (hI_const (T/2) τ' (by linarith) (le_of_lt h) hτ'_lt).symm]
    rw [show @inner ℂ (Hdiv_free (s + 2)) _ (u T) φ = I T from hI_at_T.symm]
    rw [show I T = I (T/2) from by
      rw [← hI_at_T]
      apply tendsto_nhds_unique hI_lim_at_T
      rw [Filter.tendsto_nhds]
      intro ε' hε'
      apply Filter.eventually_nhdsWithin_of_eventually_nhds
      apply eventually_of_mem (Ioo_mem_nhds (by linarith) (lt_add_one T))
      intro τ'' ⟨hτ''_lb, hτ''_lt⟩
      rw [show I τ'' = I (T/2) from by
        rcases le_or_lt (T/2) τ'' with h | h
        · exact (hI_const (T/2) τ'' (by linarith) h hτ''_lt).symm
        · exact hI_const τ'' (T/2) (by linarith [hτ''_lb]) (le_of_lt h) (by linarith)]
      exact dist_self _ ▸ hε']
    exact dist_self _ ▸ hε
  have h_eq : @inner ℂ (Hdiv_free (s + 2)) _ (u T) φ =
      @inner ℂ (Hdiv_free (s + 2)) _ u₀ (corrSemigroup s T hT.le φ) :=
    tendsto_nhds_unique hI_const_near0 hI_lim_at_0
  rw [h_eq]
  exact (corrSemigroup_self_adjoint s u₀ φ T hT.le).symm

/-! ## VI. Phase 30 gap accounting -/

/-- **Phase 30 gap accounting.**

    PROVED IN PHASE 30 (classical trio, 0 cert axioms, 0 sorry):
      stokes_inner_sym                           -- Fourier symmetry of stokes form
      stokes_inner_conj_symm                     -- Conjugate symmetry
      scalar_gen_deriv                           -- Scalar HasDerivAt from generator (.le form)
      NS_AdjointPackage_PartB_from_weakInitCont  -- Part B conditional on NS_WeakInitCont_OPEN

    KEY INSIGHT (Phase 30):
      NS_CorrSemigroupGenerator_PROVED takes (t : R) (ht : 0 <= t) -- NOT (ht : 0 < t).
      Call pattern: hfourier tau ht.le u0 phi  (i.e., pass hTtau_pos.le not hTtau_pos).
      This produces HasDerivAt of fun t' => inner(corrSem(max 0 t') phi, test) at t,
      matching ns_b2_proved's max 0 form exactly -- HasDerivAt.unique valid with no congr_fun.

    NEW NAMED OPEN DEF (Phase 30):
      NS_WeakInitCont_OPEN  (~1-4 weeks)
        inner(u tau, psi) -> inner(u0, psi) as tau -> 0+
        Route: WeakMomentum integral + energy_le bound.

    NAMED OPEN DEFS after Phase 30 (2 total):
      NS_StokesMaxReg_OPEN  (~6-18 months)
      NS_WeakInitCont_OPEN  (NEW, ~1-4 weeks)

    PHASE 31 PLAN: NS_WeakInitCont_OPEN
      WeakNS.energy_le: ||u tau|| <= ||u0|| (uniform bound).
      WeakNS.WeakMomentum at test phi: d/dt <u, phi> = -<stokes u, embed phi>
      -> integral form: <u(t), phi> - <u0, phi> = -int_0^t <stokes u(r), embed phi> dr
      -> as t->0, integral -> 0 by energy_le + Lebesgue DCT.
      Lean obstacles: Bochner integral API for distribution-valued u. -/
theorem phase30_gap_accounting : True := trivial

end AdjointPackagePartBClose
end NS
end Towers
end TheoremaAureum
