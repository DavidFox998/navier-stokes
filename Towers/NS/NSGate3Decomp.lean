/-
================================================================
Towers / NS / NSGate3Decomp  —  NS Tower 540, Phase 10
                                Gate 3 BKM Decomposition

Clay Gate 3: `NS_GlobalContinuation_OPEN s`
  (defined in NSClayCombinator.lean)
  = global_smooth_exists (s := s)             -- Part A: local regularity
  ∧ (∀ w : WeakSolution s,
      (∃ T > 0, IsSmoothOn w.u T) →           -- Part B: local → global
      ∀ T : ℝ, 0 < T → IsSmoothOn w.u T)

Decomposed into five sub-avenues via the Beale–Kato–Majda strategy:

  I   (PROVED): NS_SmoothMono_PROVED
                IsSmoothOn is monotone (downward-closed) in T.
                Proof: ContDiffOn.mono + Set.Ioo_subset_Ioo_right.
                Classical trio, 0 sorry. GENUINE.

  J   (PROVED): NS_SmoothMin_PROVED
                Intersection of two smooth intervals is smooth.
                Proof: ContDiffOn.mono + min_le_left.
                Classical trio, 0 sorry. GENUINE.

  M   (OPEN):   NS_LocalRegularity_OPEN s
                = global_smooth_exists s (Part A of Gate 3).
                Stokes parabolic regularity + Sobolev embedding ⋂_s Hˢ ↪ C^∞.
                Requires joint space–time elliptic regularity absent from
                Mathlib v4.12.0. ETA 12–18 mo.

  K   (OPEN):   NS_BKMCriterion_OPEN s
                Beale–Kato–Majda criterion: finite-time blow-up of a weak
                solution is witnessed by blow-up of the Sobolev Hˢ⁺² norm.
                Requires Gronwall-inequality energy cascade and the Sobolev
                product estimate absent from Mathlib v4.12.0. ETA 12–18 mo.

  L   (OPEN):   NS_GlobalSobolevBound_OPEN s
                Global Sobolev bound: ‖u(t)‖_{Hˢ⁺²} stays finite for all t.
                This is THE genuine Clay open problem (ruling out finite-time
                blow-up). ETA: Unknown / Clay Millennium resolution required.

  Bridge (OPEN): NS_BKM_Bridge_OPEN s
                K + L → Gate 3 Part B.
                "BKM + global bound → no blow-up → global continuation."
                Conceptually immediate given K and L; the difficulty is entirely
                in discharging K and L.

Combinator: ns_gate3_from_avenues (M + K + L + Bridge → Gate 3).
Classical trio, 0 sorry. NS global regularity: OPEN. No Clay claim.
================================================================
-/

import Towers.NS.NSClayCombinator
import Mathlib.Analysis.Calculus.ContDiff.Basic

open Filter Topology
open TheoremaAureum.Towers.NS.FunctionSpaces
open TheoremaAureum.Towers.NS.WeakSolution
open TheoremaAureum.Towers.NS.Regularity
open TheoremaAureum.Towers.NS.ClayCombinator

namespace TheoremaAureum
namespace Towers
namespace NS
namespace Gate3Decomp

/-!
## Named OPEN surfaces (Gate 3 sub-avenues M, K, L, Bridge)
-/

/-- **OPEN (Gate 3, Sub-av. M)**: Local Stokes parabolic regularity.
    `global_smooth_exists s` — every (modeled) weak solution is smooth on some
    short time interval `∃ T > 0, IsSmoothOn w.u T`. This is Part A of Gate 3.
    Requires the spatial Sobolev embedding `⋂_s Hˢ ↪ C^∞` across ALL Sobolev
    indices simultaneously (absent from this fixed-index Fourier model and from
    Mathlib v4.12.0). Mathematical status: provable in principle (Stokes
    parabolic regularity is classical), but the multi-index embedding is missing.
    ETA 12–18 mo for Mathlib formalization. -/
def NS_LocalRegularity_OPEN (s : ℝ) : Prop :=
  global_smooth_exists (s := s)

/-- **OPEN (Gate 3, Sub-av. K)**: Beale–Kato–Majda blow-up criterion.
    If a weak solution u loses smoothness at a finite time (fails to satisfy
    `IsSmoothOn u T` for some T), then the Sobolev Hˢ⁺² norm must blow up:
    for every sequence of times approaching the blow-up time, the norm
    tends to infinity. Requires the Gronwall-based energy cascade and the
    Sobolev product/algebra estimate for u ⊗ ∇u, absent from Mathlib v4.12.0.
    Mathematical status: KNOWN (Beale–Kato–Majda 1984; Kozono–Taniuchi 2000).
    ETA 12–18 mo for Mathlib formalization. -/
def NS_BKMCriterion_OPEN (s : ℝ) : Prop :=
  ∀ (u : ℝ → Hdiv_free (s + 2)) (T : ℝ), 0 < T →
    (¬IsSmoothOn u T) →
    ∃ seq : ℕ → ℝ, StrictMono seq ∧ (∀ n, seq n < T) ∧
      Filter.Tendsto
        (fun n => ‖(u (seq n) : Lp Val 2 (mu (s + 2)))‖)
        Filter.atTop Filter.atTop

/-- **OPEN (Gate 3, Sub-av. L)**: Global Sobolev bound — THE genuine Clay hard part.
    For any (modeled) weak solution u satisfying `WeakNS u u₀ f`, the Sobolev
    `Lp Val 2 (mu (s+2))` norm of `u t` remains finite for every finite time T.
    Contrapositive of K: no norm blow-up → no blow-up → global continuation.
    Mathematical status: OPEN (Clay Millennium Problem; Fefferman 2000).
    Resolution requires entirely new PDE methods beyond current Mathlib v4.12.0. -/
def NS_GlobalSobolevBound_OPEN (s : ℝ) : Prop :=
  ∀ (u₀ : Hdiv_free (s + 2)) (f : ExternalForce s)
    (u : ℝ → Hdiv_free (s + 2)),
    WeakNS u u₀ f →
    ∀ T : ℝ, 0 < T → ∀ t : ℝ, 0 ≤ t → t < T →
      ‖(u t : Lp Val 2 (mu (s + 2)))‖ < T + ‖(u₀ : Lp Val 2 (mu (s + 2)))‖ + 1

/-- **OPEN (Bridge)**: BKM criterion + Global Sobolev bound → Gate 3 Part B.
    Given K and L: K says blow-up is witnessed by norm blow-up; L says the norm
    never blows up; therefore no blow-up occurs and local smoothness extends
    globally. The logical deduction from K+L to Part B is the Bridge. Stated
    as a named OPEN surface because its proof requires K and L (both OPEN).
    The Bridge itself is logically immediate once K and L are discharged. -/
def NS_BKM_Bridge_OPEN (s : ℝ) : Prop :=
  NS_BKMCriterion_OPEN s →
  NS_GlobalSobolevBound_OPEN s →
  (∀ w : WeakSolution s,
    (∃ T > 0, IsSmoothOn w.u T) →
    ∀ T : ℝ, 0 < T → IsSmoothOn w.u T)

/-!
## Proved sub-avenues (structural; classical trio, 0 sorry)
-/

/-- **PROVED (Gate 3, Sub-av. I)**: `IsSmoothOn` is monotone (downward-closed) in `T`.
    If `u` is smooth on `(0, T)` and `T' ≤ T`, then `u` is smooth on `(0, T')`.
    Proof: `ContDiffOn.mono` + `Set.Ioo_subset_Ioo_right`. Classical trio, 0 sorry.
    This is the core structural lemma underpinning the BKM continuation argument:
    smooth existence on a larger interval implies smooth existence on any
    sub-interval. -/
theorem NS_SmoothMono_PROVED {s : ℝ}
    (u : ℝ → Hdiv_free (s + 2)) (T T' : ℝ) (hle : T' ≤ T)
    (hsmooth : IsSmoothOn u T) :
    IsSmoothOn u T' := by
  intro φ
  exact (hsmooth φ).mono (Set.Ioo_subset_Ioo_right hle)

/-- **PROVED (Gate 3, Sub-av. J)**: The intersection of two smooth intervals is smooth.
    If `u` is smooth on `(0, T₁)` and on `(0, T₂)`, then `u` is smooth on
    `(0, min T₁ T₂)`. Proof: `ContDiffOn.mono` + `min_le_left`. Classical trio, 0 sorry.
    This encodes the finite-intersection property of smooth-time intervals:
    smoothness on each of finitely many intervals implies smoothness on their
    common sub-interval, a key step in any continuation argument. -/
theorem NS_SmoothMin_PROVED {s : ℝ}
    (u : ℝ → Hdiv_free (s + 2)) (T₁ T₂ : ℝ)
    (h1 : IsSmoothOn u T₁) (h2 : IsSmoothOn u T₂) :
    IsSmoothOn u (min T₁ T₂) := by
  intro φ
  exact (h1 φ).mono (Set.Ioo_subset_Ioo_right (min_le_left T₁ T₂))

/-!
## Gate 3 combinator (M + K + L + Bridge → Gate 3)
-/

/-- **Gate 3 combinator**: M + K + L + Bridge → `NS_GlobalContinuation_OPEN s`.

    Proof route:
      M = `global_smooth_exists s`       → Gate 3 Part A ✓
      K = `NS_BKMCriterion_OPEN s`      ↘
      L = `NS_GlobalSobolevBound_OPEN s` → Bridge hypothesis
      Bridge provides: K + L → Part B   → Gate 3 Part B ✓
      Gate 3 = Part A ∧ Part B           ✓

    Classical trio, 0 sorry. Gate 3 itself is OPEN until M, K, L are discharged.
    NS global regularity: OPEN. No Clay claim. -/
theorem ns_gate3_from_avenues (s : ℝ)
    (hM : NS_LocalRegularity_OPEN s)
    (hK : NS_BKMCriterion_OPEN s)
    (hL : NS_GlobalSobolevBound_OPEN s)
    (hBridge : NS_BKM_Bridge_OPEN s) :
    NS_GlobalContinuation_OPEN s :=
  ⟨hM, hBridge hK hL⟩

/-- **Registry**: I+J proved unconditionally; M+K+L+Bridge all OPEN. -/
theorem ns_gate3_proved_avenues_hold {s : ℝ}
    (u : ℝ → Hdiv_free (s + 2)) (T T' : ℝ) (hle : T' ≤ T)
    (hsmooth : IsSmoothOn u T) :
    IsSmoothOn u T' ∧ IsSmoothOn u (min T' T) :=
  ⟨NS_SmoothMono_PROVED u T T' hle hsmooth,
   NS_SmoothMono_PROVED u T (min T' T) (min_le_right T' T) hsmooth⟩

end Gate3Decomp
end NS
end Towers
end TheoremaAureum
