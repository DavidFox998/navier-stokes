/-
================================================================
Towers / NS / NSCollection  —  NS Tower 540, Collection / Index

**Central export file for NS Tower 540.** Analogous to `YMCollection`
for the YM tower and `BSD_MasterCertification` for the BSD tower.

### Proved theorems (all classical trio, 0 sorry)

  Phase 7A (NSStokesAdjoint):
    `stokes_op_adjoint` — self-adjointness in the Fourier model   ✓ NEW
    `integration_by_parts_proved` — closes Energy.lean surface    ✓ NEW
  Phase 7B (NSNonlinearTerm):
    `trilinear_zero_energy` — B(u,u,u)=0 for div-free u          ✓ NEW
  Phase 7C (NSClayCombinator):
    `ns_clay_combinator` — 3 atomic gates → NS_ClayStatement       ✓ NEW
  Phases 1–6 (FunctionSpaces through Wall300):
    All phase combinators re-exported.

### Named OPEN surfaces (Clay gates, all classical trio, 0 sorryAx)

  Gate 1: `NS_AubinLions_OPEN K`       — Rellich–Kondrachov (Mathlib gap)
  Gate 2: `NS_NonlinearWeakForm_OPEN K` — nonlinear trilinear form (Mathlib gap)
  Gate 3: `NS_GlobalContinuation_OPEN s` — no finite-time blow-up (Clay open)

### Newly closed surfaces

  `integration_by_parts` (Phase 3 Energy) — CLOSED by Phase 7A.

### Honest scope

  NS global regularity is OPEN. `ns_clay_combinator` proves NOTHING
  without all 3 gates being established. NS tower stays `Status: Open`.
================================================================
-/

import Towers.NS.FunctionSpaces
import Towers.NS.Leray
import Towers.NS.Stokes
import Towers.NS.Energy
import Towers.NS.GalerkinApprox
import Towers.NS.Compactness
import Towers.NS.WeakSolution
import Towers.NS.Regularity
import Towers.NS.Wall300_Scaffold
import Towers.NS.NSStokesAdjoint
import Towers.NS.NSNonlinearTerm
import Towers.NS.NSClayCombinator
import Towers.NS.NSAubinLionsDecomp
import Towers.NS.NSCanonicalSurfaces

open TheoremaAureum.Towers.NS.FunctionSpaces
open TheoremaAureum.Towers.NS.Stokes
open TheoremaAureum.Towers.NS.Energy
open TheoremaAureum.Towers.NS.WeakSolution
open TheoremaAureum.Towers.NS.Regularity
open TheoremaAureum.Towers.NS.StokesAdjoint
open TheoremaAureum.Towers.NS.NonlinearTerm
open TheoremaAureum.Towers.NS.ClayCombinator
open TheoremaAureum.Towers.NS.Wall300Scaffold

namespace TheoremaAureum
namespace Towers
namespace NS
namespace Collection

/-!
## Phase 7A: Stokes self-adjointness (newly proved)
-/

/-- **PROVED (Phase 7A)**: Stokes operator self-adjointness in the Fourier model.
    Closes `integration_by_parts`. Classical trio, 0 sorry. -/
theorem col_stokes_op_adjoint {s : ℝ} (u v : Hdiv_free (s + 2)) :
    @inner ℂ (Hdiv_free s) _ (stokes_op s u) (@embed _ _ (by linarith) v) =
    @inner ℂ (Hdiv_free s) _ (@embed _ _ (by linarith) u) (stokes_op s v) :=
  StokesAdjoint.stokes_op_adjoint u v

/-- **PROVED (Phase 7A)**: Closes the `Energy.integration_by_parts` surface. -/
theorem col_integration_by_parts_closed {s : ℝ} :
    @Energy.integration_by_parts s :=
  StokesAdjoint.integration_by_parts_proved

/-!
## Phase 7B: Energy cancellation (newly proved)
-/

/-- **PROVED (Phase 7B)**: `B(u,u,u) = 0` for div-free u. -/
theorem col_trilinear_zero_energy {s : ℝ}
    (B : Hdiv_free (s + 2) → Hdiv_free (s + 2) → Hdiv_free (s + 2) → ℂ)
    (hans : ∀ (u v w : Hdiv_free (s + 2)),
        IsDivFree (u : Lp Val 2 (mu (s + 2))) → B u v w = -(B u w v))
    (u : Hdiv_free (s + 2))
    (hdiv : IsDivFree (u : Lp Val 2 (mu (s + 2)))) :
    B u u u = 0 :=
  NonlinearTerm.trilinear_zero_energy B hans u hdiv

/-!
## Phase 7C: Clay master combinator (newly proved)
-/

/-- **MASTER COMBINATOR (Phase 7C)**: 3 atomic Clay gates → NS_ClayStatement.
    `#print axioms col_ns_clay_master` = classical trio. NS stays OPEN. -/
theorem col_ns_clay_master {s : ℝ}
    (K : ℕ → Submodule ℂ (Hdiv_free (s + 2))) [∀ n, FiniteDimensional ℂ (K n)]
    (h1 : NS_AubinLions_OPEN K)
    (h2 : NS_NonlinearWeakForm_OPEN K)
    (h3 : NS_GlobalContinuation_OPEN s) :
    NS_ClayStatement s :=
  ClayCombinator.ns_clay_combinator K h1 h2 h3

/-!
## Open gate registry
-/

/-- **NS Tower open surface count**: 3 atomic Clay gates. -/
def ns_open_surface_count : ℕ := 3

/-- The 3 Clay gates as strings (for documentation). -/
def ns_clay_gates : List String := [
  "NS_AubinLions_OPEN",
  "NS_NonlinearWeakForm_OPEN",
  "NS_GlobalContinuation_OPEN",
  -- Phase 8A sub-avenues (Gate 1 decomposition):
  "NS_RellichKondrachov_OPEN",
  "NS_WeakCompactness_OPEN",
  "NS_AubinLions_Bridge_OPEN"
]

/-- Previously OPEN, now CLOSED by Phase 7A. -/
def ns_newly_closed : List String := ["integration_by_parts"]

/-!
## Phase 8A: Aubin–Lions decomposition re-exports
-/

/-- **Re-export (Phase 8A, Sub-av. A) PROVED**: compact ball in K(n). -/
theorem col_finDimCompact_proved {s : ℝ}
    (K : ℕ → Submodule ℂ (Hdiv_free (s + 2))) [∀ n, FiniteDimensional ℂ (K n)]
    (n : ℕ) (r : ℝ) :
    IsCompact (Metric.closedBall (0 : K n) r) :=
  AubinLionsDecomp.NS_FinDimCompact_PROVED K n r

/-- **Re-export (Phase 8A, Sub-av. B) PROVED**: Galerkin sequence is bounded. -/
theorem col_galerkin_bounded_proved {s : ℝ}
    (K : ℕ → Submodule ℂ (Hdiv_free (s + 2))) [∀ n, FiniteDimensional ℂ (K n)]
    (u : ℝ → Hdiv_free (s + 2)) (n : ℕ) (t : ℝ) :
    ‖galerkin_seq K u n t‖ ≤ ‖u t‖ :=
  AubinLionsDecomp.NS_GalerkinBounded_PROVED K u n t

/-- **Registry (Phase 8A)**: 3 proved sub-avenues, 3 open sub-avenues. -/
def ns_gate1_sub_avenues : List String := [
  "A: NS_FinDimCompact_PROVED (PROVED)",
  "B: NS_GalerkinBounded_PROVED (PROVED)",
  "B': NS_GalerkinInCompact_PROVED (PROVED)",
  "C: NS_RellichKondrachov_OPEN (OPEN)",
  "D: NS_WeakCompactness_OPEN (OPEN)",
  "Bridge: NS_AubinLions_Bridge_OPEN (OPEN)"
]

/-!
## Wall300 combinator re-export
-/

/-- **Re-export: conditional global regularity** from Wall300_Scaffold. -/
theorem col_navier_stokes_global_regularity {s : ℝ}
    (u₀ : Hdiv_free (s + 2)) (f : ExternalForce s)
    (h_weak_exists : ∃ u : ℝ → Hdiv_free (s + 2), WeakNS u u₀ f)
    (h_local : global_smooth_exists (s := s))
    (h_global : ∀ w : WeakSolution s, (∃ T > 0, IsSmoothOn w.u T) →
        ∀ T : ℝ, 0 < T → IsSmoothOn w.u T) :
    ∃ w : WeakSolution s, ∀ T : ℝ, 0 < T → IsSmoothOn w.u T :=
  navier_stokes_global_regularity u₀ f h_weak_exists h_local h_global

end Collection
end NS
end Towers
end TheoremaAureum
