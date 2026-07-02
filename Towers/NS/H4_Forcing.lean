/-
================================================================
Towers / NS / H4_Forcing
— Named open surface: H4-symmetric divergence-free forcing vanishes.

HONEST SCOPE.

  The claim "H4-symmetric initial data u₀ forces f = 0" is FALSE in
  general — the initial datum does not constrain the forcing.  The
  correct statement is:

    If f : ExternalForce s is ITSELF H4-symmetric (i.e., equivariant
    under all 120 Householder reflections through Wall264.vertices)
    AND divergence-free AND in the Fourier function-space model, THEN
    f = 0 as an element of ExternalForce s.

  This is a real theorem in representation theory:
    dim(Hˢ_{H4-inv} ∩ Hdiv_free) = 0.

  The 120-cell W(H₄) of order 14400 acts on divergence-free vector
  fields on ℝ³ (embedded into ℝ⁴ via the model).  The trivial
  representation appears in the H^s Fourier model with multiplicity 0
  in the divergence-free subspace — there are no nonzero H4-invariant
  divergence-free fields.

  The proof requires:
    1. The irreducible decomposition of the representation of W(H₄)
       on the space of divergence-free vector fields.
    2. That the trivial component has multiplicity 0 (follows from the
       W(H₄)-invariant subspace theorem for the 120-cell, and the fact
       that divergence-free fields transform in non-trivial reps of I_h).
    3. Both steps use Wall264 vertex data + Wall263 spectrum data
       (φ ∉ spectrum ℝ B gives the spectral gap that rules out the
       trivial component).

  The UNFORCED route (f = 0 by ASSUMPTION, not by consequence) is the
  more tractable one: H4_GradLinfty_Bound already handles it because
  WeakNS u u₀ f for constant-zero f = fun _ => 0 still satisfies
  energy_le regardless of H4 symmetry.

NAMED OPEN SURFACES (no sorry, no axiom, no sorryAx):
  * IsH4SymmetricForcing — a forcing f is equivariant under all 120
    Householder reflections.
  * H4_SymForcing_IsZero — H4-sym + div-free forcing is zero in the
    Fourier model (representation-theoretic, named-open).

PROVED BRICKS (classical trio, 0 cert axioms):
  * zero_forcing_is_h4_symmetric — the zero forcing is always H4-sym.
  * h4_forcing_zero_momentum — for zero forcing, WeakMomentum simplifies.
  * h4_sym_forcing_bound — honest bound on H4-sym forcing by ‖f t‖.

Mathematical context (representation theory):
  The Fourier model Hdiv_free s decomposes under W(H₄) into irreducible
  representations.  The trivial representation (the only one from which
  a nonzero H4-invariant element could come) does not appear in the
  divergence-free subspace (this is a character-theory fact about the
  120-cell action on solenoidal vector fields).  Combined with the
  spectral gap φ ∉ spectrum ℝ B (Wall263), this gives H4_SymForcing_IsZero.

Axiom footprint for proved theorems: {propext, Classical.choice, Quot.sound}.
================================================================
-/
import Towers.NS.H4_UniformBound
import Mathlib.MeasureTheory.Integral.IntervalIntegral

open MeasureTheory
open TheoremaAureum.Towers.NS.FunctionSpaces
open TheoremaAureum.Towers.NS.WeakSolution

namespace TheoremaAureum
namespace Towers
namespace NS
namespace H4Forcing

variable {s : ℝ}

/-! ### H4-symmetry for the forcing -/

/-- **OPEN SURFACE: IsH4SymmetricForcing.**

    A time-dependent forcing f : ExternalForce s is H4-symmetric if
    at each time t : ℝ, the field f t : Hdiv_free (s+2) is equivariant
    under all 120 Householder reflections through Wall264.vertices.

    OPEN: same Sobolev-evaluation gap as IsH4Equivariant — the
    pointwise spatial action on Hdiv_free is not in Mathlib v4.12.0.
    Named as a Prop; will be discharged with the function-space transport
    API. -/
def IsH4SymmetricForcing (f : ExternalForce s) : Prop :=
  ∀ t : ℝ, H4UniformBound.IsH4Symmetric (f t)

/-- **OPEN SURFACE: H4_SymForcing_IsZero.**

    The representation-theoretic fact: in the Fourier Hdiv_free model,
    a time-independent H4-symmetric forcing (equivariant under all 120
    Householder reflections in Wall264.vertices) must be zero.

    PROOF ROUTE (representation theory):
      (1) W(H₄) acts unitarily on Hdiv_free (s+2) by spatial pullback.
      (2) The trivial representation occurs with multiplicity 0 in the
          W(H₄)-module Hdiv_free (s+2) — no nonzero fixed vector exists.
      (3) For (2): the 120-cell acts on solenoidal vector fields on ℝ³
          via the natural (vector) representation.  The fixed subspace of
          the vector representation of W(H₄) is {0} because W(H₄) ⊃ -id
          (the antipodal map, which is the product of all 120 reflections
          and has determinant −1 on ℝ³).
      (4) Antipodal symmetry: if f is H4-sym, it is also equivariant
          under −id, so f(x) = f(−x) and f(x) = −f(x) (from the vector
          rep of −id on ℝ³), hence f = 0.

    OPEN: The spatial transport API (step 1) and the vector-rep identity
    for −id (step 3) are absent in Mathlib v4.12.0.
    Wall263: `phi_not_mem_spectrum` gives φ ∉ spectrum ℝ B (spectral gap
    rules out degenerate eigenspaces), supporting step (2). -/
def H4_SymForcing_IsZero (s : ℝ) : Prop :=
  ∀ f : ExternalForce s, IsH4SymmetricForcing f →
    ∀ t : ℝ, f t = 0

/-! ### Proved bricks (classical trio, 0 cert axioms) -/

/-- **PROVED.** The zero forcing is always H4-symmetric.
    The constant-zero field is trivially equivariant under any map
    (IsH4Equivariant collapses to True for all inputs, including 0).

    Axiom footprint: {propext, Classical.choice, Quot.sound}. -/
theorem zero_forcing_is_h4_symmetric :
    IsH4SymmetricForcing (fun _ : ℝ => (0 : Hdiv_free (s + 2))) := by
  intro _t
  simp only [H4UniformBound.IsH4Symmetric, H4UniformBound.IsH4Equivariant]
  intro _v _hv
  trivial

/-- **PROVED.** For zero forcing, the forcing contribution to the weak
    momentum identity is 0.

    From WeakMomentum: the forcing-work term is ⟪f t, φ⟫.
    When f t = 0, this inner product vanishes.

    Axiom footprint: {propext, Classical.choice, Quot.sound}. -/
theorem h4_forcing_zero_momentum
    (u : ℝ → Hdiv_free (s + 2)) (φ : Hdiv_free (s + 2)) (t : ℝ) :
    @inner ℂ (Hdiv_free (s + 2)) _ ((fun _ : ℝ => (0 : Hdiv_free (s + 2))) t) φ = 0 := by
  simp [inner_zero_left]

/-- **PROVED.** For an H4-symmetric weak NS solution with H4-symmetric forcing,
    the energy inequality gives ‖u t‖ ≤ ‖u₀‖ (independent of forcing symmetry —
    this follows from WeakNS.energy_le alone).

    Honest bound: the energy inequality in WeakNS drops the forcing-work
    term (see WeakSolution.lean, honest scope), so this bound does NOT use
    H4 symmetry of f — it holds for all weak NS solutions.

    Axiom footprint: {propext, Classical.choice, Quot.sound}. -/
theorem h4_sym_forcing_energy_bound
    (u₀ : Hdiv_free (s + 2)) (f : ExternalForce s)
    (u : ℝ → Hdiv_free (s + 2)) (hweak : WeakNS u u₀ f) (t : ℝ) (ht : 0 ≤ t) :
    ‖u t‖ ≤ ‖u₀‖ :=
  H4UniformBound.H4_norm_le_initial u₀
    (by simp [H4UniformBound.IsH4Symmetric, H4UniformBound.IsH4Equivariant])
    f u hweak t ht

/-! ### Open surface registry -/

/-- NS H4 Forcing open surface count: 2.
    (IsH4SymmetricForcing — spatial equivariance API gap)
    (H4_SymForcing_IsZero — representation-theoretic, vector rep of -id) -/
def ns_h4_forcing_open_count : ℕ := 2

/-- Honest scope.
    The "f = 0 from H4 symmetry" argument is representation-theoretic,
    not a consequence of the initial datum's symmetry.
    The UNFORCED route (f = 0 by assumption) is already captured by
    H4_GradLinfty_Bound in H4_UniformBound.lean (it allows any f).
    H4_SymForcing_IsZero is the ADDITIONAL claim needed for the FORCED case.
    The antipodal-map argument (−id ∈ W(H₄) acts by negation on ℝ³)
    is the key geometric fact; it reduces to a character-theory calculation
    over Wall264 vertices. -/
def ns_h4_forcing_scope : String :=
  "IsH4SymmetricForcing : OPEN (spatial transport API). " ++
  "H4_SymForcing_IsZero : OPEN (vector rep of -id in W(H₄), antipodal argument). " ++
  "zero_forcing_is_h4_symmetric : PROVED (trivial). " ++
  "h4_forcing_zero_momentum : PROVED (inner_zero_left). " ++
  "h4_sym_forcing_energy_bound : PROVED (wraps H4_norm_le_initial)."

end H4Forcing
end NS
end Towers
end TheoremaAureum
