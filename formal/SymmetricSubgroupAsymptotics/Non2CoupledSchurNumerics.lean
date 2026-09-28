import SymmetricSubgroupAsymptotics.RepresentationSchurRows
import Mathlib.Tactic.Linarith

/-!
# Numerical branches of the coupled nonbinary socle estimate

For one nonfixed simple row, let `t` be the fixed dimension, `r` its
fractional Schur density, and `L` the dimension of the mixed trivial/simple
section.  The four structural branches in the manuscript reduce to the
linear inequalities recorded here.  A second theorem passes the resulting
uniform row bound through the actual nonfixed Schur supremum.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra

namespace SymmetricSubgroupAsymptotics

/-- The nonfaithful-kernel branch: `L ≤ s/2` and `3r ≤ L-t`. -/
theorem non2Coupled_nonfaithful
    {s t r L : ℝ} (ht : t ≤ 11 * s / 32)
    (hL : L ≤ s / 2) (hr : 3 * r ≤ L - t) :
    2 * t + 4 * r ≤ 43 * s / 48 := by
  linarith

/-- The shared-`C₃` scalar branch: the cost is exactly twice the mixed
section dimension, which is at most `3s/8`. -/
theorem non2Coupled_scalarC3
    {s t r L : ℝ} (hL : L ≤ 3 * s / 8) (hmixed : t + 2 * r = L) :
    2 * t + 4 * r ≤ 3 * s / 4 := by
  linarith

/-- The faithful small-degree branch with `hd=8`: the mixed section has
dimension at most `s`, while the fixed row has the sharper `s/5` bound. -/
theorem non2Coupled_faithfulSmall
    {s t r L : ℝ} (ht : t ≤ s / 5) (hL : L ≤ s)
    (hr : 8 * r ≤ L - t) :
    2 * t + 4 * r ≤ 4 * s / 5 := by
  linarith

/-- The faithful large-degree branch with `hd≥9`. -/
theorem non2Coupled_faithfulLarge
    {s t r L : ℝ} (ht : t ≤ 11 * s / 32) (hL : L ≤ s)
    (hr : 9 * r ≤ L - t) :
    2 * t + 4 * r ≤ 47 * s / 48 := by
  linarith

/-- The four exhaustive numerical certificates for one nonfixed simple
row.  Constructing one certificate is the remaining structural content of
the coupled socle proposition. -/
def Non2CoupledRowCertificate (s t r : ℝ) : Prop :=
  (∃ L : ℝ, t ≤ 11 * s / 32 ∧ L ≤ s / 2 ∧ 3 * r ≤ L - t) ∨
  (∃ L : ℝ, L ≤ 3 * s / 8 ∧ t + 2 * r = L) ∨
  (∃ L : ℝ, t ≤ s / 5 ∧ L ≤ s ∧ 8 * r ≤ L - t) ∨
  (∃ L : ℝ, t ≤ 11 * s / 32 ∧ L ≤ s ∧ 9 * r ≤ L - t)

theorem Non2CoupledRowCertificate.cost_le
    {s t r : ℝ} (hs : 0 ≤ s) (h : Non2CoupledRowCertificate s t r) :
    2 * t + 4 * r ≤ 47 * s / 48 := by
  rcases h with ⟨L, ht, hL, hr⟩ | ⟨L, hL, hmixed⟩ |
      ⟨L, ht, hL, hr⟩ | ⟨L, ht, hL, hr⟩
  · exact (non2Coupled_nonfaithful ht hL hr).trans (by linarith)
  · exact (non2Coupled_scalarC3 hL hmixed).trans (by linarith)
  · exact (non2Coupled_faithfulSmall ht hL hr).trans (by linarith)
  · exact non2Coupled_faithfulLarge ht hL hr

universe u
variable {k B A : Type u} [Field k] [Group B]
    [AddCommGroup A] [Module k A]

/-- A uniform affine bound on every actual nonfixed simple row passes to
the concrete nonfixed Schur capacity.  The base inequality handles the
inserted zero when no nonfixed simple row exists. -/
theorem representationNonfixedSchurCapacity_coupled_of_rows
    [FiniteDimensional k A]
    (σ : Representation k B A) (t K : ℝ)
    (hbase : 2 * t ≤ K)
    (hrows : ∀ (S : Submodule k[B] σ.asModule),
      IsSimpleModule k[B] S →
      (hfixed : ¬ representationSubmoduleFixed σ S) →
      2 * t + 4 *
        ((Module.finrank k (S →ₗ[k[B]] σ.asModule) : ℝ) /
          Module.finrank k S) ≤ K) :
    2 * t + 4 * representationNonfixedSchurCapacity σ ≤ K := by
  have hcap : representationNonfixedSchurCapacity σ ≤ (K - 2 * t) / 4 := by
    unfold representationNonfixedSchurCapacity
    apply csSup_le (Set.insert_nonempty _ _)
    rintro x (rfl | ⟨S, hS, hfixed, rfl⟩)
    · linarith
    · exact (by
        have h := hrows S hS hfixed
        linarith)
  linarith

/-- Certificate form of the complete coupled nonfixed-row estimate. -/
theorem representationNonfixedSchurCapacity_coupled_of_certificates
    [FiniteDimensional k A]
    (σ : Representation k B A) (s t : ℝ)
    (hs : 0 ≤ s)
    (hbase : 2 * t ≤ 47 * s / 48)
    (hcert : ∀ (S : Submodule k[B] σ.asModule),
      IsSimpleModule k[B] S →
      (hfixed : ¬ representationSubmoduleFixed σ S) →
      Non2CoupledRowCertificate s t
        ((Module.finrank k (S →ₗ[k[B]] σ.asModule) : ℝ) /
          Module.finrank k S)) :
    2 * t + 4 * representationNonfixedSchurCapacity σ ≤
      47 * s / 48 := by
  apply representationNonfixedSchurCapacity_coupled_of_rows σ t
    (47 * s / 48) hbase
  intro S hS hfixed
  exact (hcert S hS hfixed).cost_le hs

end SymmetricSubgroupAsymptotics

end
