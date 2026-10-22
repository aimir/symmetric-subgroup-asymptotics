import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-! Orthogonal-complement lattice identities needed by the actual
maximal-singular triangle. No orthogonal group or component is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexOrthogonalLattice
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem orthogonal_sup (B : LinearMap.BilinForm K V) (P L : Submodule K V) :
    B.orthogonal (P ⊔ L) = B.orthogonal P ⊓ B.orthogonal L := by
  ext x
  constructor
  · intro hx
    exact ⟨fun p hp => hx p (Submodule.mem_sup_left hp),
      fun l hl => hx l (Submodule.mem_sup_right hl)⟩
  · rintro ⟨hP, hL⟩ y hy
    obtain ⟨p, hp, l, hl, rfl⟩ := Submodule.mem_sup.mp hy
    change B (p + l) x = 0
    rw [LinearMap.BilinForm.add_left, hP p hp, hL l hl, add_zero]

theorem orthogonal_inf [FiniteDimensional K V] (B : LinearMap.BilinForm K V)
    (hB : B.Nondegenerate) (hRefl : B.IsRefl) (P L : Submodule K V) :
    B.orthogonal (P ⊓ L) = B.orthogonal P ⊔ B.orthogonal L := by
  have he : B.orthogonal (B.orthogonal P ⊔ B.orthogonal L) = P ⊓ L := by
    rw [orthogonal_sup, B.orthogonal_orthogonal hB hRefl P,
      B.orthogonal_orthogonal hB hRefl L]
  rw [← he, B.orthogonal_orthogonal hB hRefl]

theorem total_sum_orthogonal (B : LinearMap.BilinForm K V) (P L M : Submodule K V)
    (hP : B.orthogonal P = P) (hL : B.orthogonal L = L)
    (hM : B.orthogonal M = M) :
    B.orthogonal (P ⊔ L ⊔ M) = P ⊓ L ⊓ M := by
  rw [orthogonal_sup, orthogonal_sup, hP, hL, hM]

theorem middle_range_orthogonal [FiniteDimensional K V] (B : LinearMap.BilinForm K V)
    (hB : B.Nondegenerate) (hRefl : B.IsRefl) (P L M : Submodule K V)
    (hP : B.orthogonal P = P) (hL : B.orthogonal L = L)
    (hM : B.orthogonal M = M) :
    B.orthogonal (L ⊓ (P ⊔ M)) = L ⊔ (P ⊓ M) := by
  rw [orthogonal_inf B hB hRefl, orthogonal_sup, hP, hL, hM]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexOrthogonalLattice
