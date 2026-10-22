import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-! Actual kernels of skew-adjoint linear maps are orthogonal
complements of their actual ranges. Orthogonal lattice laws are proved
from their definitions and finite-dimensional nondegeneracy. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSkewOrthogonalKernels
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

 theorem orthogonal_sup (B : LinearMap.BilinForm K V) (P Q : Submodule K V) :
    B.orthogonal (P ⊔ Q) = B.orthogonal P ⊓ B.orthogonal Q := by
  ext x
  change (∀ u ∈ P ⊔ Q, B u x = 0) ↔
    (∀ u ∈ P, B u x = 0) ∧ (∀ u ∈ Q, B u x = 0)
  constructor
  · intro h
    have hPin : P ≤ P ⊔ Q := le_sup_left
    have hQin : Q ≤ P ⊔ Q := le_sup_right
    exact ⟨fun u hu => h u (hPin hu), fun u hu => h u (hQin hu)⟩
  · rintro ⟨hP, hQ⟩ u hu
    obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hu
    rw [map_add, LinearMap.add_apply, hP p hp, hQ q hq, add_zero]

 theorem orthogonal_inf [FiniteDimensional K V] (B : LinearMap.BilinForm K V)
    (hB : B.Nondegenerate) (hs : ∀ x y, B x y = B y x) (P Q : Submodule K V) :
    B.orthogonal (P ⊓ Q) = B.orthogonal P ⊔ B.orthogonal Q := by
  have hr : B.IsRefl := fun x y h => (hs y x).trans h
  have h := orthogonal_sup B (B.orthogonal P) (B.orthogonal Q)
  rw [B.orthogonal_orthogonal hB hr P, B.orthogonal_orthogonal hB hr Q] at h
  have hh := congrArg (fun S : Submodule K V => B.orthogonal S) h
  dsimp only at hh
  rw [B.orthogonal_orthogonal hB hr] at hh
  exact hh.symm

 theorem skew_ker_eq_orthogonal_range (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (A : V →ₗ[K] V) (hA : ∀ x y, B (A x) y = -B x (A y)) :
    LinearMap.ker A = B.orthogonal (LinearMap.range A) := by
  ext x
  constructor
  · intro hx
    change A x = 0 at hx
    rintro y ⟨z, rfl⟩
    change B (A z) x = 0
    rw [hA, hx, map_zero, neg_zero]
  · intro hx
    change A x = 0
    apply hB.2
    intro y
    have hz : B (A y) x = 0 := hx (A y) ⟨y, rfl⟩
    have he := hA y x
    rw [hz] at he
    exact neg_eq_zero.mp he.symm

end SymmetricSubgroupAsymptotics.CFSGSkewOrthogonalKernels
