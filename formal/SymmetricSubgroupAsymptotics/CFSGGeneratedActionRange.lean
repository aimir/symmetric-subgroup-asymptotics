import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Algebra.Group.Subgroup.Ker

/-! An actual generating set controls the complete range of a group
homomorphism, without an abstract group recognition premise. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGGeneratedActionRange
variable {G H : Type*} [Group G] [Group H]

theorem range_le_of_generators (S : Set G) (hS : Subgroup.closure S = ⊤)
    (f : G →* H) (R : Subgroup H) (hR : ∀ s ∈ S, f s ∈ R) : f.range ≤ R := by
  have h : Subgroup.closure S ≤ R.comap f := (Subgroup.closure_le _).mpr hR
  rw [hS] at h
  rintro y ⟨x, rfl⟩
  exact h (show x ∈ (⊤ : Subgroup G) from Subgroup.mem_top x)

end SymmetricSubgroupAsymptotics.CFSGGeneratedActionRange
