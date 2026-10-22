import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic.Group

/-! A parameter-range subgroup normalizes a generated subgroup when its
actual parameter commutators with the generators lie in that subgroup.
The group cancellation is proved with an opaque ambient group so concrete
matrix implementations need not be unfolded during elaboration. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGParameterCommutatorNormalizer
variable {G P : Type*} [Group G]

theorem range_normalizes_closure (root : P→G) (H : Subgroup G) (S : Set G)
    (hrange : ∀x,x∈H↔∃a,root a=x)
    (hcomm : ∀a,∀y∈S,root a*y*(root a)⁻¹*y⁻¹∈Subgroup.closure S) :
    H≤Subgroup.normalizer (Subgroup.closure S : Set G) := by
  apply Subgroup.le_normalizer_closure_iff.mpr
  intro x hx y hy
  obtain ⟨a,rfl⟩ := (hrange x).mp hx
  have hm := (Subgroup.closure S).mul_mem (hcomm a y hy) (Subgroup.subset_closure hy)
  convert hm using 1 <;> group

end SymmetricSubgroupAsymptotics.CFSGParameterCommutatorNormalizer
