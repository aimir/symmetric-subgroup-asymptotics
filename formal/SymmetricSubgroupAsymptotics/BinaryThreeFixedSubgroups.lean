import SymmetricSubgroupAsymptotics.BinaryThreeInvariantSubspaces

/-! A fixed vector or fixed dual vector is a subgroup condition, so it
suffices to check the literal generators of a listed subgroup. -/

set_option autoImplicit false
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.BinaryThreeInvariantSubspaces

def fixesVector (v : Vector) : Subgroup Ambient where
  carrier := {g | g.val *ᵥ v = v}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    change (g.val * h.val) *ᵥ v = v
    rw [← Matrix.mulVec_mulVec, hh, hg]
  inv_mem' := by
    intro g hg
    change g.inv *ᵥ v = v
    calc
      _ = g.inv *ᵥ (g.val *ᵥ v) := congrArg (g.inv *ᵥ ·) hg.symm
      _ = (g.inv * g.val) *ᵥ v := Matrix.mulVec_mulVec _ _ _
      _ = v := by rw [g.inv_val]; simp

def fixesCovector (l : Vector) : Subgroup Ambient where
  carrier := {g | l ᵥ* g.val = l}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    change l ᵥ* (g.val * h.val) = l
    rw [← Matrix.vecMul_vecMul, hg, hh]
  inv_mem' := by
    intro g hg
    change l ᵥ* g.inv = l
    calc
      _ = (l ᵥ* g.val) ᵥ* g.inv := congrArg (· ᵥ* g.inv) hg.symm
      _ = l ᵥ* (g.val * g.inv) := Matrix.vecMul_vecMul _ _ _
      _ = l := by rw [g.val_inv]; simp

theorem generators_fix_vector {G I : Type*} [Group G]
    (f : G →* Ambient) (generators : I → G) (v : Vector)
    (h : ∀ i, (f (generators i)).val *ᵥ v = v) :
    ∀ g ∈ Subgroup.closure (Set.range generators), (f g).val *ᵥ v = v := by
  have hle : Subgroup.closure (Set.range generators) ≤ (fixesVector v).comap f := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    exact h i
  exact fun g hg => hle hg

theorem generators_fix_covector {G I : Type*} [Group G]
    (f : G →* Ambient) (generators : I → G) (l : Vector)
    (h : ∀ i, l ᵥ* (f (generators i)).val = l) :
    ∀ g ∈ Subgroup.closure (Set.range generators), l ᵥ* (f g).val = l := by
  have hle : Subgroup.closure (Set.range generators) ≤ (fixesCovector l).comap f := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    exact h i
  exact fun g hg => hle hg

end SymmetricSubgroupAsymptotics.BinaryThreeInvariantSubspaces
