import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.Algebra.Group.Subgroup.Map

/-! The literal subgroup of automorphisms fixing every member of a
displayed subgroup family. No permutation or linearity is built in. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSubgroupFamilyStabilizer
variable {G J : Type*} [Group G]

def familyStabilizer (S : J → Subgroup G) : Subgroup (MulAut G) where
  carrier := {f | ∀ j, (S j).map f.toMonoidHom = S j}
  one_mem' := by intro j; exact Subgroup.map_id (S j)
  mul_mem' := by
    intro f g hf hg j
    have hc : (f * g).toMonoidHom = f.toMonoidHom.comp g.toMonoidHom := rfl
    rw [hc, ← Subgroup.map_map, hg j, hf j]
  inv_mem' := by
    intro f hf j
    change (S j).map f.symm.toMonoidHom = S j
    apply Subgroup.map_injective (f := f.toMonoidHom) f.injective
    rw [Subgroup.map_map]
    have hc : f.toMonoidHom.comp f.symm.toMonoidHom = MonoidHom.id G := by
      ext x
      exact f.apply_symm_apply x
    rw [hc, Subgroup.map_id, hf j]

@[simp] theorem mem_familyStabilizer (S : J → Subgroup G) (f : MulAut G) :
    f ∈ familyStabilizer S ↔ ∀ j, (S j).map f.toMonoidHom = S j := Iff.rfl

end SymmetricSubgroupAsymptotics.CFSGSubgroupFamilyStabilizer
