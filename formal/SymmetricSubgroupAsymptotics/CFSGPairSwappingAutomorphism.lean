import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.GroupTheory.GroupAction.ConjAct

/-! Conjugating an actual ambient automorphism by a given pair-swapping
automorphism transfers preservation of the second subgroup to the first. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGPairSwappingAutomorphism
variable {G : Type*} [Group G]

theorem inverse_swap (U V : Subgroup G) (e : MulAut G)
    (he : U.map e.toMonoidHom=V) : V.map e.symm.toMonoidHom=U := by
  rw [←he,Subgroup.map_map]
  have hh : e.symm.toMonoidHom.comp e.toMonoidHom=MonoidHom.id G := by
    apply MonoidHom.ext
    intro x
    exact e.symm_apply_apply x
  rw [hh,Subgroup.map_id]

theorem conjugate_preserves_first (U V : Subgroup G) (e f : MulAut G)
    (he : U.map e.toMonoidHom=V) (hf : V.map f.toMonoidHom=V) :
    U.map (e.symm*f*e).toMonoidHom=U := by
  have hh : (e.symm*f*e).toMonoidHom=
      e.symm.toMonoidHom.comp (f.toMonoidHom.comp e.toMonoidHom) := by
    apply MonoidHom.ext
    intro x
    rfl
  rw [hh,←Subgroup.map_map,←Subgroup.map_map,he,hf]
  exact inverse_swap U V e he

end SymmetricSubgroupAsymptotics.CFSGPairSwappingAutomorphism
