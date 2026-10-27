import Mathlib.GroupTheory.GroupAction.Primitive
import Mathlib.Algebra.Group.Subgroup.Map

/-! Canonical literal permutation ranges under an actual point bijection.
The original subgroup, action and primitive/transitive predicates are
transported together; no group-isomorphism-only substitute is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FinitePermutationActionRelabel

variable {X Y : Type} (e : X ≃ Y) (H : Subgroup (Equiv.Perm X))

def group : Subgroup (Equiv.Perm Y) := H.map e.permCongrHom.toMonoidHom

def groupEquiv : H ≃* group e H :=
  H.equivMapOfInjective e.permCongrHom.toMonoidHom e.permCongrHom.injective

theorem equivariant (h : H) (x : X) :
    e (h • x)=groupEquiv e H h • e x := by
  change e (h.val x)=e (h.val (e.symm (e x)))
  rw [e.symm_apply_apply]

def pointHom : X →ₑ[(groupEquiv e H).toMonoidHom] Y where
  toFun := e
  map_smul' h x := equivariant e H h x

theorem pretransitive [MulAction.IsPretransitive H X] :
    MulAction.IsPretransitive (group e H) Y :=
  MulAction.IsPretransitive.of_surjective_map (f := pointHom e H) e.surjective inferInstance

theorem preprimitive [MulAction.IsPreprimitive H X] :
    MulAction.IsPreprimitive (group e H) Y :=
  MulAction.IsPreprimitive.of_surjective (f := pointHom e H) e.surjective

theorem recover : (group e H).map e.symm.permCongrHom.toMonoidHom=H := by
  rw [group,Subgroup.map_map]
  have hm : e.symm.permCongrHom.toMonoidHom.comp e.permCongrHom.toMonoidHom=
      MonoidHom.id (Equiv.Perm X) := by
    ext g x
    change e.symm (e (g (e.symm (e x))))=g x
    rw [e.symm_apply_apply,e.symm_apply_apply]
  rw [hm,Subgroup.map_id]

end SymmetricSubgroupAsymptotics.FinitePermutationActionRelabel
