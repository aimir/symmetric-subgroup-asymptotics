import SymmetricSubgroupAsymptotics.CFSGSolublePrimitiveContainersCount
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.GroupAction.Basic

/-! Actual affine envelopes of soluble automorphism subgroups. The natural
permutation action is faithful and is conjugated by an explicit point
equivalence when installed on a labelled point set. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGSolublePrimitiveContainers
universe u v

variable (T : Type u) [Group T]

def autPermutation : MulAut T →* Equiv.Perm T where
  toFun a := a.toEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

abbrev AffineGroup (H : Subgroup (MulAut T)) := T ⋊[H.subtype] H

def affineAction (H : Subgroup (MulAut T)) : AffineGroup T H →* Equiv.Perm T :=
  SemidirectProduct.lift (MulAction.toPermHom T T)
    ((autPermutation T).comp H.subtype) (by
      intro h
      apply MonoidHom.ext
      intro t
      apply Equiv.ext
      intro x
      change (h : MulAut T) t * x =
        (h : MulAut T) (t * (h : MulAut T).symm x)
      rw [map_mul, MulEquiv.apply_symm_apply])

theorem affineAction_apply (H : Subgroup (MulAut T)) (g : AffineGroup T H) (t : T) :
    affineAction T H g t = g.left * (g.right : MulAut T) t := rfl

theorem affineAction_injective (H : Subgroup (MulAut T)) :
    Function.Injective (affineAction T H) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hpoint : ∀ t : T, g.left * (g.right : MulAut T) t = t := by
    intro t
    change affineAction T H g t = t
    rw [hg]
    rfl
  have hl : g.left = 1 := by
    simpa only [map_one, mul_one] using hpoint 1
  have hr : g.right = 1 := by
    apply Subtype.ext
    apply MulEquiv.ext
    intro t
    simpa only [hl, one_mul, MulAut.one_apply] using hpoint t
  exact SemidirectProduct.ext hl hr

theorem affineGroup_soluble (H : Subgroup (MulAut T))
    [IsSolvable T] [IsSolvable H] : IsSolvable (AffineGroup T H) := by
  apply solvable_of_ker_le_range
    (SemidirectProduct.inl : T →* AffineGroup T H)
    (SemidirectProduct.rightHom : AffineGroup T H →* H)
  exact le_of_eq SemidirectProduct.range_inl_eq_ker_rightHom.symm

def labelledEnvelope {X : Type v} (H : Subgroup (MulAut T)) (e : T ≃ X) :
    Subgroup (Equiv.Perm X) :=
  (e.permCongrHom.toMonoidHom.comp (affineAction T H)).range

theorem labelledEnvelope_soluble {X : Type v} (H : Subgroup (MulAut T)) (e : T ≃ X)
    [IsSolvable T] [IsSolvable H] : IsSolvable (labelledEnvelope T H e) := by
  letI solublePrimitiveAffine_source : IsSolvable (AffineGroup T H) := affineGroup_soluble T H
  exact solvable_of_surjective
    (e.permCongrHom.toMonoidHom.comp (affineAction T H)).rangeRestrict_surjective

end SymmetricSubgroupAsymptotics.CFSGSolublePrimitiveContainers
