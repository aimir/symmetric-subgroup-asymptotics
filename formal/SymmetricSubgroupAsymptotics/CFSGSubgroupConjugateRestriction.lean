import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.GroupTheory.GroupAction.ConjAct

/-! Restrict and push forward actual subgroup-conjugation identities
along the SAME group maps. No injectivity of a quotient map is needed
for the push-forward identity. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGSubgroupConjugateRestriction
variable {G Q : Type*} [Group G] [Group Q]

theorem restrict_conjugate (H R S : Subgroup G) (hR : R≤H) (hS : S≤H) (g : H)
    (he : R.map (MulAut.conj (g : G)).toMonoidHom=S) :
    (R.subgroupOf H).map (MulAut.conj g).toMonoidHom=S.subgroupOf H := by
  apply Subgroup.map_injective H.subtype_injective
  calc
    _=((R.subgroupOf H).map H.subtype).map (MulAut.conj (g : G)).toMonoidHom := by
      rw [Subgroup.map_map,Subgroup.map_map]
      congr 1
    _=R.map (MulAut.conj (g : G)).toMonoidHom := by
      rw [Subgroup.map_subgroupOf_eq_of_le hR]
    _=S := he
    _=(S.subgroupOf H).map H.subtype := (Subgroup.map_subgroupOf_eq_of_le hS).symm

theorem map_conjugate (f : G→*Q) (R : Subgroup G) (g : G) :
    (R.map (MulAut.conj g).toMonoidHom).map f=
      (R.map f).map (MulAut.conj (f g)).toMonoidHom := by
  rw [Subgroup.map_map,Subgroup.map_map]
  congr 1
  ext x
  change f (g*x*g⁻¹)=f g*f x*(f g)⁻¹
  rw [map_mul,map_mul,map_inv]

end SymmetricSubgroupAsymptotics.CFSGSubgroupConjugateRestriction
