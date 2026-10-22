import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.GroupTheory.GroupAction.ConjAct

/-! Restriction of an actual ambient automorphism and transport of its
subgroup images through an equivariant coordinate homomorphism. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGInvariantSubgroupCoordinateImage
variable {G C : Type*} [Group G] [Group C]

def restrictAut (H : Subgroup G) (f : MulAut G)
    (hH : H.map f.toMonoidHom=H) : MulAut H :=
  (f.subgroupMap H).trans (MulEquiv.subgroupCongr hH)

theorem restrictAut_val (H : Subgroup G) (f : MulAut G)
    (hH : H.map f.toMonoidHom=H) (x : H) :
    (restrictAut H f hH x : G)=f x := rfl

theorem restrictAut_map (H R S : Subgroup G) (f : MulAut G)
    (hH : H.map f.toMonoidHom=H) (hR : R≤H) (hS : S≤H)
    (he : R.map f.toMonoidHom=S) :
    (R.subgroupOf H).map (restrictAut H f hH).toMonoidHom=S.subgroupOf H := by
  apply Subgroup.map_injective H.subtype_injective
  calc
    _=((R.subgroupOf H).map H.subtype).map f.toMonoidHom := by
      rw [Subgroup.map_map,Subgroup.map_map]
      congr 1
    _=R.map f.toMonoidHom := by rw [Subgroup.map_subgroupOf_eq_of_le hR]
    _=S := he
    _=(S.subgroupOf H).map H.subtype := (Subgroup.map_subgroupOf_eq_of_le hS).symm

theorem coordinate_image_map (H : Subgroup G) (f : MulAut G)
    (hH : H.map f.toMonoidHom=H) (coord : H→*C) (F : MulAut C)
    (hF : ∀x : H,F (coord x)=coord (restrictAut H f hH x))
    (R S : Subgroup G) (hR : R≤H) (hS : S≤H) (he : R.map f.toMonoidHom=S) :
    ((R.subgroupOf H).map coord).map F.toMonoidHom=(S.subgroupOf H).map coord := by
  calc
    _=((R.subgroupOf H).map (restrictAut H f hH).toMonoidHom).map coord := by
      rw [Subgroup.map_map,Subgroup.map_map]
      congr 1
      apply MonoidHom.ext
      intro x
      exact hF x
    _=(S.subgroupOf H).map coord := by rw [restrictAut_map H R S f hH hR hS he]

theorem map_ne_bot (F : MulAut C) (L : Subgroup C) (hL : L≠⊥) :
    L.map F.toMonoidHom≠⊥ := by
  intro he
  apply hL
  apply Subgroup.map_injective (f := F.toMonoidHom) F.injective
  exact he.trans (Subgroup.map_bot F.toMonoidHom).symm

end SymmetricSubgroupAsymptotics.CFSGInvariantSubgroupCoordinateImage
