import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.NoncommCoprod

/-! Two elementwise commuting nilpotent subgroups have a nilpotent join,
including when their intersection is nontrivial. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

theorem nilpotent_sup_of_commuting
    {G : Type} [Group G] (A B : Subgroup G)
    [Group.IsNilpotent A] [Group.IsNilpotent B]
    (hcomm : ∀ a : A, ∀ b : B, Commute (a : G) (b : G)) :
    Group.IsNilpotent (A⊔B : Subgroup G) := by
  let f : A×B →* G := A.subtype.noncommCoprod B.subtype hcomm
  have hr : f.range=A⊔B := by
    rw [MonoidHom.noncommCoprod_range,Subgroup.range_subtype,Subgroup.range_subtype]
  letI : Group.IsNilpotent f.range :=
    Group.nilpotent_of_surjective f.rangeRestrict f.rangeRestrict_surjective
  exact Group.nilpotent_of_mulEquiv (MulEquiv.subgroupCongr hr)

end SymmetricSubgroupAsymptotics
