import Mathlib.GroupTheory.IsSubnormal
import Mathlib.Algebra.Group.Subgroup.Ker

/-! A subnormal source subgroup has subnormal image when the ACTUAL
range of the homomorphism is subnormal in the target. Surjectivity is
used only for rangeRestrict; the original homomorphism need not be
surjective. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.SubnormalImageOfSubnormalRange

variable {G Q : Type*} [Group G] [Group Q]

theorem map_isSubnormal (f : G →* Q) (hf : f.range.IsSubnormal)
    (H : Subgroup G) (hH : H.IsSubnormal) : (H.map f).IsSubnormal := by
  have h := (Subgroup.IsSubnormal.map (f := f.rangeRestrict)
    f.rangeRestrict_surjective hH).trans' hf
  simpa only [Subgroup.map_map,MonoidHom.subtype_comp_rangeRestrict] using h

theorem restricted_range_isSubnormal (f : G →* Q) (hf : f.range.IsSubnormal)
    (H : Subgroup G) (hH : H.IsSubnormal) : (f.comp H.subtype).range.IsSubnormal := by
  rw [MonoidHom.range_comp,Subgroup.range_subtype]
  exact map_isSubnormal f hf H hH

end SymmetricSubgroupAsymptotics.SubnormalImageOfSubnormalRange
