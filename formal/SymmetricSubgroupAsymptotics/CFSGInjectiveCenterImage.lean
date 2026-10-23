import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Algebra.Group.Subgroup.Map

/-! The intrinsic centre of an injective group image is the image of
the source centre. This records the exact ambient subgroup maps. -/
set_option autoImplicit false

namespace SymmetricSubgroupAsymptotics.CFSGInjectiveCenterImage
variable {G H : Type*} [Group G] [Group H]

theorem center_image (f : G →* H) (hf : Function.Injective f) :
    (Subgroup.center G).map f = (Subgroup.center f.range).map f.range.subtype := by
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨⟨f g, ⟨g, rfl⟩⟩, ?_, rfl⟩
    apply Subgroup.mem_center_iff.mpr
    intro y
    obtain ⟨v, hv⟩ := y.property
    apply Subtype.ext
    change y.val * f g = f g * y.val
    rw [← hv, ← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hg v]
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨g, hg⟩ := z.property
    refine ⟨g, ?_, hg⟩
    apply Subgroup.mem_center_iff.mpr
    intro a
    apply hf
    have he := congrArg (fun y : f.range => y.val)
      (Subgroup.mem_center_iff.mp hz ⟨f a, ⟨a, rfl⟩⟩)
    change f a * z.val = z.val * f a at he
    simpa only [map_mul, hg] using he

end SymmetricSubgroupAsymptotics.CFSGInjectiveCenterImage
