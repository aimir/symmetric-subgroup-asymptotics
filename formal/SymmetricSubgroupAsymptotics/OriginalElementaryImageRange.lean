import SymmetricSubgroupAsymptotics.ElementaryKernelIntersectionFiltration
import SymmetricSubgroupAsymptotics.OriginalKernelNonbinaryResidual

set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalKernelModuleChart
variable {Q B D : Type} [Group Q] [Group B] [Group D]
    {eta : Q →* D} {A : Rep.{0} (ZMod 2) D}
    (E : OriginalKernelModuleChart eta A) (pi : Q →* B)

theorem elementaryImage_range : (E.elementaryImageHom pi).range=eta.ker.map pi := by
  ext b
  constructor
  · rintro ⟨v,rfl⟩
    exact ⟨E.element v.toAdd,(E.equiv v).property,rfl⟩
  · rintro ⟨q,hq,rfl⟩
    obtain ⟨v,hv⟩ := E.equiv.surjective ⟨q,hq⟩
    refine ⟨v,?_⟩
    exact congrArg pi (congrArg Subtype.val hv)

theorem elementaryImage_normal (hpi : Function.Surjective pi) :
    (E.elementaryImageHom pi).range.Normal := by
  rw [E.elementaryImage_range pi]
  exact Subgroup.Normal.map inferInstance pi hpi

theorem elementaryImage_isPGroup_two : IsPGroup 2 (E.elementaryImageHom pi).range := by
  rw [E.elementaryImage_range pi]
  exact (E.kernel_isPGroup_two eta A).map pi

end SymmetricSubgroupAsymptotics.OriginalKernelModuleChart
