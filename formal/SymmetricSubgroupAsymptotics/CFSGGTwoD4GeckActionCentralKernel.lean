import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOppositeActionImages
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckGeneratedGroup
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOpposedImageKernel

/-! The actual action of J(K,id) on the SAME original G2 integral image
has central kernel. Its positive injectivity and opposite-image
separation are proved by the original two Cartans. No natural-eight
faithfulness or projective correspondence is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckActionCentralKernel
open CFSGGTwoD4GeckImageRealization CFSGGTwoD4GeckGeneratedGroup
open CFSGGTwoD4GeckOppositeActionImages CFSGTrialityGeckRelativeRootGenerated
open CFSGTrialityGeckRootGeneratedPGroup
variable (K : Type) [Field K] [Finite K]
local notation "J" => fixedRootGenerated K (RingEquiv.refl K)

theorem generatedImageAction_injOn_positive :
    Set.InjOn (generatedImageAction K) (rootPart K (RingEquiv.refl K) false : Set J) := by
  intro g hg h hh he
  apply (generatedEquiv K).injective
  have hg' : generatedEquiv K g∈positivePart K := hg.1
  have hh' : generatedEquiv K h∈positivePart K := hh.1
  change foldedImageAction K (generatedEquiv K g)=foldedImageAction K (generatedEquiv K h) at he
  exact foldedImageAction_injOn_positive K hg' hh' he

theorem generated_opposite_action_images_disjoint :
    (rootPart K (RingEquiv.refl K) false).map (generatedImageAction K) ⊓
      (rootPart K (RingEquiv.refl K) true).map (generatedImageAction K)=⊥ := by
  apply le_antisymm _ bot_le
  rintro x ⟨⟨g,hg,rfl⟩,h,hh,he⟩
  have hraw : foldedImageAction K (generatedEquiv K g)=foldedImageAction K (generatedEquiv K h) := he.symm
  have hgone : generatedEquiv K g=1 :=
    positive_eq_one_of_opposite_action_eq K (generatedEquiv K g) (generatedEquiv K h) hg.1 hh.1 hraw
  have hg1 : g=1 := (generatedEquiv K).injective (hgone.trans (map_one (generatedEquiv K)).symm)
  simpa only [hg1,map_one,Subgroup.mem_bot]

theorem generatedImageAction_kernel_le_center :
    (generatedImageAction K).ker≤Subgroup.center J :=
  CFSGTrialityGeckOpposedImageKernel.kernel_le_center K (RingEquiv.refl K)
    (generatedImageAction K) (generatedImageAction_injOn_positive K)
    (generated_opposite_action_images_disjoint K)

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckActionCentralKernel
