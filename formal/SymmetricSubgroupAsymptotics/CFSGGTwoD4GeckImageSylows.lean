import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckActionCentralKernel
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckGeneratedSylow
import SymmetricSubgroupAsymptotics.CFSGCentralKernelPSubgroups
import SymmetricSubgroupAsymptotics.CFSGDisjointSylowProjectiveCardinality

/-! Named opposite Sylows of the SAME original G2 folded action image.
Both carriers are the images of actual J root parts; the proved
opposite-image separation survives the range restriction. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckImageSylows
open CFSGGTwoD4GeckImageRealization CFSGGTwoD4GeckGeneratedGroup
open CFSGGTwoD4GeckActionCentralKernel CFSGTrialityGeckGeneratedSylow
open CFSGTrialityGeckRelativeRootGenerated CFSGTrialityGeckRootGeneratedPGroup
open CFSGTrialityGeckOpposedImageKernel
variable (K : Type) [Field K] [Finite K]
local notation "J" => fixedRootGenerated K (RingEquiv.refl K)

abbrev imageGroup := (generatedImageAction K).range

abbrev generatedToImage : J→*imageGroup K := (generatedImageAction K).rangeRestrict

theorem generatedToImage_surjective : Function.Surjective (generatedToImage K) :=
  (generatedImageAction K).rangeRestrict_surjective

theorem generatedToImage_kernel_le_center : (generatedToImage K).ker≤Subgroup.center J := by
  intro x hx
  apply generatedImageAction_kernel_le_center K
  exact congrArg (fun z : imageGroup K=>z.val) hx

theorem generatedToImage_injOn_positive :
    Set.InjOn (generatedToImage K) (rootPart K (RingEquiv.refl K) false : Set J) := by
  intro x hx y hy he
  exact generatedImageAction_injOn_positive K hx hy
    (congrArg (fun z : imageGroup K=>z.val) he)

theorem opposite_parts_inf :
    (rootPart K (RingEquiv.refl K) false).map (generatedToImage K) ⊓
      (rootPart K (RingEquiv.refl K) true).map (generatedToImage K)=⊥ := by
  apply le_antisymm _ bot_le
  rintro x ⟨⟨g,hg,rfl⟩,h,hh,he⟩
  have hraw : generatedImageAction K h=generatedImageAction K g :=
    congrArg (fun z : imageGroup K=>z.val) he
  have hm : generatedImageAction K g∈
      (rootPart K (RingEquiv.refl K) false).map (generatedImageAction K) ⊓
      (rootPart K (RingEquiv.refl K) true).map (generatedImageAction K) :=
    ⟨⟨g,hg,rfl⟩,h,hh,hraw⟩
  rw [generated_opposite_action_images_disjoint,Subgroup.mem_bot] at hm
  exact Subgroup.mem_bot.mpr (Subtype.ext hm)

variable (p : ℕ) [Fact p.Prime] [CharP K p]

def negativeSylow : Sylow p J :=
  (positiveSylow K (RingEquiv.refl K) p).mapSurjective
    (f:=(MulAut.conj (oppositionInGenerated K (RingEquiv.refl K))).toMonoidHom)
    (MulAut.conj (oppositionInGenerated K (RingEquiv.refl K))).surjective

theorem negativeSylow_coe :
    (negativeSylow K p : Subgroup J)=rootPart K (RingEquiv.refl K) true := by
  simp only [negativeSylow,Sylow.coe_mapSurjective,positiveSylow_coe]
  exact rootPart_opposition K (RingEquiv.refl K)

def imagePositiveSylow : Sylow p (imageGroup K) :=
  (positiveSylow K (RingEquiv.refl K) p).mapSurjective
    (f:=generatedToImage K) (generatedToImage_surjective K)

def imageNegativeSylow : Sylow p (imageGroup K) :=
  (negativeSylow K p).mapSurjective (f:=generatedToImage K) (generatedToImage_surjective K)

theorem imagePositiveSylow_coe :
    (imagePositiveSylow K p : Subgroup (imageGroup K))=
      (rootPart K (RingEquiv.refl K) false).map (generatedToImage K) := by
  simp only [imagePositiveSylow,Sylow.coe_mapSurjective,positiveSylow_coe]

theorem imageNegativeSylow_coe :
    (imageNegativeSylow K p : Subgroup (imageGroup K))=
      (rootPart K (RingEquiv.refl K) true).map (generatedToImage K) := by
  simp only [imageNegativeSylow,Sylow.coe_mapSurjective,negativeSylow_coe]

theorem imageSylows_inf :
    (imagePositiveSylow K p : Subgroup (imageGroup K)) ⊓
      (imageNegativeSylow K p : Subgroup (imageGroup K))=⊥ := by
  rw [imagePositiveSylow_coe,imageNegativeSylow_coe]
  exact opposite_parts_inf K

theorem generatedToImage_positive_injective :
    Function.Injective ((generatedToImage K).comp
      (positiveSylow K (RingEquiv.refl K) p : Subgroup J).subtype) := by
  intro x y he
  apply Subtype.ext
  have hx : x.val∈rootPart K (RingEquiv.refl K) false := by
    rw [←positiveSylow_coe K (RingEquiv.refl K) p]
    exact x.property
  have hy : y.val∈rootPart K (RingEquiv.refl K) false := by
    rw [←positiveSylow_coe K (RingEquiv.refl K) p]
    exact y.property
  exact generatedToImage_injOn_positive K hx hy he

theorem imagePositiveSylow_card :
    Nat.card (imagePositiveSylow K p)=Nat.card (rootPart K (RingEquiv.refl K) false) := by
  change Nat.card ((positiveSylow K (RingEquiv.refl K) p : Subgroup J).map (generatedToImage K))=_
  have he := CFSGCentralKernelPElements.p_subgroup_card_map (generatedToImage K)
    (positiveSylow K (RingEquiv.refl K) p) (generatedToImage_positive_injective K p)
    (generatedToImage_kernel_le_center K) (positiveSylow K (RingEquiv.refl K) p : Subgroup J)
    (positiveSylow K (RingEquiv.refl K) p).isPGroup'
  rw [he]
  change Nat.card (positiveSylow K (RingEquiv.refl K) p : Subgroup J)=_
  rw [positiveSylow_coe]

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckImageSylows
