import SymmetricSubgroupAsymptotics.CFSGTrialityGeckRootPartCoordinates
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalRootFamily

/-! The literal relative-root-generated group surjects onto the SAME
original triality projective model, and the restriction to its positive
root part is injective. This retains the checked two-stage action cover. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckGeneratedOriginalProjection
open CFSGTrialityGeckRootPartCoordinates CFSGTrialityGeckRootGeneratedPGroup
open CFSGTrialityGeckGoodSylow CFSGTrialityGeckRelativeRootGenerated
open CFSGTrialityGeckOriginalIndexSquare CFSGTrialityGeckOriginalRootFamily
open CFSGTrialityGeckFixedPositiveImageSylow CFSGTrialityGeckPositiveDerivedEquiv
open CFSGSerreOrdinaryTwists

def generatedToOriginal (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TrialityD4 q)] :
    fixedRootGenerated (q.Extension 3) (definingFieldAutomorphism q 3) →*
      CFSG.Models.TrialityD4 q := (originalProjection q).comp (generatedToDerived q)

theorem generatedToOriginal_surjective (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] : Function.Surjective (generatedToOriginal q) :=
  (originalProjection_surjective q).comp (generatedToDerived_surjective q)

theorem rootPart_positive_original_injective (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] :
    Function.Injective ((generatedToOriginal q).comp
      (rootPart (q.Extension 3) (definingFieldAutomorphism q 3) false).subtype) := by
  intro x y he
  have hxP : generatedToDerived q x.val ∈ imagePositiveSylow q :=
    (positivePart_derived_image q).le ⟨x.val,x.property,rfl⟩
  have hyP : generatedToDerived q y.val ∈ imagePositiveSylow q :=
    (positivePart_derived_image q).le ⟨y.val,y.property,rfl⟩
  let a : imagePositiveSylow q := ⟨generatedToDerived q x.val,hxP⟩
  let b : imagePositiveSylow q := ⟨generatedToDerived q y.val,hyP⟩
  have hab : (originalProjection q).comp
      (imagePositiveSylow q : Subgroup (DerivedImage q)).subtype a =
      (originalProjection q).comp
        (imagePositiveSylow q : Subgroup (DerivedImage q)).subtype b := he
  have hd : generatedToDerived q x.val = generatedToDerived q y.val :=
    congrArg (fun z : imagePositiveSylow q => z.val) (originalProjection_sylow_injective q hab)
  have hp : positiveToDerived q (positivePartEquiv _ _ x) =
      positiveToDerived q (positivePartEquiv _ _ y) :=
    (positivePart_derived_action q x).symm.trans (hd.trans (positivePart_derived_action q y))
  exact (positivePartEquiv _ _).injective (positiveToDerived_injective q hp)

theorem rootPart_positive_original_image (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] :
    (rootPart (q.Extension 3) (definingFieldAutomorphism q 3) false).map
      (generatedToOriginal q) = (originalSylow q : Subgroup (CFSG.Models.TrialityD4 q)) := by
  rw [generatedToOriginal,← Subgroup.map_map,positivePart_derived_image]
  rfl

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckGeneratedOriginalProjection
