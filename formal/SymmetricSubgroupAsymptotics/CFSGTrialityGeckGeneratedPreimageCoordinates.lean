import SymmetricSubgroupAsymptotics.CFSGTrialityGeckGeneratedOriginalProjection
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckGeneratedPositiveSylow
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalOppositeAlignment

/-! Literal J embeds into the same natural derived-image preimage used
for opposite-pair alignment. Its negative root part maps onto the exact
originalNegative target from that alignment. This is a comparison of
actual matrix words and action homomorphisms, not an automorphism lift. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckGeneratedPreimageCoordinates
open CFSGTrialityGeckGeneratedOriginalProjection CFSGTrialityGeckGeneratedPositiveSylow
open CFSGTrialityGeckGoodSylow CFSGTrialityGeckOriginalIndexSquare
open CFSGTrialityGeckOriginalPreimageProjection CFSGTrialityGeckOriginalOppositeAlignment
open CFSGTrialityGeckPreimageOppositeAlignment CFSGTrialityGeckPreimageRawCoordinates
open CFSGTrialityGeckDerivedSylowNormalizer CFSGTrialityGeckFixedDerivedMatrixLift
open CFSGTrialityGeckRelativeRootGenerated CFSGTrialityGeckRootGeneratedPGroup
open CFSGTrialityGeckDiagramCovariance CFSGSerreOrdinaryTwists

def generatedToPreimage (q : CFSG.PrimePower) :
    fixedRootGenerated (q.Extension 3) (definingFieldAutomorphism q 3)→*naturalDerivedPreimage q where
  toFun g := ⟨generatedToMatrixFixed q g,(generatedToDerived q g).property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem generatedToPreimage_raw (q : CFSG.PrimePower)
    (g : fixedRootGenerated (q.Extension 3) (definingFieldAutomorphism q 3)) :
    preimageRawInclusion q (generatedToPreimage q g)=g.val := rfl

theorem generatedToPreimage_original (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)]
    (g : fixedRootGenerated (q.Extension 3) (definingFieldAutomorphism q 3)) :
    originalPreimageProjection q (generatedToPreimage q g)=generatedToOriginal q g := rfl

theorem rootPart_negative_original_image (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] :
    (rootPart (q.Extension 3) (definingFieldAutomorphism q 3) true).map (generatedToOriginal q)=
      originalNegative q := by
  ext g
  constructor
  · rintro ⟨x,hx,rfl⟩
    refine ⟨generatedToPreimage q x,?_,generatedToPreimage_original q x⟩
    change preimageRawInclusion q (generatedToPreimage q x)∈
      signedFixed (q.Extension 3) (definingFieldAutomorphism q 3) true
    rw [generatedToPreimage_raw]
    exact hx
  · rintro ⟨v,hv,rfl⟩
    have hneg : preimageRawInclusion q v∈signedFixed (q.Extension 3)
        (definingFieldAutomorphism q 3) true := hv
    let x : fixedRootGenerated (q.Extension 3) (definingFieldAutomorphism q 3) :=
      ⟨preimageRawInclusion q v,signedFixed_le_generated _ _ true hneg⟩
    refine ⟨x,hneg,?_⟩
    have he : generatedToDerived q x=preimageToImage q v := by
      apply Subtype.ext
      rfl
    exact congrArg (originalProjection q) he

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckGeneratedPreimageCoordinates
