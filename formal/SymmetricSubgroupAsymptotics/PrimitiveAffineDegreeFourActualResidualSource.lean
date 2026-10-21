import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourPublishedResidueSource
import SymmetricSubgroupAsymptotics.DegreeFourSixteenZeroCoreColdSource

/-! Actual degree4 residue assembly. The degree16 top is retained as a
faithful comparator of the original zero-core action, so no primitive16
classification or stronger finite-frame rank statement is needed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

def degreeFourZeroCoreActualResidualSource
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (published8 : DegreeEightCanonicalCatalogue.PublishedClassification)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput) : DegreeFourZeroCoreResidualSource := by
  intro w U hw basePoint block P inst hres hr hs hD
  exact match degreeFourZeroCoreExceptionalExhaustion block P
      hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm hr hD hs with
    | .inl source => source
    | .inr residue => Classical.choice (by
        rcases residue.down with hs2 | hs4 | hs8 | hs16
        · exact ⟨degreeFourZeroCoreTwoBlockSource block P hr hD hs2⟩
        · exact ⟨degreeFourFourBlockSource_of_retainedSocles block P hZmud lit hr hs4
            (fun N _ => degreeFourZeroCore_fourPoint_quotientSocle_le_two block P hMN hr hs4 hD N)⟩
        · exact ⟨degreeFourZeroCoreEightBlockSource_of_verifiedFrames block P
            hZmud lit (degreeFourZeroCoreEightBridgeInput_of_binarySchur
              hMN hTraceyPerm block P) hr hD hs8
                (degreeFourZeroCoreEightFrameBounds_of_published published8 block P hr hD hs8)⟩
        · exact ⟨degreeFourSixteenZeroCoreColdSource block P hTraceyPerm hr hs16 hD⟩)

def degreeFourActualResidualSource
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (published8 : DegreeEightCanonicalCatalogue.PublishedClassification)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hClifford : CliffordHomogeneousRestriction.Input)
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput) : PrimitiveAffineResidualDegreeSource 4 :=
  degreeFourResidualSource_of_zeroCore hZmud lit hMN hClifford hTraceyPerm
    (degreeFourZeroCoreActualResidualSource hZmud lit published8 hMN
      hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm)

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
