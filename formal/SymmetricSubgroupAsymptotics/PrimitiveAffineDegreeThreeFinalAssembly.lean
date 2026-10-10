import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockDiagonalComparison
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockTwoSignStructural

/-!
# Final source-only assembly for the degree-three affine residual

The diagonal four-block comparison is already constructed from the literal
action.  Consequently the ordinary residual-source route has only two
remaining mathematical inputs: the two-sign four-block comparison and the
post-four source at six, twelve, and eighteen blocks.  This file records the
resulting composition without adding a classification or counting premise.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

/-- Assemble the full degree-three residual source from the two remaining
ordinary-source construction boundaries. -/
noncomputable def degreeThreeResidualSource_of_twoSignAndPostFour
    (hKP : KovacsPraegerAbelianizationBound)
    (publishedSix : PublishedDegreeSixThreeByTwoAffineClassification)
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (hClifford : CliffordHomogeneousRestriction.Input)
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hgen : PermutationSubgroupGeneratorBound)
    (publishedPairs : PublishedDegreeTwoFourPairClassification)
    (twoSign : DegreeThreeFourBlockTwoSignComparisonSource)
    (postFour : DegreeThreeNonzeroSignedKernelPostFourResidualSource) :
    PrimitiveAffineResidualDegreeSource 3 :=
  degreeThreeResidualSource_of_nonzeroLater hKP publishedSix hZmud lit
    hClifford hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
      (degreeThreeNonzeroSignedKernelLaterSource_of_postFour hTraceyHalf
        hTraceyLog hTraceyRefined hTraceyPerm hgen hZmud lit publishedPairs
        (degreeThreeFourBlockBinarySource_of_signedComparisons hTraceyHalf
          hTraceyLog hTraceyRefined hTraceyPerm
          degreeThreeFourBlockDiagonalComparisonSource twoSign)
        postFour)

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
