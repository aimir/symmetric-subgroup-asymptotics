import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFinalAssembly
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockTwoSignComparison
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreePostFourSignSplit
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreePostFourOneSignSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreePostFourTwoSignSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeThreeSignIdentitySource

/-!
# Concrete degree-three affine residual source

The post-four sign partition is now exhaustive.  High sign count uses the
uniformly cyclic signed module, one and two signs use their central binary
comparators, and the sole remaining three-sign cell is the eighteen-block
capacity-three identity source.  Together with the literal four-block
two-sign comparison this removes both project-owned endpoint parameters
from the final degree-three assembly.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

/-- Concrete post-four source in every six-, twelve-, or eighteen-block
cell with nonzero signed kernel. -/
noncomputable def degreeThreeNonzeroSignedKernelPostFourSource
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput) :
    DegreeThreeNonzeroSignedKernelPostFourResidualSource := by
  intro w U _hw basePoint block P _hres hr hs hcomponent _hK
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hr]; norm_num)
  have hsplit := degreeThreePostFour_highSign_or_lowSign
    block P hr hcomponent hs
  rcases hsplit with hhigh | hlow
  · exact degreeThreeSixOrTwelveHighSignIdentitySource block P
      hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
      hr hcomponent hhigh
  · rcases hlow with ⟨hs6, hone⟩ |
      ⟨hs12, hone | htwo⟩ |
      ⟨hs18, hone | htwo | hthree⟩
    · exact degreeThreePostFourOneSignSource block P
        hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
        hr (Or.inl hs6) hone
    · exact degreeThreePostFourOneSignSource block P
        hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
        hr (Or.inr (Or.inl hs12)) hone
    · exact degreeThreePostFourTwoSignSource block P
        hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
        hr (Or.inl hs12) hcomponent htwo
    · exact degreeThreePostFourOneSignSource block P
        hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
        hr (Or.inr (Or.inr hs18)) hone
    · exact degreeThreePostFourTwoSignSource block P
        hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
        hr (Or.inr hs18) hcomponent htwo
    · exact degreeThreeEighteenThreeSignIdentitySource block P
        hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
        hr hcomponent hs18 hthree

/-- Fully concrete degree-three residual source, depending only on the
published inputs already exposed by the surrounding affine theorem. -/
noncomputable def degreeThreeResidualSource
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
    (publishedPairs : PublishedDegreeTwoFourPairClassification) :
    PrimitiveAffineResidualDegreeSource 3 :=
  degreeThreeResidualSource_of_twoSignAndPostFour
    hKP publishedSix hZmud lit hClifford hTraceyHalf hTraceyLog
      hTraceyRefined hTraceyPerm hgen publishedPairs
      degreeThreeFourBlockTwoSignComparisonSource
      (degreeThreeNonzeroSignedKernelPostFourSource
        hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm)

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
