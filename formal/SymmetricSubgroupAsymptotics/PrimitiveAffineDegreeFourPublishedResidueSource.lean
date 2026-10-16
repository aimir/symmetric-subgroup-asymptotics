import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourSixteenClosedSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourOriginalResidueAssembly
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourZeroCoreFourPointSocleSource

/-! Closed original degree-four residue construction. Every finite frame
and every four-block quotient bound is constructed from its original
normal axis; only the existing published inputs remain explicit. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

def degreeFourResidualSource_of_publishedFrames
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (published8 : DegreeEightCanonicalCatalogue.PublishedClassification)
    (published16 : PrimitiveSixteenCanonicalCatalogue.PublishedClassification)
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (hTracey : TraceySolubleOrbitInducedModuleInput)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hClifford : CliffordHomogeneousRestriction.Input)
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput) :
    PrimitiveAffineResidualDegreeSource 4 := by
  apply degreeFourResidualSource_of_originalResidues hZmud lit hTracey hMN hClifford
    hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
  · intro w U basePoint block P _ hr hD hs
    apply degreeFourFourBlockSource_of_retainedSocles block P hZmud lit hr hs
    intro N _
    exact degreeFourZeroCore_fourPoint_quotientSocle_le_two block P hMN hr hs hD N
  · exact degreeFourZeroCoreEightFrameBounds_of_published published8
  · exact degreeFourZeroCoreSixteenFrameBounds_of_published published8 published16 socle
      hTracey hMN hClifford hTraceyPerm

end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics
