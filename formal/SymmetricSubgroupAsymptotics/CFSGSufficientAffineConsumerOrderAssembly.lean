import SymmetricSubgroupAsymptotics.CFSGSufficientAffineConsumerAssembly
import SymmetricSubgroupAsymptotics.PrimitiveAffineExceptionalActualAssemblyAutSquare
import SymmetricSubgroupAsymptotics.CFSGPrimitiveAffineOrderConsumer
import SymmetricSubgroupAsymptotics.CFSGAffineComponentActualExhaustion

/-! Complete actual affine assembly from original order and trace bounds.
Both primitive owners and the imprimitive component cover avoid a primitive
composition theorem. Small physical sources and original normal denominators
are unchanged. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
open PrimitiveAffineImprimitiveBlockTransfer
namespace ActualAffineSources

def consumerData_of_sufficient_order_of_autSquare
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (hgen : PermutationSubgroupGeneratorBound)
    (hClifford : CliffordHomogeneousRestriction.Input)
    (hKP : KovacsPraegerAbelianizationBound)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hAut : FiniteSimpleAutomorphismSquareBound)
    (publishedSix : PublishedDegreeSixThreeByTwoAffineClassification)
    (publishedPairs : PublishedDegreeTwoFourPairClassification)
    (publishedThree : PublishedDegreeTwoThreePairRepresentativeClassification)
    (published8 : DegreeEightCanonicalCatalogue.PublishedClassification) :
    PreE7PrimitiveAffineConsumerData := by
  let degreeTwo : PrimitiveAffineResidualDegreeSource 2 := DegreeTwoClosedSourceAssembly.SufficientActualTwelveSixteen.source
    hindex hZmud lit publishedThree published8 hMN
  let degreeThree : PrimitiveAffineResidualDegreeSource 3 := degreeThreeResidualSource hKP publishedSix hZmud lit hClifford
    hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm hgen publishedPairs
  let degreeFour : PrimitiveAffineResidualDegreeSource 4 := degreeFourActualResidualSource hZmud lit published8 hMN
    hClifford hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
  let exceptional := PrimitiveAffineImprimitiveBlockTransfer.ActualAffineSources.preE7PrimitiveAffineExceptionalCellConsumerData_of_lowDegreeSources_of_autSquare
      hZmud lit hgen hClifford hTraceyHalf hTraceyLog hTraceyRefined
      hTraceyPerm hAut degreeTwo degreeThree degreeFour
  let components := PrimitiveAffineImprimitiveBlockTransfer.ActualAffineSources.preE7PrimitiveAffineImprimitiveActualComponentSourceData_sufficientOrder hindex hTraceyHalf
      hTraceyLog hTraceyRefined hTraceyPerm exceptional
  refine { primitive := ?_, imprimitive := ?_ }
  · intro w U hw hp P
    exact match CFSGPrimitiveAffineOrderConsumer.primitiveSource hindex hgen hKP U hw hp P with
      | .inl owner => .inl owner
      | .inr source => source
  · intro w U hw basePoint block P
    exact match components.source w U hw basePoint block P with
      | .inl source => imprimitiveAffineComponentTransfer_of_autSquare hTraceyHalf hTraceyLog
          hTraceyRefined hTraceyPerm hAut block P source
      | .inr source => source

end ActualAffineSources
end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
