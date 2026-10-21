import SymmetricSubgroupAsymptotics.T1CatalogueFromFinitePackage
import SymmetricSubgroupAsymptotics.PrimitiveAffineActualConsumerAssembly
import SymmetricSubgroupAsymptotics.PrimitiveAffineActualFiniteDataConstruction
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoClosedSourceAssemblyDirectConsumers
import SymmetricSubgroupAsymptotics.PrimitiveChiefWeightWithoutCatalogue
import SymmetricSubgroupAsymptotics.DegreeEighteenHeadFromActualSmallConsumers
import SymmetricSubgroupAsymptotics.MarkedMomentComponentExhaustionWithoutCatalogue
import SymmetricSubgroupAsymptotics.PrimitiveComponentExhaustionWithoutComposition

/-! T1 from actual primitive consumers and original-kernel affine sources.
No bounded primitive correspondence, twelve-point locator, or sixteen-point
locator is a parameter. All original normal axes and actions are retained. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
open PrimitiveAffineImprimitiveBlockTransfer

theorem T1_of_globalMarkedMoment_actualAffineSources
    (lit : PreE7CharacterLiterature) (hM4 : GlobalMarkedC4MomentBound)
    (hZmud : ZmudFaithfulCharacterTupleInput) (hcomp : PrimitiveCompositionLengthInput)
    (hodd : MarkedC4.OrdinarySubgroupUpper.PublishedTheoremOneUpper)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hPrimitiveGen : PrimitiveNormalGeneratorInput)
    (hSimpleIndex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hSimpleGen : FiniteSimpleTwoGeneratorBound)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (publishedSix : PublishedDegreeSixThreeByTwoAffineClassification)
    (published8 : DegreeEightCanonicalCatalogue.PublishedClassification)
    (publishedThree : PublishedDegreeTwoThreePairRepresentativeClassification) : T1 := by
  have hgen := permutationSubgroupGeneratorBound_of_mcIverNeumann hMN
  have hWeight := primitiveTernaryThreeTenthsWeightBound_of_linear_and_simpleIndex
    hcomp hSimpleIndex
  have h18 := degreeEighteenTernaryHeadBound_of_actual_small_heads hSimpleIndex
    hPrimitiveGen published8
  have publishedPairs := FourPairCanonicalClassification.classification hZmud published8
  have hOuter := semisimpleOuterFactorPermutationBound_of_primitiveGenerator
    hSimpleGen.faithfulSimplePermutationGeneratorBound
  exact T1_of_componentExhaustion_marked_without_catalogue lit hgen hM4 hTraceyRefined.binaryFormula
    (traceyBinaryExceptionalThree_of_raw traceySolublePermutationFormulaRawInput_proved hExceptionalOrbits)
    (primitiveTernaryChiefWeightBound_without_catalogue hcomp hSimpleIndex)
    hWeight hPrimitiveGen hSimpleIndex published8 h18 lit.kovacsPraeger hLMM hOuter
    (primitiveComponentExhaustion_without_composition published8 hSimpleIndex hZmud lit hOuter
      (ActualAffineSources.consumerData_of_actualFiniteData hSimpleIndex hZmud lit hgen
        CliffordRawRestriction.proved.toHomogeneousRestriction hcomp lit.kovacsPraeger
        hMN hTraceyRefined.affineHalf hTraceyRefined.affine
        hTraceyRefined hTraceyPerm hSimpleGen (actualPrimitiveAffineFiniteData hcomp)
        publishedSix publishedPairs publishedThree published8))
    (fusionCoarseEstimate_of_published_theorem_one hodd) fusariSpigaBinaryNormalSubgroup

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
