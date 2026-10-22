import SymmetricSubgroupAsymptotics.CFSGSufficientT1FromActualConsumers
import SymmetricSubgroupAsymptotics.CFSGSufficientAffineConsumerAssemblyAutSquare
import SymmetricSubgroupAsymptotics.SemisimpleOuterFactorAutSquare

/-! The same T1 constructor with no simple-generation input. AutSquare is
 proved internally from the supplied sufficient simple-index theorem. -/
/-! T1 from actual primitive consumers and original-kernel affine sources.
No bounded primitive correspondence, twelve-point locator, or sixteen-point
locator is a parameter. All original normal axes and actions are retained. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
open PrimitiveAffineImprimitiveBlockTransfer

theorem T1_of_globalMarkedMoment_sufficientSimpleIndex_autSquare
    (lit : PreE7CharacterLiterature) (hM4 : GlobalMarkedC4MomentBound)
    (hZmud : ZmudFaithfulCharacterTupleInput) (hcomp : PrimitiveCompositionLengthInput)
    (hodd : MarkedC4.OrdinarySubgroupUpper.PublishedTheoremOneUpper)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hPrimitiveGen : PrimitiveNormalGeneratorInput)
    (hSimpleIndex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (publishedSix : PublishedDegreeSixThreeByTwoAffineClassification)
    (published8 : DegreeEightCanonicalCatalogue.PublishedClassification)
    (publishedThree : PublishedDegreeTwoThreePairRepresentativeClassification) : T1 := by
  have hgen := permutationSubgroupGeneratorBound_of_mcIverNeumann hMN
  have hWeight := primitiveTernaryThreeTenthsWeightBound_of_sufficient
    hcomp hSimpleIndex
  have h18 := degreeEighteenTernaryHeadBound_of_actual_small_heads_of_sufficient hSimpleIndex
    hPrimitiveGen published8
  have publishedPairs := FourPairCanonicalClassification.classification hZmud published8
  have hAut := finiteSimpleAutomorphismSquareBound_of_sufficient hSimpleIndex
  have hOuter := semisimpleOuterFactorPermutationBound_of_autSquare hAut
  exact T1_of_componentExhaustion_marked_of_sufficient lit hgen hM4 hTraceyRefined.binaryFormula
    (traceyBinaryExceptionalThree_of_raw traceySolublePermutationFormulaRawInput_proved hExceptionalOrbits)
    (primitiveTernaryChiefWeightBound_of_sufficient hcomp hSimpleIndex)
    hWeight hPrimitiveGen hSimpleIndex published8 h18 lit.kovacsPraeger hLMM hOuter
    (primitiveComponentExhaustion_of_sufficient published8 hSimpleIndex hZmud lit hOuter
      (ActualAffineSources.consumerData_of_sufficient_actualFiniteData_of_autSquare hSimpleIndex hZmud lit hgen
        CliffordRawRestriction.proved.toHomogeneousRestriction hcomp lit.kovacsPraeger
        hMN hTraceyRefined.affineHalf hTraceyRefined.affine
        hTraceyRefined hTraceyPerm hAut (actualPrimitiveAffineFiniteData hcomp)
        publishedSix publishedPairs publishedThree published8))
    (fusionCoarseEstimate_of_published_theorem_one hodd) fusariSpigaBinaryNormalSubgroup

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
