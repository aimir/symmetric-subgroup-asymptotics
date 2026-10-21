import SymmetricSubgroupAsymptotics.T1CatalogueFromFinitePackage
import SymmetricSubgroupAsymptotics.DegreeTwoSourceWithoutTwelveCatalogue
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoClosedSourceAssemblyDirectConsumers
import SymmetricSubgroupAsymptotics.PrimitiveChiefWeightWithoutCatalogue
import SymmetricSubgroupAsymptotics.DegreeEighteenHeadFromActualSmallConsumers
import SymmetricSubgroupAsymptotics.MarkedMomentComponentExhaustionWithoutCatalogue
import SymmetricSubgroupAsymptotics.PrimitiveComponentExhaustionWithoutComposition

/-! Assembly from proved actual primitive consumers. The stronger unused
C336, degree12 correspondence and global strict-head statements are not asserted. The
complete physical C3 estimate pays the actual primitive10/12 sector. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
open PrimitiveAffineImprimitiveBlockTransfer

theorem T1_of_globalMarkedMoment_actualPrimitiveAndTwelveConsumers
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
    (publishedSmall : BinaryAffineSmallCatalogueData)
    (publishedFinite : PublishedPrimitiveAffineFiniteInput)
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (publishedSix : PublishedDegreeSixThreeByTwoAffineClassification)
    (published8 : DegreeEightCanonicalCatalogue.PublishedClassification)
    (published16 : PrimitiveSixteenCanonicalCatalogue.PublishedClassification)
    (publishedThree : PublishedDegreeTwoThreePairRepresentativeClassification)
 : T1 := by
  have hgen := permutationSubgroupGeneratorBound_of_mcIverNeumann hMN
  have hWeight := primitiveTernaryThreeTenthsWeightBound_of_linear_and_simpleIndex
    hcomp hSimpleIndex
  have h18 := degreeEighteenTernaryHeadBound_of_actual_small_heads hSimpleIndex
    hPrimitiveGen published8
  have publishedPairs := FourPairCanonicalClassification.classification hZmud published8
  let degreeTwo : PrimitiveAffineResidualDegreeSource 2 :=
    DegreeTwoClosedSourceAssembly.ActualTwelve.source_of_sixteenPairSource
      hSimpleIndex hZmud lit publishedThree published8
      (DegreeSixteenCompleteGeometricSource.residualSource
        published8 published16 socle hMN hZmud lit)
  have hOuter := semisimpleOuterFactorPermutationBound_of_primitiveGenerator
    hSimpleGen.faithfulSimplePermutationGeneratorBound
  exact T1_of_componentExhaustion_marked_without_catalogue lit hgen hM4 hTraceyRefined.binaryFormula
    (traceyBinaryExceptionalThree_of_raw traceySolublePermutationFormulaRawInput_proved hExceptionalOrbits)
    (primitiveTernaryChiefWeightBound_without_catalogue hcomp hSimpleIndex)
    hWeight hPrimitiveGen hSimpleIndex published8 h18 lit.kovacsPraeger hLMM hOuter
    (primitiveComponentExhaustion_without_composition published8 hSimpleIndex hZmud lit hOuter
      (BinarySmallReduced.preE7PrimitiveAffineConsumerData_of_finitePackage hZmud lit hgen
        CliffordRawRestriction.proved.toHomogeneousRestriction hcomp lit.kovacsPraeger
        hMN hTraceyRefined.affineHalf hTraceyRefined.affine
        hTraceyRefined hTraceyPerm hSimpleGen publishedSmall publishedFinite publishedSix
        publishedPairs published8 published16 socle degreeTwo))
    (fusionCoarseEstimate_of_published_theorem_one hodd) fusariSpigaBinaryNormalSubgroup

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
