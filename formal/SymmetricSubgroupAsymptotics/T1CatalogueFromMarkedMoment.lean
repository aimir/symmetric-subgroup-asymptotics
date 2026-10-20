import SymmetricSubgroupAsymptotics.MarkedC4PublishedClosedTargets
import SymmetricSubgroupAsymptotics.DegreeSixteenCompleteGeometricSource
import SymmetricSubgroupAsymptotics.CliffordActualRetainedConstituent
import SymmetricSubgroupAsymptotics.CliffordRestriction
import SymmetricSubgroupAsymptotics.BinaryNormalSubgroupBound
import SymmetricSubgroupAsymptotics.TraceyRefinedInputConsequences
import SymmetricSubgroupAsymptotics.FaithfulSimpleGeneratorFromTwoGeneration
import SymmetricSubgroupAsymptotics.PrimitiveDegreeNineFromCompositionCatalogue
import SymmetricSubgroupAsymptotics.PrimitiveDegreeSixCatalogueClassification
import SymmetricSubgroupAsymptotics.TraceyPermutationFormulaConsequences
import SymmetricSubgroupAsymptotics.TraceySolublePermutationConsequences
import SymmetricSubgroupAsymptotics.PermutationGeneratorBoundFromMcIverNeumann
import SymmetricSubgroupAsymptotics.TraceyExceptionalThreeFromRaw

/-! Final catalogue assembly is independent of the particular route used
to prove the global marked moment. This isolates the reusable mathematical
endpoint from stronger historical inputs to that moment. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu

open PrimitiveAffineImprimitiveBlockTransfer

theorem T1_of_globalMarkedMoment_and_catalogues
    (lit : PreE7CharacterLiterature)
    (hM4 : GlobalMarkedC4MomentBound)
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (hcomp : PrimitiveCompositionLengthInput)
    (hodd : MarkedC4.OrdinarySubgroupUpper.PublishedTheoremOneUpper)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (compositionCatalogue : PublishedPrimitiveCompositionCatalogueCorrespondence)
    (hPrimitiveGen : PrimitiveNormalGeneratorInput)
    (strictCatalogue : PublishedPrimitiveStrictHeadCatalogueCorrespondence)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hSimpleGen : FiniteSimpleTwoGeneratorBound)
    (publishedAffine : PublishedPrimitiveAffineFiniteLiterature)
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence)
    (hTraceySoluble : TraceySolubleOrbitInducedModuleInput)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (publishedSix : PublishedDegreeSixThreeByTwoAffineClassification)
    (published8 : DegreeEightCanonicalCatalogue.PublishedClassification)
    (published16 : PrimitiveSixteenCanonicalCatalogue.PublishedClassification)
    (publishedThree : PublishedDegreeTwoThreePairRepresentativeClassification)
    (publishedTwelve : DegreeTwelveCanonicalCatalogueLocator.PublishedClassification) : T1 := by
  have hgen := permutationSubgroupGeneratorBound_of_mcIverNeumann hMN
  have primitiveSix :=
    PrimitiveDegreeSixCatalogueClassification.publishedPrimitiveDegreeSixClassification_of_compositionCatalogue
      compositionCatalogue
  have hDegreeNine := primitiveDegreeNineClassification_of_compositionCatalogue compositionCatalogue
  have hWeight := primitiveTernaryThreeTenthsWeightBound_of_published hcomp compositionCatalogue
  have hPrimitive := primitiveTernaryStrictHeadBound_of_published hPrimitiveGen strictCatalogue
  have h18 := degreeEighteenTernaryHeadBound_of_published strictCatalogue primitiveSix hPrimitive
  have publishedPairs := FourPairCanonicalClassification.classification hZmud published8
  let degreeTwo : PrimitiveAffineResidualDegreeSource 2 :=
    DegreeTwoClosedSourceAssembly.source_of_sixteenPairSource
      socle catalogue primitiveSix hZmud lit publishedThree published8 publishedTwelve
      (DegreeSixteenCompleteGeometricSource.residualSource
        published8 published16 socle hMN hZmud lit)
  exact T1_of_catalogueExhaustion_marked lit hgen hM4 hTraceyRefined.binaryFormula
    (traceyBinaryExceptionalThree_of_raw hTraceySoluble.permutationFormulaRaw hExceptionalOrbits)
    (primitiveTernaryChiefWeightBound_of_published hWeight hDegreeNine)
    hWeight hPrimitive h18 lit.kovacsPraeger hLMM
    (semisimpleOuterFactorPermutationBound_of_primitiveGenerator
      hSimpleGen.faithfulSimplePermutationGeneratorBound)
    (preE7PrimitiveCatalogueExhaustionData
      (preE7PrimitiveCatalogueClassificationInput_of_published socle catalogue)
      (preE7PrimitiveAffineConsumerData_of_degreeTwoSource hZmud lit hgen
        CliffordRawRestriction.proved.toHomogeneousRestriction hcomp lit.kovacsPraeger
        hTraceySoluble hMN hTraceyRefined.affineHalf hTraceyRefined.affine
        hTraceyRefined hTraceyPerm hSimpleGen publishedAffine publishedSix
        publishedPairs published8 published16 socle degreeTwo))
    (fusionCoarseEstimate_of_published_theorem_one hodd) fusariSpigaBinaryNormalSubgroup

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu

end
