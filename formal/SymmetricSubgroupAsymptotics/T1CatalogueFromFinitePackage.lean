import SymmetricSubgroupAsymptotics.MarkedMomentComponentExhaustion
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoClosedSourceAssemblyBoundedCatalogueReduced
import SymmetricSubgroupAsymptotics.PrimitiveStrictHeadFromCompositionAndSimpleIndex
import SymmetricSubgroupAsymptotics.DegreeEighteenHeadFromComposition
import SymmetricSubgroupAsymptotics.TraceySolublePermutationFormulaProof
import SymmetricSubgroupAsymptotics.MarkedC4PublishedClosedTargets
import SymmetricSubgroupAsymptotics.PrimitiveAffineFinitePackageConsumerBinarySmallReduced
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

theorem T1_of_globalMarkedMoment_and_finitePackage
    (lit : PreE7CharacterLiterature)
    (hM4 : GlobalMarkedC4MomentBound)
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (hcomp : PrimitiveCompositionLengthInput)
    (hodd : MarkedC4.OrdinarySubgroupUpper.PublishedTheoremOneUpper)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (compositionCatalogue : PublishedPrimitiveCompositionCatalogueCorrespondence)
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
    (publishedTwelve : DegreeTwelveCanonicalCatalogueLocator.PublishedClassification) : T1 := by
  have hgen := permutationSubgroupGeneratorBound_of_mcIverNeumann hMN
  have primitiveSix :=
    PrimitiveDegreeSixCatalogueClassification.publishedPrimitiveDegreeSixClassification_of_compositionCatalogue
      compositionCatalogue
  have hDegreeNine := primitiveDegreeNineClassification_of_compositionCatalogue compositionCatalogue
  have hWeight := primitiveTernaryThreeTenthsWeightBound_of_published hcomp compositionCatalogue
  have hPrimitive := primitiveTernaryStrictHeadBound_of_composition_and_simpleIndex
    hPrimitiveGen compositionCatalogue hSimpleIndex
  have h18 := degreeEighteenTernaryHeadBound_from_composition
    compositionCatalogue hSimpleIndex primitiveSix hPrimitive
  have publishedPairs := FourPairCanonicalClassification.classification hZmud published8
  let degreeTwo : PrimitiveAffineResidualDegreeSource 2 :=
    DegreeTwoClosedSourceAssembly.BoundedCatalogueReduced.source_of_sixteenPairSource
      socle (PrimitiveSixTwelveNormalConsumerFacts.of_composition compositionCatalogue hSimpleIndex) primitiveSix hZmud lit publishedThree published8 publishedTwelve
      (DegreeSixteenCompleteGeometricSource.residualSource
        published8 published16 socle hMN hZmud lit)
  have hOuter := semisimpleOuterFactorPermutationBound_of_primitiveGenerator
    hSimpleGen.faithfulSimplePermutationGeneratorBound
  exact T1_of_componentExhaustion_marked lit hgen hM4 hTraceyRefined.binaryFormula
    (traceyBinaryExceptionalThree_of_raw traceySolublePermutationFormulaRawInput_proved hExceptionalOrbits)
    (primitiveTernaryChiefWeightBound_of_published hWeight hDegreeNine)
    hWeight hPrimitive h18 lit.kovacsPraeger hLMM
    hOuter
    (primitiveComponentExhaustion_of_composition_and_margin
      compositionCatalogue published8 published16 hSimpleIndex hOuter
      (BinarySmallReduced.preE7PrimitiveAffineConsumerData_of_finitePackage hZmud lit hgen
        CliffordRawRestriction.proved.toHomogeneousRestriction hcomp lit.kovacsPraeger
        hMN hTraceyRefined.affineHalf hTraceyRefined.affine
        hTraceyRefined hTraceyPerm hSimpleGen publishedSmall publishedFinite publishedSix
        publishedPairs published8 published16 socle degreeTwo))
    (fusionCoarseEstimate_of_published_theorem_one hodd) fusariSpigaBinaryNormalSubgroup

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu

end
