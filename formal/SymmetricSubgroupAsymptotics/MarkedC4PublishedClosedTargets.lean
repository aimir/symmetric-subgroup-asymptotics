import SymmetricSubgroupAsymptotics.MarkedC4PublishedDegreeTwoT1
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoClosedSourceAssembly
import SymmetricSubgroupAsymptotics.PublishedSubgroupCoarseEstimate

/-! Target composition with derived marked, head and coarse bounds.
The remaining project source frontier is explicit: a complete original
sixteen-pair residual source. All smaller pair-source branches are
constructed internally. The degree-twelve input is bare point-conjugacy
classification, with its action correspondence derived by the locator
adapter. No exhaustive sixteen-point location premise is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
open PrimitiveAffineImprimitiveBlockTransfer
open MarkedC4 MarkedC4.RDTOriginalWordStructure MarkedC4.RDTNormalFInterface
open MarkedC4.OrdinaryNilpotentGeneration MarkedC4.LargeOrbitOrdinaryGeneration
open MarkedC4.SolubleContainerCount MarkedC4.SolubleContainerOrder

/-- All smaller source branches are discharged; the actual sixteen-pair
source remains an explicit project obligation. -/
theorem T1_of_published_inputs_and_sixteenPairSource
    (lit : PreE7CharacterLiterature)
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (hClifford : CliffordHomogeneousRestriction.Input)
    (hgen : PermutationSubgroupGeneratorBound)
    (hcomp : PrimitiveCompositionLengthInput)
    (hsub : PublishedSolubleSubdirectHeight) (hseven : PublishedTheoremSeven)
    (h55 : PublishedTheorem55Binary)
    (h53 : ActualCaseIITargetStructure.PublishedProposition53Binary)
    (h57 : RDTExcessStructure.PublishedTheorem57Binary)
    (h8 : RDTDegreeEightExceptional.PublishedDegreeEightExceptional)
    (hderived : RDTDerivedNormalQuarter.PublishedDerivedNormalQuarterBinary)
    (rdt46 : RDTTheorem46BinaryInput)
    (hodd : OrdinarySubgroupUpper.PublishedTheoremOneUpper)
    (h62 : PublishedProposition62) (h86 : PublishedTheorem86Representatives)
    (hDixon : PublishedDixonOrder)
    (hAG : PublishedAschbacherGuralnickSolubleGeneration)
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (compositionCatalogue : PublishedPrimitiveCompositionCatalogueCorrespondence)
    (hDegreeNine : PublishedPrimitiveDegreeNineClassification)
    (hPrimitiveGen : PrimitiveNormalGeneratorInput)
    (strictCatalogue : PublishedPrimitiveStrictHeadCatalogueCorrespondence)
    (primitiveSix : PublishedPrimitiveDegreeSixClassification)
    (hKP : KovacsPraegerAbelianizationBound)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hHoltRoneyDougal : FaithfulSimplePermutationGeneratorBound)
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hSimpleGen : FiniteSimpleTwoGeneratorBound)
    (publishedAffine : PublishedPrimitiveAffineFiniteLiterature)
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (publishedSix : PublishedDegreeSixThreeByTwoAffineClassification)
    (published8 : DegreeEightCanonicalCatalogue.PublishedClassification)
    (published16 : PrimitiveSixteenCanonicalCatalogue.PublishedClassification)
    (publishedThree : PublishedDegreeTwoThreePairRepresentativeClassification)
    (publishedTwelve : DegreeTwelveCanonicalCatalogueLocator.PublishedClassification)
    (sixteenPair : DegreeTwoSixteenPairResidualSource)
    (hFS : FusariSpigaBinaryNormalSubgroupInput) : T1 := by
  let degreeTwo : PrimitiveAffineResidualDegreeSource 2 :=
    DegreeTwoClosedSourceAssembly.source_of_sixteenPairSource
      socle catalogue primitiveSix hZmud lit publishedThree published8 publishedTwelve sixteenPair
  exact T1_of_published_inputs_and_degreeTwoAffineSource
    lit hZmud hClifford hgen hcomp hsub hseven h55 h53 h57 h8 hderived
    rdt46 hodd h62 h86 hDixon hAG hTracey hExceptional compositionCatalogue
    hDegreeNine hPrimitiveGen strictCatalogue primitiveSix hKP hLMM
    hHoltRoneyDougal hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
    hSimpleGen publishedAffine socle catalogue hMN
    publishedSix published8 published16 degreeTwo
    (fusionCoarseEstimate_of_published_theorem_one hodd) hFS

/-- All targets conditional on the same actual sixteen-pair source. -/
theorem allTargets_of_published_inputs_and_sixteenPairSource
    (lit : PreE7CharacterLiterature)
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (hClifford : CliffordHomogeneousRestriction.Input)
    (hgen : PermutationSubgroupGeneratorBound)
    (hcomp : PrimitiveCompositionLengthInput)
    (hsub : PublishedSolubleSubdirectHeight) (hseven : PublishedTheoremSeven)
    (h55 : PublishedTheorem55Binary)
    (h53 : ActualCaseIITargetStructure.PublishedProposition53Binary)
    (h57 : RDTExcessStructure.PublishedTheorem57Binary)
    (h8 : RDTDegreeEightExceptional.PublishedDegreeEightExceptional)
    (hderived : RDTDerivedNormalQuarter.PublishedDerivedNormalQuarterBinary)
    (rdt46 : RDTTheorem46BinaryInput)
    (hodd : OrdinarySubgroupUpper.PublishedTheoremOneUpper)
    (h62 : PublishedProposition62) (h86 : PublishedTheorem86Representatives)
    (hDixon : PublishedDixonOrder)
    (hAG : PublishedAschbacherGuralnickSolubleGeneration)
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (compositionCatalogue : PublishedPrimitiveCompositionCatalogueCorrespondence)
    (hDegreeNine : PublishedPrimitiveDegreeNineClassification)
    (hPrimitiveGen : PrimitiveNormalGeneratorInput)
    (strictCatalogue : PublishedPrimitiveStrictHeadCatalogueCorrespondence)
    (primitiveSix : PublishedPrimitiveDegreeSixClassification)
    (hKP : KovacsPraegerAbelianizationBound)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hHoltRoneyDougal : FaithfulSimplePermutationGeneratorBound)
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hSimpleGen : FiniteSimpleTwoGeneratorBound)
    (publishedAffine : PublishedPrimitiveAffineFiniteLiterature)
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (publishedSix : PublishedDegreeSixThreeByTwoAffineClassification)
    (published8 : DegreeEightCanonicalCatalogue.PublishedClassification)
    (published16 : PrimitiveSixteenCanonicalCatalogue.PublishedClassification)
    (publishedThree : PublishedDegreeTwoThreePairRepresentativeClassification)
    (publishedTwelve : DegreeTwelveCanonicalCatalogueLocator.PublishedClassification)
    (sixteenPair : DegreeTwoSixteenPairResidualSource)
    (hFS : FusariSpigaBinaryNormalSubgroupInput) : AllTargets := by
  exact allTargets_iff_T1.mpr (T1_of_published_inputs_and_sixteenPairSource
    lit hZmud hClifford hgen hcomp hsub hseven h55 h53 h57 h8 hderived
    rdt46 hodd h62 h86 hDixon hAG hTracey hExceptional compositionCatalogue
    hDegreeNine hPrimitiveGen strictCatalogue primitiveSix hKP hLMM
    hHoltRoneyDougal hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
    hSimpleGen publishedAffine socle catalogue hMN
    publishedSix published8 published16 publishedThree publishedTwelve sixteenPair hFS)

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
