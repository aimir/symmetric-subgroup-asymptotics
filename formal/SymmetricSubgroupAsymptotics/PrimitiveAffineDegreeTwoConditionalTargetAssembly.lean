import SymmetricSubgroupAsymptotics.PrimitiveAffineLowDegreeConsumerAssembly
import SymmetricSubgroupAsymptotics.ElementaryBenchmarkEstimates

/-! Conditional T1 and AllTargets composition with only degree two left
as a low-degree source argument. Every other input remains explicit.
In particular the four-pair row correspondence is retained as its actual
certificate-valued interface; its construction is not asserted here. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
open PrimitiveAffineImprimitiveBlockTransfer

/-- Conditional composition; this does not discharge the explicit premises. -/
theorem T1_of_explicit_inputs_and_degreeTwoAffineSource
    (lit : PreE7CharacterLiterature)
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (hClifford : CliffordHomogeneousRestriction.Input)
    (hgen : PermutationSubgroupGeneratorBound)
    (hcomp : PrimitiveCompositionLengthInput)
    (hRDT : MarkedC4.RDTMarkedC4ReductionInput)
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hDegreeNine : PublishedPrimitiveDegreeNineClassification)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
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
    (hTraceySoluble : TraceySolubleOrbitInducedModuleInput)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (publishedSix : PublishedDegreeSixThreeByTwoAffineClassification)
    (publishedPairs : PublishedDegreeTwoFourPairClassification)
    (published8 : DegreeEightCanonicalCatalogue.PublishedClassification)
    (published16 : PrimitiveSixteenCanonicalCatalogue.PublishedClassification)
    (degreeTwo : PrimitiveAffineResidualDegreeSource 2)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ)))
    (hFS : FusariSpigaBinaryNormalSubgroupInput) : T1 :=
  T1_of_preE7_primitiveCatalogueClassification lit hgen hRDT hTracey
    hExceptional hWeight hDegreeNine hPrimitive h18 hKP hLMM
    hHoltRoneyDougal
    (preE7PrimitiveCatalogueClassificationInput_of_published socle catalogue)
    (preE7PrimitiveAffineConsumerData_of_degreeTwoSource hZmud lit hgen
      hClifford hcomp hKP hTraceySoluble hMN hTraceyHalf hTraceyLog
      hTraceyRefined hTraceyPerm hSimpleGen publishedAffine publishedSix
      publishedPairs published8 published16 socle degreeTwo)
    hcoarse hFS

/-- The existing T1 equivalence supplies all targets under the same premises. -/
theorem allTargets_of_explicit_inputs_and_degreeTwoAffineSource
    (lit : PreE7CharacterLiterature)
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (hClifford : CliffordHomogeneousRestriction.Input)
    (hgen : PermutationSubgroupGeneratorBound)
    (hcomp : PrimitiveCompositionLengthInput)
    (hRDT : MarkedC4.RDTMarkedC4ReductionInput)
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hDegreeNine : PublishedPrimitiveDegreeNineClassification)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
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
    (hTraceySoluble : TraceySolubleOrbitInducedModuleInput)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (publishedSix : PublishedDegreeSixThreeByTwoAffineClassification)
    (publishedPairs : PublishedDegreeTwoFourPairClassification)
    (published8 : DegreeEightCanonicalCatalogue.PublishedClassification)
    (published16 : PrimitiveSixteenCanonicalCatalogue.PublishedClassification)
    (degreeTwo : PrimitiveAffineResidualDegreeSource 2)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ)))
    (hFS : FusariSpigaBinaryNormalSubgroupInput) : AllTargets :=
  allTargets_iff_T1.mpr
    (T1_of_explicit_inputs_and_degreeTwoAffineSource
      lit hZmud hClifford hgen hcomp
      hRDT hTracey hExceptional hWeight hDegreeNine
      hPrimitive h18 hKP hLMM hHoltRoneyDougal
      hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm hSimpleGen
      publishedAffine socle catalogue hTraceySoluble hMN
      publishedSix publishedPairs published8 published16 degreeTwo
      hcoarse hFS )

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics
