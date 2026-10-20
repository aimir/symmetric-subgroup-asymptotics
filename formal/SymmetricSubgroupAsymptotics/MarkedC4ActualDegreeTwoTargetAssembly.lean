import SymmetricSubgroupAsymptotics.MarkedC4ActualCatalogueT1
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoConditionalTargetAssembly

/-! Conditional final T1 facade with the marked moment derived from ordinary
literature. Only the existing explicit degree-two source and certificate-valued
catalogue boundary remain project-owned; this is not an unconditional T1. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
open PrimitiveAffineImprimitiveBlockTransfer
open MarkedC4 MarkedC4.RDTOriginalWordStructure MarkedC4.RDTNormalFInterface
open MarkedC4.OrdinaryNilpotentGeneration MarkedC4.LargeOrbitOrdinaryGeneration
open MarkedC4.SolubleContainerCount MarkedC4.SolubleContainerOrder

/-- Conditional composition; this does not discharge the explicit premises. -/
theorem T1_of_ordinary_inputs_and_degreeTwoAffineSource
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
    (hFS : FusariSpigaBinaryNormalSubgroupInput) : T1 := by
  let hM4 := MarkedC4.ActualGlobalMarkedMoment.marked_bound hsub hseven hKP
    lit.kovacsPraegerBinary h55 h53 h57 h8 hderived rdt46 hodd h62 h86 hDixon hAG
  exact T1_of_catalogueExhaustion_marked lit hgen hM4 hTracey hExceptional
    (primitiveTernaryChiefWeightBound_of_published hWeight hDegreeNine)
    hWeight hPrimitive h18 hKP hLMM
    (semisimpleOuterFactorPermutationBound_of_primitiveGenerator hHoltRoneyDougal)
    (preE7PrimitiveCatalogueExhaustionData
      (preE7PrimitiveCatalogueClassificationInput_of_published socle catalogue)
      (preE7PrimitiveAffineConsumerData_of_degreeTwoSource hZmud lit hgen
        hClifford hcomp hKP hTraceySoluble hMN hTraceyHalf hTraceyLog
        hTraceyRefined hTraceyPerm hSimpleGen publishedAffine publishedSix
        publishedPairs published8 published16 socle degreeTwo))
    hcoarse hFS

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
