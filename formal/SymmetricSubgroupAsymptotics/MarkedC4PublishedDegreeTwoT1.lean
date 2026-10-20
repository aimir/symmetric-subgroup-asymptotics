import SymmetricSubgroupAsymptotics.MarkedC4ActualDegreeTwoTargetAssembly
import SymmetricSubgroupAsymptotics.PrimitiveTernaryThreeTenthsPublished
import SymmetricSubgroupAsymptotics.PrimitiveTernaryStrictHeadPublished
import SymmetricSubgroupAsymptotics.DegreeEighteenTernaryHeadProof
import SymmetricSubgroupAsymptotics.FourPairCanonicalClassification

/-! Final composition boundary with the project-owned primitive weight,
strict-head, degree-eighteen and marked-C4 theorems derived, rather than
assumed. The actual degree-two residual source remains an explicit project
obligation. Bounded catalogue correspondences expose ordinary published
classification data, not source or relative-character conclusions. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
open PrimitiveAffineImprimitiveBlockTransfer
open MarkedC4 MarkedC4.RDTOriginalWordStructure MarkedC4.RDTNormalFInterface
open MarkedC4.OrdinaryNilpotentGeneration MarkedC4.LargeOrbitOrdinaryGeneration
open MarkedC4.SolubleContainerCount MarkedC4.SolubleContainerOrder

/-- This theorem remains conditional on the actual degree-two source. All
derived numerical/marked inputs and certificate-valued four-pair classification are discharged by checked theorems. -/
theorem T1_of_published_inputs_and_degreeTwoAffineSource
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
    (hTraceySoluble : TraceySolubleOrbitInducedModuleInput)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (publishedSix : PublishedDegreeSixThreeByTwoAffineClassification)
    (published8 : DegreeEightCanonicalCatalogue.PublishedClassification)
    (published16 : PrimitiveSixteenCanonicalCatalogue.PublishedClassification)
    (degreeTwo : PrimitiveAffineResidualDegreeSource 2)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ)))
    (hFS : FusariSpigaBinaryNormalSubgroupInput) : T1 := by
  have publishedPairs := FourPairCanonicalClassification.classification hZmud published8
  have hWeight := primitiveTernaryThreeTenthsWeightBound_of_published
    hcomp compositionCatalogue
  have hPrimitive := primitiveTernaryStrictHeadBound_of_published
    hPrimitiveGen strictCatalogue
  have h18 := degreeEighteenTernaryHeadBound_of_published
    strictCatalogue primitiveSix hPrimitive
  exact T1_of_ordinary_inputs_and_degreeTwoAffineSource lit hZmud hClifford
    hgen hcomp hsub hseven h55 h53 h57 h8 hderived rdt46 hodd h62 h86
    hDixon hAG hTracey hExceptional hWeight hDegreeNine hPrimitive h18 hKP
    hLMM hHoltRoneyDougal hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
    hSimpleGen publishedAffine socle catalogue hTraceySoluble hMN
    publishedSix publishedPairs published8 published16 degreeTwo hcoarse hFS

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
