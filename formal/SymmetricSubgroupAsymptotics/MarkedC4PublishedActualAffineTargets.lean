import SymmetricSubgroupAsymptotics.CFSGSolubleOrbitFinal
import SymmetricSubgroupAsymptotics.MarkedC4PublishedActualTargets
import SymmetricSubgroupAsymptotics.T1FromActualAffineSources
import SymmetricSubgroupAsymptotics.BinaryExcessProposition53Proof

/-! Twelve retained inputs suffice for all approved targets. The complete
original affine sources remove the unused sixteen-point classification;
Proposition53 is supplied by its proved binary theorem. Theorem57 remains
an explicit retained input. No public facade is changed by this module. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
open PrimitiveAffineImprimitiveBlockTransfer
open MarkedC4 MarkedC4.RDTOriginalWordStructure MarkedC4.RDTNormalFInterface
open MarkedC4.OrdinaryNilpotentGeneration MarkedC4.LargeOrbitOrdinaryGeneration
open MarkedC4.SolubleContainerCount MarkedC4.SolubleContainerOrder

theorem T1_of_published_inputs_actualAffineSources
    (lit : PreE7CharacterPublishedInputs)
    (hcomp : PrimitiveCompositionLengthInput)
    (h57 : RDTExcessStructure.PublishedTheorem57Binary)
    (hodd : OrdinarySubgroupUpper.PublishedTheoremOneUpper)
    (hAG : PublishedAschbacherGuralnickSolubleGeneration)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hPrimitiveGen : PrimitiveNormalGeneratorInput)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hSimpleGen : FiniteSimpleTwoGeneratorBound)
    (hSimpleIndex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (hMN : McIverNeumannPermutationGeneratorBound)
    : T1 := by
  have published8 := S8TransitiveCanonicalCoverage.publishedClassification
  let fullLit := lit.toLiterature
  have hTraceyRefined := traceyRefinedInducedModuleInput_proved
  have hZmud := zmudFaithfulCharacterTupleInput_proved
  have rdt46 := RDTBoundedFactorEpimorphismProof.rdtTheorem46BinaryInput_proved
  have hderived := publishedDerivedNormalQuarterBinary_proved
  have h53 := publishedProposition53Binary_proved
  have h55 := publishedTheorem55Binary_of_proposition53 h53
  have publishedSix :=
    DegreeSixThreeByTwoClassificationProof.publishedDegreeSixThreeByTwoAffineClassification
  have publishedThree := DegreeSixThreePairClassificationProof.representativeClassification
  have h8 := RDTDegreeEightExceptionalProof.publishedDegreeEightExceptional
  have h62 := CFSGSolubleOrbitConsequences.publishedProposition62_proved
  have hM4 := CFSGConstructedContainersGlobal.marked_bound
    fullLit.kovacsPraeger fullLit.kovacsPraegerBinary h55 h53 h57 h8 hderived
    rdt46 hodd h62 hAG
  exact T1_of_globalMarkedMoment_actualAffineSources fullLit hM4 hZmud hcomp hodd
    hExceptionalOrbits hPrimitiveGen hSimpleIndex hLMM
    hTraceyRefined hTraceyPerm hSimpleGen hMN publishedSix published8 publishedThree

/-- The same published inputs imply all three approved asymptotic targets. -/
theorem allTargets_of_published_inputs_actualAffineSources
    (lit : PreE7CharacterPublishedInputs)
    (hcomp : PrimitiveCompositionLengthInput)
    (h57 : RDTExcessStructure.PublishedTheorem57Binary)
    (hodd : OrdinarySubgroupUpper.PublishedTheoremOneUpper)
    (hAG : PublishedAschbacherGuralnickSolubleGeneration)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hPrimitiveGen : PrimitiveNormalGeneratorInput)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hSimpleGen : FiniteSimpleTwoGeneratorBound)
    (hSimpleIndex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (hMN : McIverNeumannPermutationGeneratorBound)
    : AllTargets := by
  exact allTargets_iff_T1.mpr (T1_of_published_inputs_actualAffineSources
    lit hcomp h57
    hodd hAG hExceptionalOrbits
    hPrimitiveGen hLMM
    hTraceyPerm
    hSimpleGen
    hSimpleIndex hMN)


end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
