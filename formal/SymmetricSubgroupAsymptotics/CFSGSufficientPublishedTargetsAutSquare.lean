import SymmetricSubgroupAsymptotics.CFSGSufficientT1FromActualConsumersAutSquare
import SymmetricSubgroupAsymptotics.MarkedC4PublishedTenTargets
import SymmetricSubgroupAsymptotics.CFSGClassicalSufficientSimpleIndexReduction

/-! Optional sufficient-index targets with the SAME final T1/AllTargets.
Eight other published inputs remain explicit; actual AutSquare is proved internally. Global marked moments, coarse
ordinary counting, h53/h57, large-orbit generation and all finite actual
sources are supplied by existing proved factories. No public facade changes.
The CFSG variant explicitly retains its genuine nonclassical model callback;
it is not a CFSG-only theorem. -/
set_option autoImplicit false
noncomputable section
open scoped IsMulCommutative
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
open PrimitiveAffineImprimitiveBlockTransfer
open MarkedC4 MarkedC4.RDTOriginalWordStructure MarkedC4.RDTNormalFInterface
open MarkedC4.OrdinaryNilpotentGeneration MarkedC4.LargeOrbitOrdinaryGeneration
open MarkedC4.SolubleContainerCount MarkedC4.SolubleContainerOrder

theorem T1_of_eight_published_inputs_and_sufficientSimpleIndex
    (lit : PreE7CharacterPublishedInputs)
    (hcomp : PrimitiveCompositionLengthInput)
    (hAG : PublishedAschbacherGuralnickSolubleGeneration)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hPrimitiveGen : PrimitiveNormalGeneratorInput)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hSimpleIndex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds) : T1 := by
  have hodd := CFSGReduction.ordinarySubgroupUpper_of_soluble_generation hAG
  have published8 := S8TransitiveCanonicalCoverage.publishedClassification
  let fullLit := lit.toLiterature
  have hTraceyRefined := traceyRefinedInducedModuleInput_proved
  have hZmud := zmudFaithfulCharacterTupleInput_proved
  have rdt46 := RDTBoundedFactorEpimorphismProof.rdtTheorem46BinaryInput_proved
  have hderived := publishedDerivedNormalQuarterBinary_proved
  have h53 := publishedProposition53Binary_proved
  have h55 := publishedTheorem55Binary_of_proposition53 h53
  have h57 := publishedTheorem57Binary_proved
  have publishedSix :=
    DegreeSixThreeByTwoClassificationProof.publishedDegreeSixThreeByTwoAffineClassification
  have publishedThree := DegreeSixThreePairClassificationProof.representativeClassification
  have h8 := RDTDegreeEightExceptionalProof.publishedDegreeEightExceptional
  have h62 := CFSGSolubleOrbitConsequences.publishedProposition62_proved
  have hM4 := CFSGConstructedContainersGlobal.marked_bound
    fullLit.kovacsPraeger fullLit.kovacsPraegerBinary h55 h53 h57 h8 hderived
    rdt46 hodd h62 hAG
  exact T1_of_globalMarkedMoment_sufficientSimpleIndex_autSquare fullLit hM4 hZmud hcomp hodd
    hExceptionalOrbits hPrimitiveGen hSimpleIndex hLMM
    hTraceyRefined hTraceyPerm hMN publishedSix published8 publishedThree

theorem allTargets_of_eight_published_inputs_and_sufficientSimpleIndex
    (lit : PreE7CharacterPublishedInputs)
    (hcomp : PrimitiveCompositionLengthInput)
    (hAG : PublishedAschbacherGuralnickSolubleGeneration)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hPrimitiveGen : PrimitiveNormalGeneratorInput)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hSimpleIndex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds) : AllTargets :=
  allTargets_iff_T1.mpr (T1_of_eight_published_inputs_and_sufficientSimpleIndex
    lit hcomp hAG hExceptionalOrbits hPrimitiveGen hLMM hTraceyPerm hMN hSimpleIndex)

theorem T1_of_eight_published_inputs_cfsg_and_remaining_nonclassical_simpleIndex
    (lit : PreE7CharacterPublishedInputs)
    (hcomp : PrimitiveCompositionLengthInput)
    (hAG : PublishedAschbacherGuralnickSolubleGeneration)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hPrimitiveGen : PrimitiveNormalGeneratorInput)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model →
        CFSGReduction.RemainingSufficientSimpleIndexModelWithoutClassicalSuzuki i →
        CFSGReduction.ModelSufficientSimpleIndexBounds i) : T1 :=
  T1_of_eight_published_inputs_and_sufficientSimpleIndex
    lit hcomp hAG hExceptionalOrbits hPrimitiveGen hLMM hTraceyPerm hMN
    (CFSGReduction.sufficientSimpleIndexBounds_of_cfsg_and_remaining_nonclassical_models
      hCFSG remaining)

theorem allTargets_of_eight_published_inputs_cfsg_and_remaining_nonclassical_simpleIndex
    (lit : PreE7CharacterPublishedInputs)
    (hcomp : PrimitiveCompositionLengthInput)
    (hAG : PublishedAschbacherGuralnickSolubleGeneration)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hPrimitiveGen : PrimitiveNormalGeneratorInput)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model →
        CFSGReduction.RemainingSufficientSimpleIndexModelWithoutClassicalSuzuki i →
        CFSGReduction.ModelSufficientSimpleIndexBounds i) : AllTargets :=
  allTargets_iff_T1.mpr
    (T1_of_eight_published_inputs_cfsg_and_remaining_nonclassical_simpleIndex
      lit hcomp hAG hExceptionalOrbits hPrimitiveGen hLMM hTraceyPerm hMN
      hCFSG remaining)

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
