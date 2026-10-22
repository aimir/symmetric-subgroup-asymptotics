import SymmetricSubgroupAsymptotics.CFSGSufficientT1FromActualConsumersDirect
import SymmetricSubgroupAsymptotics.CFSGSufficientT1FromActualConsumersAutSquare
import SymmetricSubgroupAsymptotics.CFSGSufficientPublishedTargetsAutSquare
import SymmetricSubgroupAsymptotics.CFSGSufficientAffineConsumerOrderAssembly
import SymmetricSubgroupAsymptotics.CFSGSufficientPrimitiveWeightsOrder

/-! The same original T1/AllTargets with six other published inputs and
sufficient simple-index bounds. Actual primitive relative-three-head bounds
and actual automorphism-square bounds are proved internally. There is no
ordinary primitive normal-generator or finite-simple two-generator premise.
The optional CFSG variant retains its genuine nonclassical index callback. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
open PrimitiveAffineImprimitiveBlockTransfer

theorem T1_of_globalMarkedMoment_sufficientSimpleIndex_order
    (lit : PreE7CharacterLiterature) (hM4 : GlobalMarkedC4MomentBound)
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (hodd : MarkedC4.OrdinarySubgroupUpper.PublishedTheoremOneUpper)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    
    (hSimpleIndex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (publishedSix : PublishedDegreeSixThreeByTwoAffineClassification)
    (published8 : DegreeEightCanonicalCatalogue.PublishedClassification)
    (publishedThree : PublishedDegreeTwoThreePairRepresentativeClassification) : T1 := by
  have hgen := permutationSubgroupGeneratorBound_of_mcIverNeumann hMN
  have hWeight := primitiveTernaryThreeTenthsWeightBound_of_sufficientOrder
    hSimpleIndex
  have h18 := degreeEighteenTernaryHeadBound_of_actual_small_heads_of_sufficientHead hSimpleIndex
     published8
  have publishedPairs := FourPairCanonicalClassification.classification hZmud published8
  have hAut := finiteSimpleAutomorphismSquareBound_of_sufficient hSimpleIndex
  have hOuter := semisimpleOuterFactorPermutationBound_of_autSquare hAut
  exact T1_of_componentExhaustion_marked_of_sufficientHead lit hgen hM4 hTraceyRefined.binaryFormula
    (traceyBinaryExceptionalThree_of_raw traceySolublePermutationFormulaRawInput_proved hExceptionalOrbits)
    (primitiveTernaryChiefWeightBound_of_sufficientOrder hSimpleIndex)
    hWeight  hSimpleIndex published8 h18 lit.kovacsPraeger hLMM hOuter
    (primitiveComponentExhaustion_of_sufficient published8 hSimpleIndex hZmud lit hOuter
      (ActualAffineSources.consumerData_of_sufficient_order_of_autSquare hSimpleIndex hZmud lit hgen
        CliffordRawRestriction.proved.toHomogeneousRestriction lit.kovacsPraeger
        hMN hTraceyRefined.affineHalf hTraceyRefined.affine
        hTraceyRefined hTraceyPerm hAut
        publishedSix publishedPairs publishedThree published8))
    (fusionCoarseEstimate_of_published_theorem_one hodd) fusariSpigaBinaryNormalSubgroup

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu

set_option autoImplicit false
noncomputable section
open scoped IsMulCommutative
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
open PrimitiveAffineImprimitiveBlockTransfer
open MarkedC4 MarkedC4.RDTOriginalWordStructure MarkedC4.RDTNormalFInterface
open MarkedC4.OrdinaryNilpotentGeneration MarkedC4.LargeOrbitOrdinaryGeneration
open MarkedC4.SolubleContainerCount MarkedC4.SolubleContainerOrder

theorem T1_of_six_published_inputs_and_sufficientSimpleIndex
    (lit : PreE7CharacterPublishedInputs)
   
    (hAG : PublishedAschbacherGuralnickSolubleGeneration)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    
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
  exact T1_of_globalMarkedMoment_sufficientSimpleIndex_order fullLit hM4 hZmud hodd
    hExceptionalOrbits  hSimpleIndex hLMM
    hTraceyRefined hTraceyPerm hMN publishedSix published8 publishedThree

theorem allTargets_of_six_published_inputs_and_sufficientSimpleIndex
    (lit : PreE7CharacterPublishedInputs)
   
    (hAG : PublishedAschbacherGuralnickSolubleGeneration)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hSimpleIndex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds) : AllTargets :=
  allTargets_iff_T1.mpr (T1_of_six_published_inputs_and_sufficientSimpleIndex
    lit hAG hExceptionalOrbits  hLMM hTraceyPerm hMN hSimpleIndex)

theorem T1_of_six_published_inputs_cfsg_and_remaining_nonclassical_simpleIndex
    (lit : PreE7CharacterPublishedInputs)
   
    (hAG : PublishedAschbacherGuralnickSolubleGeneration)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model →
        CFSGReduction.RemainingSufficientSimpleIndexModelWithoutClassicalSuzuki i →
        CFSGReduction.ModelSufficientSimpleIndexBounds i) : T1 :=
  T1_of_six_published_inputs_and_sufficientSimpleIndex
    lit hAG hExceptionalOrbits  hLMM hTraceyPerm hMN
    (CFSGReduction.sufficientSimpleIndexBounds_of_cfsg_and_remaining_nonclassical_models
      hCFSG remaining)

theorem allTargets_of_six_published_inputs_cfsg_and_remaining_nonclassical_simpleIndex
    (lit : PreE7CharacterPublishedInputs)
   
    (hAG : PublishedAschbacherGuralnickSolubleGeneration)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hCFSG : CFSG.CFSGClassification)
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model →
        CFSGReduction.RemainingSufficientSimpleIndexModelWithoutClassicalSuzuki i →
        CFSGReduction.ModelSufficientSimpleIndexBounds i) : AllTargets :=
  allTargets_iff_T1.mpr
    (T1_of_six_published_inputs_cfsg_and_remaining_nonclassical_simpleIndex
      lit hAG hExceptionalOrbits  hLMM hTraceyPerm hMN
      hCFSG remaining)

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
