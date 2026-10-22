import SymmetricSubgroupAsymptotics.CFSGSufficientC3FinalPhysicalContinuation
import SymmetricSubgroupAsymptotics.CFSGSufficientPrimitiveWeights
import SymmetricSubgroupAsymptotics.CFSGSufficientPrimitiveComponentExhaustion
import SymmetricSubgroupAsymptotics.CFSGSufficientDegreeEighteenHead
import SymmetricSubgroupAsymptotics.CFSGSufficientAffineConsumerAssembly
import SymmetricSubgroupAsymptotics.Non2PreE7C3PartitionWithoutCatalogue
import SymmetricSubgroupAsymptotics.Non2PreE7RankTailNumericalClosureWithoutCatalogue
import SymmetricSubgroupAsymptotics.MarkedMomentComponentExhaustionWithoutCatalogue
import SymmetricSubgroupAsymptotics.T1FromActualAffineSources

/-! Internal actual T1 adapter for the sufficient simple-index boundary.
The final T1 assertion, physical families, normal axes, complements and all
numerical constants are unchanged. This does not install a new public input:
a final CFSG endpoint must prove the sufficient boundary from actual models.
The older published coefficient-three theorem and public facade are intact. -/

/-! Actual-consumer adapter without the composition catalogue. The original
physical families, rank caps, normal axes and numerical kernels are retained. -/
set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
open RepeatedC3TailPhysical RepeatedC3TailExtraction

noncomputable def preE7C3Covered_exponentialForwardEstimate_of_sufficient
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    (hKP : KovacsPraegerAbelianizationBound)
    (hOuter : SemisimpleOuterFactorPermutationBound)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ))) :
    OrdinaryFrontierClosure.ExponentialForwardEstimate
      preE7C3CoveredRatio :=
  OrdinaryFrontierClosure.ExponentialForwardEstimate.of_le
    (c3CompleteOrdinary_closedExponentialForwardEstimate_of_sufficient
      hChief hWeight hgen hindex published8 h18 hKP hOuter hcoarse) 0
    (fun n _ => preE7C3CoveredRatio_le_c3 n)

/-- A forward estimate for the exact complement after the regular-`C3` cut
closes the whole non-pair pre-`E7` residual. -/

noncomputable def preE7NonPair_exponentialForwardEstimate_of_noC3_of_sufficient
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    (hKP : KovacsPraegerAbelianizationBound)
    (hOuter : SemisimpleOuterFactorPermutationBound)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ)))
    (P : OrdinaryFrontierClosure.ExponentialForwardEstimate
      preE7NoPairNoC3ResidualRatio) :
    OrdinaryFrontierClosure.ExponentialForwardEstimate
      preE7NonPairResidualRatio := by
  let E := OrdinaryFrontierClosure.ExponentialForwardEstimate.add
    (preE7C3Covered_exponentialForwardEstimate_of_sufficient
      hChief hWeight hgen hindex published8 h18 hKP hOuter hcoarse) P
  exact OrdinaryFrontierClosure.ExponentialForwardEstimate.of_le E 0
    (fun n _ => by rw [preE7NonPairResidualRatio_eq_c3_partition])

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics
end


/-! Actual-consumer adapter without the composition catalogue. The original
physical families, rank caps, normal axes and numerical kernels are retained. -/
set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
open RepeatedC3TailPhysical RepeatedC3TailExtraction

theorem T1_of_preE7_numericalRankTail_residual_of_sufficient
    (lit : PreE7CharacterLiterature)
    (Residual : PreE7NumericalRankTailResidualData)
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    (hKP : KovacsPraegerAbelianizationBound)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ)))
    (hFS : FusariSpigaBinaryNormalSubgroupInput)
    (hOuter : SemisimpleOuterFactorPermutationBound) : T1 := by
  let Epacket := preE7SmallC3Packet_exponentialForwardEstimate_of_sufficient
    hChief hWeight hgen hindex published8 h18
  let Elarge := preE7NumericalRankTail_exponentialForwardEstimate lit Residual
    hLMM hcoarse hFS hOuter
  let Esum := OrdinaryFrontierClosure.ExponentialForwardEstimate.add
    Epacket Elarge
  let Eresidual := OrdinaryFrontierClosure.ExponentialForwardEstimate.of_le
    Esum 0 (fun n _ => le_of_eq
      (preE7NoPairNoC3ResidualRatio_eq_packet_add_large n))
  exact T1_of_preE7_nonPair_estimate hTracey hExceptional
    (preE7NonPair_exponentialForwardEstimate_of_noC3_of_sufficient
      hChief hWeight hgen hindex published8 h18 hKP hOuter hcoarse Eresidual)

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics
end


/-! Actual-consumer adapter without the composition catalogue. The original
physical families, rank caps, normal axes and numerical kernels are retained. -/
set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
open RepeatedC3TailPhysical RepeatedC3TailExtraction

theorem T1_of_componentExhaustion_marked_of_sufficient
    (lit : PreE7CharacterLiterature) (hgen : PermutationSubgroupGeneratorBound)
    (hM4 : GlobalMarkedC4MomentBound)
    (hTracey : TraceyBinaryFormulaInput) (hExceptional : TraceyBinaryExceptionalThreeInput)
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r/3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitiveGen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    (hKP : KovacsPraegerAbelianizationBound)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hOuter : SemisimpleOuterFactorPermutationBound)
    (D : PreE7PrimitiveComponentExhaustionData)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ)))
    (hFS : FusariSpigaBinaryNormalSubgroupInput) : T1 := by
  let source := fun w (t : PreE7NumericalTerminalIndex w) =>
    let localData := (D.classify w t).toLocalCompressionOrSourceOrYonedaTopData
    let compression := localData.toCompressionOrSourceOrYonedaTopData
    compression.toSourceOrYonedaTopData hOuter
  exact T1_of_preE7_numericalRankTail_residual_of_sufficient lit
    (fun w t => (source w t).toResidualChoiceMarked lit hgen hM4)
    hTracey hExceptional hChief hWeight hPrimitiveGen hindex published8 h18 hKP hLMM hcoarse hFS hOuter

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics
end


/-! T1 from actual primitive consumers and original-kernel affine sources.
No bounded primitive correspondence, twelve-point locator, or sixteen-point
locator is a parameter. All original normal axes and actions are retained. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
open PrimitiveAffineImprimitiveBlockTransfer

theorem T1_of_globalMarkedMoment_sufficientSimpleIndex
    (lit : PreE7CharacterLiterature) (hM4 : GlobalMarkedC4MomentBound)
    (hZmud : ZmudFaithfulCharacterTupleInput) (hcomp : PrimitiveCompositionLengthInput)
    (hodd : MarkedC4.OrdinarySubgroupUpper.PublishedTheoremOneUpper)
    (hExceptionalOrbits : TraceyCorollaryThreeTwelveRawInput)
    (hPrimitiveGen : PrimitiveNormalGeneratorInput)
    (hSimpleIndex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hSimpleGen : FiniteSimpleTwoGeneratorBound)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (publishedSix : PublishedDegreeSixThreeByTwoAffineClassification)
    (published8 : DegreeEightCanonicalCatalogue.PublishedClassification)
    (publishedThree : PublishedDegreeTwoThreePairRepresentativeClassification) : T1 := by
  have hgen := permutationSubgroupGeneratorBound_of_mcIverNeumann hMN
  have hWeight := primitiveTernaryThreeTenthsWeightBound_of_sufficient
    hcomp hSimpleIndex
  have h18 := degreeEighteenTernaryHeadBound_of_actual_small_heads_of_sufficient hSimpleIndex
    hPrimitiveGen published8
  have publishedPairs := FourPairCanonicalClassification.classification hZmud published8
  have hOuter := semisimpleOuterFactorPermutationBound_of_primitiveGenerator
    hSimpleGen.faithfulSimplePermutationGeneratorBound
  exact T1_of_componentExhaustion_marked_of_sufficient lit hgen hM4 hTraceyRefined.binaryFormula
    (traceyBinaryExceptionalThree_of_raw traceySolublePermutationFormulaRawInput_proved hExceptionalOrbits)
    (primitiveTernaryChiefWeightBound_of_sufficient hcomp hSimpleIndex)
    hWeight hPrimitiveGen hSimpleIndex published8 h18 lit.kovacsPraeger hLMM hOuter
    (primitiveComponentExhaustion_of_sufficient published8 hSimpleIndex hZmud lit hOuter
      (ActualAffineSources.consumerData_of_sufficient_actualFiniteData hSimpleIndex hZmud lit hgen
        CliffordRawRestriction.proved.toHomogeneousRestriction hcomp lit.kovacsPraeger
        hMN hTraceyRefined.affineHalf hTraceyRefined.affine
        hTraceyRefined hTraceyPerm hSimpleGen (actualPrimitiveAffineFiniteData hcomp)
        publishedSix publishedPairs publishedThree published8))
    (fusionCoarseEstimate_of_published_theorem_one hodd) fusariSpigaBinaryNormalSubgroup

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
