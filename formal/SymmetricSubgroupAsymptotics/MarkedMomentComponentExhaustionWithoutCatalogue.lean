import SymmetricSubgroupAsymptotics.MarkedMomentComponentExhaustion
import SymmetricSubgroupAsymptotics.Non2PreE7RankTailNumericalClosureWithoutCatalogue

/-! Actual-consumer adapter without the composition catalogue. The original
physical families, rank caps, normal axes and numerical kernels are retained. -/
set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
open RepeatedC3TailPhysical RepeatedC3TailExtraction

theorem T1_of_componentExhaustion_marked_without_catalogue
    (lit : PreE7CharacterLiterature) (hgen : PermutationSubgroupGeneratorBound)
    (hM4 : GlobalMarkedC4MomentBound)
    (hTracey : TraceyBinaryFormulaInput) (hExceptional : TraceyBinaryExceptionalThreeInput)
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r/3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitiveGen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
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
  exact T1_of_preE7_numericalRankTail_residual_without_catalogue lit
    (fun w t => (source w t).toResidualChoiceMarked lit hgen hM4)
    hTracey hExceptional hChief hWeight hPrimitiveGen hindex published8 h18 hKP hLMM hcoarse hFS hOuter

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics
end
