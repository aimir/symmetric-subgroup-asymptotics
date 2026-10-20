import SymmetricSubgroupAsymptotics.MarkedC4ActualCatalogueT1
import SymmetricSubgroupAsymptotics.PrimitiveComponentMarginExhaustion

/-! The existing global marked-moment endpoint accepts primitive-component
exhaustion directly. This only removes an unused intermediate catalogue
representation; every source, normal quotient weight and residual choice is
passed through the same checked conversion. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu

theorem T1_of_componentExhaustion_marked
    (lit : PreE7CharacterLiterature) (hgen : PermutationSubgroupGeneratorBound)
    (hM4 : GlobalMarkedC4MomentBound)
    (hTracey : TraceyBinaryFormulaInput) (hExceptional : TraceyBinaryExceptionalThreeInput)
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r/3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound) (h18 : DegreeEighteenTernaryHeadBound)
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
  exact T1_of_preE7_numericalRankTail_residual lit
    (fun w t => (source w t).toResidualChoiceMarked lit hgen hM4)
    hTracey hExceptional hChief hWeight hPrimitive h18 hKP hLMM hcoarse hFS hOuter

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
