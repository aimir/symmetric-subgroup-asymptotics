import SymmetricSubgroupAsymptotics.MarkedC4ActualEarlierNumerical
import SymmetricSubgroupAsymptotics.PrimitiveCatalogueClassificationAssembly

/-! Conditional T1 catalogue composition using the proved marked moment,
without a project-owned RDT reduction input. The literal primitive catalogue
and affine-source construction remain explicit, unchanged obligations. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu

def PreE7RankTailSourceOrYonedaTopData.toResidualChoiceMarked
    (lit : PreE7CharacterLiterature) (hgen : PermutationSubgroupGeneratorBound)
    (hM4 : GlobalMarkedC4MomentBound) {w : ℕ} {U : PreE7NonPairActionClass w}
    (D : PreE7RankTailSourceOrYonedaTopData w U) :
    PreE7NumericalRankTailResidualChoice w U :=
  match D with
  | .inl source => .emptyOfActionOwner U (source.toActionOwnerMarked lit hgen hM4)
  | .inr (.inl cells) => .ofNumericalResidualJointTopCells cells.toJointTopCellSourceData
  | .inr (.inr residual) => residual

theorem T1_of_catalogueExhaustion_marked
    (lit : PreE7CharacterLiterature) (hgen : PermutationSubgroupGeneratorBound)
    (hM4 : GlobalMarkedC4MomentBound)
    (hTracey : TraceyBinaryFormulaInput) (hExceptional : TraceyBinaryExceptionalThreeInput)
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r/3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound) (h18 : DegreeEighteenTernaryHeadBound)
    (hKP : KovacsPraegerAbelianizationBound)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hOuter : SemisimpleOuterFactorPermutationBound)
    (D : PreE7PrimitiveCatalogueExhaustionData)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ)))
    (hFS : FusariSpigaBinaryNormalSubgroupInput) : T1 := by
  let E := D.toBoundedIndexExhaustion.toOuterLogExhaustion.toPrimitiveComponentExhaustion
  let source := fun w (t : PreE7NumericalTerminalIndex w) =>
    let localData := (E.classify w t).toLocalCompressionOrSourceOrYonedaTopData
    let compression := localData.toCompressionOrSourceOrYonedaTopData
    compression.toSourceOrYonedaTopData hOuter
  exact T1_of_preE7_numericalRankTail_residual lit
    (fun w t => (source w t).toResidualChoiceMarked lit hgen hM4)
    hTracey hExceptional hChief hWeight hPrimitive h18 hKP hLMM hcoarse hFS hOuter

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
