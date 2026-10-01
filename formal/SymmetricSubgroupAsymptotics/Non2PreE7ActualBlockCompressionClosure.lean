import SymmetricSubgroupAsymptotics.Non2PreE7ActualBlockCompression
import SymmetricSubgroupAsymptotics.Non2PreE7SemisimpleCompressionClosure

/-!
# T1 from local exact-block compression

The structural compression alternative is now stated entirely on an actual
minimal block.  Its global wreath embedding, full-component property,
semisimple normal intersection and faithful quotient action are theorems.
Only the local primitive component quotient remains in the certificate.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- Exact structural obligation after the actual block-system construction:
either a local compression certificate on one original minimal block, or an
already integrated source/Yoneda-top certificate. -/
abbrev PreE7ActualBlockCompressionOrSourceOrYonedaTopData
    (w : ℕ) (U : PreE7NonPairActionClass w) :=
  PreE7OriginalMinimalBlockCompressionData w U ⊕
    PreE7RankTailSourceOrYonedaTopData w U

/-- Actual block data construct the global compression witness; the other
branch is unchanged. -/
noncomputable def
    PreE7ActualBlockCompressionOrSourceOrYonedaTopData.toCompressionOrSourceOrYonedaTopData
    {w : ℕ} {U : PreE7NonPairActionClass w}
    (D : PreE7ActualBlockCompressionOrSourceOrYonedaTopData w U) :
    PreE7CompressionOrSourceOrYonedaTopData w U :=
  match D with
  | .inl block => .inl block.toSemisimpleCompressionData
  | .inr source => .inr source

/-- T1 with the exact global block lifting discharged. -/
theorem T1_of_preE7_actualBlockCompression_or_sourceOrYonedaTop_data
    (lit : PreE7CharacterLiterature)
    (hgen : PermutationSubgroupGeneratorBound)
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (hKP : KovacsPraegerAbelianizationBound)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hOuter : SemisimpleOuterFactorPermutationBound)
    (D : ∀ w (U : PreE7NonPairActionClass w),
      PreE7ActualBlockCompressionOrSourceOrYonedaTopData w U)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ)))
    (hFS : FusariSpigaBinaryNormalSubgroupInput) : T1 :=
  T1_of_preE7_semisimpleCompression_or_sourceOrYonedaTop_data
    lit hgen hTracey hExceptional hChief hWeight hPrimitive h18 hKP hLMM
    hOuter
    (fun w U => (D w U).toCompressionOrSourceOrYonedaTopData)
    hcoarse hFS

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
