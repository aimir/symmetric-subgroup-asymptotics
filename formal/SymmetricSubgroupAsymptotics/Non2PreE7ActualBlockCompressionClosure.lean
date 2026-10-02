import SymmetricSubgroupAsymptotics.Non2PreE7ActualBlockCompression
import SymmetricSubgroupAsymptotics.Non2PreE7LocalSemisimpleCompression
import SymmetricSubgroupAsymptotics.Non2PreE7SemisimpleCompressionClosure
import SymmetricSubgroupAsymptotics.PrimitiveSemisimpleCompressionProfile

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
    (hRDT : MarkedC4.RDTMarkedC4ReductionInput)
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (hKP : KovacsPraegerAbelianizationBound)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hOuter : SemisimpleOuterFactorPermutationBound)
    (D : ∀ w (t : PreE7NumericalTerminalIndex w),
      PreE7ActualBlockCompressionOrSourceOrYonedaTopData w t.action)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ)))
    (hFS : FusariSpigaBinaryNormalSubgroupInput) : T1 :=
  T1_of_preE7_semisimpleCompression_or_sourceOrYonedaTop_data
    lit hgen hRDT hTracey hExceptional hChief hWeight hPrimitive h18 hKP hLMM
    hOuter
    (fun w t => (D w t).toCompressionOrSourceOrYonedaTopData)
    hcoarse hFS

/-- Final local structural alternatives.  Primitive actions use their own
local quotient; imprimitive actions use one actual minimal block; all affine,
soluble and exceptional branches may instead supply an already integrated
source or the terminal Yoneda family. -/
inductive PreE7LocalCompressionOrSourceOrYonedaTopData
    (w : ℕ) (U : PreE7NonPairActionClass w) : Type 1 where
  | primitive (data : PreE7PrimitiveLocalCompressionData w U)
  | imprimitive (data : PreE7OriginalMinimalBlockLocalCompressionData w U)
  | source (data : PreE7RankTailSourceOrYonedaTopData w U)

/-- Every local structural alternative enters the already checked global
compression/source frontier. -/
noncomputable def
    PreE7LocalCompressionOrSourceOrYonedaTopData.toCompressionOrSourceOrYonedaTopData
    {w : ℕ} {U : PreE7NonPairActionClass w}
    (D : PreE7LocalCompressionOrSourceOrYonedaTopData w U) :
    PreE7CompressionOrSourceOrYonedaTopData w U :=
  match D with
  | .primitive data => .inl data.toSemisimpleCompressionData
  | .imprimitive data => .inl data.toSemisimpleCompressionData
  | .source data => .inr data

/-- T1 after all global compression and exact-block arguments have been
discharged.  The remaining exhaustion theorem is local on a primitive action
or an actual primitive block component. -/
theorem T1_of_preE7_localCompression_or_sourceOrYonedaTop_data
    (lit : PreE7CharacterLiterature)
    (hgen : PermutationSubgroupGeneratorBound)
    (hRDT : MarkedC4.RDTMarkedC4ReductionInput)
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (hKP : KovacsPraegerAbelianizationBound)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hOuter : SemisimpleOuterFactorPermutationBound)
    (D : ∀ w (t : PreE7NumericalTerminalIndex w),
      PreE7LocalCompressionOrSourceOrYonedaTopData w t.action)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ)))
    (hFS : FusariSpigaBinaryNormalSubgroupInput) : T1 :=
  T1_of_preE7_semisimpleCompression_or_sourceOrYonedaTop_data
    lit hgen hRDT hTracey hExceptional hChief hWeight hPrimitive h18 hKP hLMM
    hOuter
    (fun w t => (D w t).toCompressionOrSourceOrYonedaTopData)
    hcoarse hFS

/-- Primitive-socle-facing final alternatives.  The uniform branches retain
the factor count, least index and outer order; only the bounded almost-simple
branch uses a direct finite certificate. -/
inductive PreE7PrimitiveCompressionOrSourceOrYonedaTopData
    (w : ℕ) (U : PreE7NonPairActionClass w) : Type 1 where
  | primitive (data : PreE7PrimitiveCompressionCertificateData w U)
  | imprimitive
      (data : PreE7OriginalMinimalBlockCompressionCertificateData w U)
  | source (data : PreE7RankTailSourceOrYonedaTopData w U)

noncomputable def
    PreE7PrimitiveCompressionOrSourceOrYonedaTopData.toLocalCompressionOrSourceOrYonedaTopData
    {w : ℕ} {U : PreE7NonPairActionClass w}
    (D : PreE7PrimitiveCompressionOrSourceOrYonedaTopData w U) :
    PreE7LocalCompressionOrSourceOrYonedaTopData w U :=
  match D with
  | .primitive data => .primitive data.toPrimitiveLocalCompressionData
  | .imprimitive data => .imprimitive data.toLocalCompressionData
  | .source data => .source data

/-- T1 from the exact primitive-socle compression certificate or an already
integrated affine/soluble/exceptional/Yoneda source. -/
theorem T1_of_preE7_primitiveCompression_or_sourceOrYonedaTop_data
    (lit : PreE7CharacterLiterature)
    (hgen : PermutationSubgroupGeneratorBound)
    (hRDT : MarkedC4.RDTMarkedC4ReductionInput)
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (hKP : KovacsPraegerAbelianizationBound)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hOuter : SemisimpleOuterFactorPermutationBound)
    (D : ∀ w (t : PreE7NumericalTerminalIndex w),
      PreE7PrimitiveCompressionOrSourceOrYonedaTopData w t.action)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ)))
    (hFS : FusariSpigaBinaryNormalSubgroupInput) : T1 :=
  T1_of_preE7_localCompression_or_sourceOrYonedaTop_data
    lit hgen hRDT hTracey hExceptional hChief hWeight hPrimitive h18 hKP hLMM
    hOuter
    (fun w t => (D w t).toLocalCompressionOrSourceOrYonedaTopData)
    hcoarse hFS

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
