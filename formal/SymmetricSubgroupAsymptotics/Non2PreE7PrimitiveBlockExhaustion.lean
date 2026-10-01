import SymmetricSubgroupAsymptotics.Non2PreE7ActualBlockCompressionClosure

/-!
# Final pre-E7 exhaustion on primitive components

The exact block construction already turns a compression certificate on one
literal minimal block component into a compression of the original action.
This file also removes the choice of that block from the remaining theorem.
Every retained action of width at least five is split into its primitive and
imprimitive cases.  In the latter case Lean chooses an actual minimal block,
whose component is primitive, and asks the classifier only about that local
component.

Thus the remaining classification inputs are local: the two widths below
five, primitive original actions, and primitive components of actual minimal
blocks.  No finite action census or owner label is inserted here.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- Classification data after the abstract primitive/imprimitive dichotomy.
The source alternative always belongs to the original action.  In the
imprimitive branch only the compression certificate is local to the selected
minimal block component. -/
structure PreE7PrimitiveComponentExhaustionData where
  small : ∀ w (U : PreE7NonPairActionClass w), w < 5 →
    PreE7RankTailSourceOrYonedaTopData w U
  primitive : ∀ w (U : PreE7NonPairActionClass w), 5 ≤ w →
    MulAction.IsPreprimitive (preE7NonPairAction w U) (Fin w) →
    PreE7PrimitiveCompressionCertificateData w U ⊕
      PreE7RankTailSourceOrYonedaTopData w U
  imprimitive : ∀ w (U : PreE7NonPairActionClass w), 5 ≤ w →
    (basePoint : Fin w) →
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint) →
    PrimitiveSemisimpleCompressionCertificate block.Component
        (Nat.card block.Fibre) ⊕
      PreE7RankTailSourceOrYonedaTopData w U

namespace PreE7PrimitiveComponentExhaustionData

/-- The primitive-component classifier constructs the exact final structural
alternative for every retained action.  The imprimitive proof uses an actual
minimal block of the original action and retains that block in the resulting
certificate. -/
noncomputable def classify
    (D : PreE7PrimitiveComponentExhaustionData)
    (w : ℕ) (U : PreE7NonPairActionClass w) :
    PreE7PrimitiveCompressionOrSourceOrYonedaTopData w U := by
  by_cases hw : 5 ≤ w
  · by_cases hp : MulAction.IsPreprimitive
        (preE7NonPairAction w U) (Fin w)
    · exact match D.primitive w U hw hp with
      | .inl compression => .primitive compression
      | .inr source => .source source
    · letI : Nontrivial (Fin w) :=
        Fin.nontrivial_iff_two_le.mpr (by omega)
      let basePoint : Fin w := ⟨0, by omega⟩
      let block : OriginalMinimalBlock
          (A := preE7NonPairAction w U) basePoint :=
        Classical.choice (originalMinimalBlock_nonempty basePoint hp)
      exact match D.imprimitive w U hw basePoint block with
      | .inl compression => .imprimitive
          { width_lower := hw
            basePoint := basePoint
            block := block
            certificate := compression }
      | .inr source => .source source
  · exact .source (D.small w U (by omega))

/-- T1 after the general primitive/imprimitive split and actual minimal-block
choice have been discharged.  What remains in `D` is precisely the local
primitive classification and the already integrated source alternatives. -/
theorem T1_of_preE7_primitiveComponentExhaustion
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
    (D : PreE7PrimitiveComponentExhaustionData)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ)))
    (hFS : FusariSpigaBinaryNormalSubgroupInput) : T1 :=
  T1_of_preE7_primitiveCompression_or_sourceOrYonedaTop_data
    lit hgen hRDT hTracey hExceptional hChief hWeight hPrimitive h18 hKP hLMM
    hOuter D.classify hcoarse hFS

end PreE7PrimitiveComponentExhaustionData

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
