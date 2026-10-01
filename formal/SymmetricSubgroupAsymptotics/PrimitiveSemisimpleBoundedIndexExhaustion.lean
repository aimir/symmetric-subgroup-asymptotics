import SymmetricSubgroupAsymptotics.PrimitiveSemisimpleOuterLogExhaustion

/-!
# Bounded primitive compression from the quotient-index inequality

The outer-log profile already retains the literal semisimple subgroup, its
product chart and a faithful action of the quotient on
`factorCount * outerOrder` points.  In the sole bounded branch the factor
count is one.  Consequently the finite primitive package need only certify
the integer inequality `2 * outerOrder <= r`; it does not have to export a
second quotient map or reprove its kernel.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

namespace PrimitiveSemisimpleOuterLogProfile

variable {L : Type} [Group L] {r : ℕ}
  (C : PrimitiveSemisimpleOuterLogProfile L r)

/-- In the one-factor branch the quotient action already stored in the
outer-log profile is a bounded local compression as soon as its actual order
fits in half the local degree. -/
noncomputable def toLocalCompressionOfBoundedIndex
    (hone : C.factorCount = 1)
    (hindex : 2 * C.outerOrder ≤ r) :
    LocalSemisimpleCompressionData L r where
  E := C.E
  E_normal := C.E_normal
  chart := C.chart
  quotientDegree := C.factorCount * C.outerOrder
  quotientDegree_pos := Nat.mul_pos C.factorCount_pos C.outerOrder_pos
  quotientAction := C.quotientAction
  quotientAction_injective := C.quotientAction_injective
  quotientDegree_small := by
    apply even_le_evenWidth
    · exact ⟨C.factorCount * C.outerOrder, by omega⟩
    · simpa only [hone, one_mul] using hindex

end PrimitiveSemisimpleOuterLogProfile

/-- Natural outer-log data whose only finite remainder is the checked
quotient-index inequality in the one-factor, least-index-below-thirty range. -/
structure PrimitiveSemisimpleBoundedIndexCertificateData
    (L : Type) [Group L] (r : ℕ) where
  profile : PrimitiveSemisimpleOuterLogProfile L r
  boundedIndex : profile.factorCount = 1 → profile.leastIndex < 30 →
    2 * profile.outerOrder ≤ r

namespace PrimitiveSemisimpleBoundedIndexCertificateData

variable {L : Type} [Group L] {r : ℕ}
  (D : PrimitiveSemisimpleBoundedIndexCertificateData L r)

/-- Convert the numerical bounded row to the older direct-certificate
interface.  The literal quotient action and semisimple chart are reused. -/
noncomputable def toOuterLogCertificateData :
    PrimitiveSemisimpleOuterLogCertificateData L r where
  profile := D.profile
  bounded := fun hone hsmall =>
    D.profile.toLocalCompressionOfBoundedIndex hone
      (D.boundedIndex hone hsmall)

/-- Every natural profile plus the bounded index inequality gives the full
uniform-or-bounded primitive compression certificate. -/
noncomputable def certificate :
    PrimitiveSemisimpleCompressionCertificate L r :=
  D.toOuterLogCertificateData.certificate

end PrimitiveSemisimpleBoundedIndexCertificateData

namespace Non2UnipotentPrefixFiniteMenu

/-- Final local exhaustion with the bounded primitive package reduced to its
actual numerical output `2 |L/E| <= r`. -/
structure PreE7PrimitiveBoundedIndexExhaustionData where
  small : ∀ w (U : PreE7NonPairActionClass w), w < 5 →
    PreE7RankTailSourceOrYonedaTopData w U
  primitive : ∀ w (U : PreE7NonPairActionClass w), 5 ≤ w →
    MulAction.IsPreprimitive (preE7NonPairAction w U) (Fin w) →
    PrimitiveSemisimpleBoundedIndexCertificateData
        (preE7NonPairAction w U) w ⊕
      PreE7RankTailSourceOrYonedaTopData w U
  imprimitive : ∀ w (U : PreE7NonPairActionClass w), 5 ≤ w →
    (basePoint : Fin w) →
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint) →
    PrimitiveSemisimpleBoundedIndexCertificateData block.Component
        (Nat.card block.Fibre) ⊕
      PreE7RankTailSourceOrYonedaTopData w U

namespace PreE7PrimitiveBoundedIndexExhaustionData

/-- Forget only the already discharged bounded-index conversion. -/
noncomputable def toOuterLogExhaustion
    (D : PreE7PrimitiveBoundedIndexExhaustionData) :
    PreE7PrimitiveOuterLogExhaustionData where
  small := D.small
  primitive := by
    intro w U hw hp
    exact match D.primitive w U hw hp with
    | .inl profile => .inl profile.toOuterLogCertificateData
    | .inr source => .inr source
  imprimitive := by
    intro w U hw basePoint block
    exact match D.imprimitive w U hw basePoint block with
    | .inl profile => .inl profile.toOuterLogCertificateData
    | .inr source => .inr source

/-- T1 from natural primitive-socle profiles, the finite quotient-index
inequality below least index thirty, and the integrated source alternatives. -/
theorem T1_of_preE7_primitiveBoundedIndexExhaustion
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
    (D : PreE7PrimitiveBoundedIndexExhaustionData)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ)))
    (hFS : FusariSpigaBinaryNormalSubgroupInput) : T1 :=
  D.toOuterLogExhaustion.T1_of_preE7_primitiveOuterLogExhaustion
    lit hgen hRDT hTracey hExceptional hChief hWeight hPrimitive h18 hKP hLMM
    hOuter hcoarse hFS

end PreE7PrimitiveBoundedIndexExhaustionData

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
