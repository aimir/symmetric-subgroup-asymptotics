import SymmetricSubgroupAsymptotics.PrimitiveBoundedIndexCatalogueMatch
import SymmetricSubgroupAsymptotics.PrimitiveSemisimpleBoundedIndexExhaustion

/-!
# Catalogue bridge for bounded primitive compression

The lightweight catalogue-match layer supplies the checked bounded
inequality.  This file installs it in the full pre-E7 exhaustion and T1
recurrence interfaces.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

namespace PrimitiveSemisimpleCatalogueCertificateData

variable {L : Type} [Group L] {r : ℕ}
  (D : PrimitiveSemisimpleCatalogueCertificateData L r)

/-- Discharge the bounded numerical branch from the matched checked row. -/
noncomputable def toBoundedIndexCertificateData :
    PrimitiveSemisimpleBoundedIndexCertificateData L r where
  profile := D.profile
  boundedIndex := fun hone hsmall =>
    PrimitiveBoundedIndexCatalogueResolution.index_bound
      (D.boundedMatch hone hsmall)

noncomputable def certificate :
    PrimitiveSemisimpleCompressionCertificate L r :=
  D.toBoundedIndexCertificateData.certificate

end PrimitiveSemisimpleCatalogueCertificateData

namespace Non2UnipotentPrefixFiniteMenu

/-- Final local exhaustion where every small almost-simple remainder is
identified with a row of the checked primitive catalogue receipt. -/
structure PreE7PrimitiveCatalogueExhaustionData where
  small : ∀ w (U : PreE7NonPairActionClass w), w < 5 →
    PreE7RankTailSourceOrYonedaTopData w U
  primitive : ∀ w (U : PreE7NonPairActionClass w), 5 ≤ w →
    MulAction.IsPreprimitive (preE7NonPairAction w U) (Fin w) →
    PrimitiveSemisimpleCatalogueCertificateData
        (preE7NonPairAction w U) w ⊕
      PreE7RankTailSourceOrYonedaTopData w U
  imprimitive : ∀ w (U : PreE7NonPairActionClass w), 5 ≤ w →
    (basePoint : Fin w) →
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint) →
    PrimitiveSemisimpleCatalogueCertificateData block.Component
        (Nat.card block.Fibre) ⊕
      PreE7RankTailSourceOrYonedaTopData w U

namespace PreE7PrimitiveCatalogueExhaustionData

noncomputable def toBoundedIndexExhaustion
    (D : PreE7PrimitiveCatalogueExhaustionData) :
    PreE7PrimitiveBoundedIndexExhaustionData where
  small := D.small
  primitive := by
    intro w U hw hp
    exact match D.primitive w U hw hp with
    | .inl profile => .inl profile.toBoundedIndexCertificateData
    | .inr source => .inr source
  imprimitive := by
    intro w U hw basePoint block
    exact match D.imprimitive w U hw basePoint block with
    | .inl profile => .inl profile.toBoundedIndexCertificateData
    | .inr source => .inr source

/-- T1 from the primitive structural classification, exact bounded catalogue
matches, and the already integrated action-source alternatives. -/
theorem T1_of_preE7_primitiveCatalogueExhaustion
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
    (D : PreE7PrimitiveCatalogueExhaustionData)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ)))
    (hFS : FusariSpigaBinaryNormalSubgroupInput) : T1 :=
  D.toBoundedIndexExhaustion.T1_of_preE7_primitiveBoundedIndexExhaustion
    lit hgen hRDT hTracey hExceptional hChief hWeight hPrimitive h18 hKP hLMM
    hOuter hcoarse hFS

end PreE7PrimitiveCatalogueExhaustionData

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
