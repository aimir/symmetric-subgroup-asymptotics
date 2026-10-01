import SymmetricSubgroupAsymptotics.PrimitiveBoundedIndexReceipt

/-!
# Catalogue bridge for bounded primitive compression

The generated receipt proves `2q <= r` for each of the 116 bounded primitive
locators.  This file isolates the remaining correspondence statement: a
literal one-factor outer-log profile has the same degree and quotient order
as one receipt row.  Once those two equalities are supplied, Lean transports
the checked inequality and constructs the full compression certificate.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- Exact correspondence between one literal outer-log profile and one row of
the kernel-checked bounded primitive receipt. -/
structure PrimitiveBoundedIndexCatalogueMatch
    {L : Type} [Group L] {r : ℕ}
    (C : PrimitiveSemisimpleOuterLogProfile L r) where
  row : Fin 116
  degree_eq : (primitiveBoundedIndexRow row).degree = r
  outerOrder_eq : (primitiveBoundedIndexRow row).outerOrder = C.outerOrder

namespace PrimitiveBoundedIndexCatalogueMatch

variable {L : Type} [Group L] {r : ℕ}
  {C : PrimitiveSemisimpleOuterLogProfile L r}
  (M : PrimitiveBoundedIndexCatalogueMatch C)

include M

/-- The catalogue equalities transport the kernel-checked row inequality to
the literal quotient order in the primitive profile. -/
theorem index_bound : 2 * C.outerOrder ≤ r := by
  let row := PrimitiveBoundedIndexCatalogueMatch.row M
  calc
    2 * C.outerOrder = 2 * (primitiveBoundedIndexRow row).outerOrder := by
      rw [PrimitiveBoundedIndexCatalogueMatch.outerOrder_eq M]
    _ ≤ (primitiveBoundedIndexRow row).degree :=
      primitiveBoundedIndexRow_bound row
    _ = r := PrimitiveBoundedIndexCatalogueMatch.degree_eq M

end PrimitiveBoundedIndexCatalogueMatch

/-- Natural outer-log data in which each bounded one-factor branch is matched
to an exact row of the finite primitive receipt. -/
structure PrimitiveSemisimpleCatalogueCertificateData
    (L : Type) [Group L] (r : ℕ) where
  profile : PrimitiveSemisimpleOuterLogProfile L r
  boundedMatch : profile.factorCount = 1 → profile.leastIndex < 30 →
    PrimitiveBoundedIndexCatalogueMatch profile

namespace PrimitiveSemisimpleCatalogueCertificateData

variable {L : Type} [Group L] {r : ℕ}
  (D : PrimitiveSemisimpleCatalogueCertificateData L r)

/-- Discharge the bounded numerical branch from the matched checked row. -/
noncomputable def toBoundedIndexCertificateData :
    PrimitiveSemisimpleBoundedIndexCertificateData L r where
  profile := D.profile
  boundedIndex := fun hone hsmall =>
    PrimitiveBoundedIndexCatalogueMatch.index_bound
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
    lit hgen hTracey hExceptional hChief hWeight hPrimitive h18 hKP hLMM
    hOuter hcoarse hFS

end PreE7PrimitiveCatalogueExhaustionData

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
