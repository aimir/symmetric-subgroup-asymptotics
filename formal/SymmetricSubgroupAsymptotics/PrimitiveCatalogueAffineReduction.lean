import SymmetricSubgroupAsymptotics.PrimitiveBoundedIndexCatalogueBridge

/-!
# Separating primitive catalogue matching from the affine remainder

The bounded primitive receipt checks the numerical row attached to a
nonaffine semisimple profile.  It does not, by itself, say that an arbitrary
primitive action has such a profile, nor that the complementary affine case
belongs to one of the already proved source families.

This file makes that distinction formal.  `PreE7PrimitiveCatalogueMatchData`
is only the finite primitive-catalogue correspondence: whenever a literal
profile is present, its bounded one-factor branch is identified with a row of
the checked receipt.  `PreE7AffineRemainderExhaustionData` contains only the
complementary source assertion, stated after the nonexistence of any such
profile.  Their assembler constructs the older
`PreE7PrimitiveCatalogueExhaustionData` without hiding either obligation in a
blanket action-exhaustion hypothesis.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- Exact finite-catalogue matching for every semisimple profile which can
occur on the original primitive action or on the selected literal minimal
block component.  The hypotheses `hone` and `hsmall` restrict the request to
the 116-row bounded almost-simple slice. -/
structure PreE7PrimitiveCatalogueMatchData where
  primitive : ∀ w (U : PreE7NonPairActionClass w), 5 ≤ w →
    MulAction.IsPreprimitive (preE7NonPairAction w U) (Fin w) →
    (profile : PrimitiveSemisimpleOuterLogProfile
      (preE7NonPairAction w U) w) →
    profile.factorCount = 1 → profile.leastIndex < 30 →
    PrimitiveBoundedIndexCatalogueMatch profile
  imprimitive : ∀ w (U : PreE7NonPairActionClass w), 5 ≤ w →
    (basePoint : Fin w) →
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint) →
    (profile : PrimitiveSemisimpleOuterLogProfile block.Component
      (Nat.card block.Fibre)) →
    profile.factorCount = 1 → profile.leastIndex < 30 →
    PrimitiveBoundedIndexCatalogueMatch profile

/-- The project-owned complement of the nonaffine primitive profile.  It asks
for a concrete, already integrated owner/Yoneda source only after Lean has a
proof that no semisimple outer-log profile exists on the literal primitive
action or block component. -/
structure PreE7AffineRemainderExhaustionData where
  small : ∀ w (U : PreE7NonPairActionClass w), w < 5 →
    PreE7RankTailSourceOrYonedaTopData w U
  primitive : ∀ w (U : PreE7NonPairActionClass w), 5 ≤ w →
    MulAction.IsPreprimitive (preE7NonPairAction w U) (Fin w) →
    (¬ Nonempty (PrimitiveSemisimpleOuterLogProfile
      (preE7NonPairAction w U) w)) →
    PreE7RankTailSourceOrYonedaTopData w U
  imprimitive : ∀ w (U : PreE7NonPairActionClass w), 5 ≤ w →
    (basePoint : Fin w) →
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint) →
    (¬ Nonempty (PrimitiveSemisimpleOuterLogProfile block.Component
      (Nat.card block.Fibre))) →
    PreE7RankTailSourceOrYonedaTopData w U

/-- The finite primitive correspondence and the affine remainder together
inhabit the final primitive catalogue interface.  The split is made by actual
existence of a literal semisimple profile, so no affine/nonaffine ledger label
enters the theorem. -/
noncomputable def PreE7PrimitiveCatalogueExhaustionData.ofMatchAndAffine
    (M : PreE7PrimitiveCatalogueMatchData)
    (A : PreE7AffineRemainderExhaustionData) :
    PreE7PrimitiveCatalogueExhaustionData where
  small := A.small
  primitive := by
    intro w U hw hp
    by_cases hprofile : Nonempty (PrimitiveSemisimpleOuterLogProfile
        (preE7NonPairAction w U) w)
    · let profile := Classical.choice hprofile
      exact .inl
        { profile := profile
          boundedMatch := M.primitive w U hw hp profile }
    · exact .inr (A.primitive w U hw hp hprofile)
  imprimitive := by
    intro w U hw basePoint block
    by_cases hprofile : Nonempty (PrimitiveSemisimpleOuterLogProfile
        block.Component (Nat.card block.Fibre))
    · let profile := Classical.choice hprofile
      exact .inl
        { profile := profile
          boundedMatch := M.imprimitive w U hw basePoint block profile }
    · exact .inr (A.imprimitive w U hw basePoint block hprofile)

/-- T1 with the finite primitive catalogue correspondence and the affine
remainder displayed as separate arguments. -/
theorem T1_of_preE7_primitiveCatalogueMatch_and_affineRemainder
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
    (M : PreE7PrimitiveCatalogueMatchData)
    (A : PreE7AffineRemainderExhaustionData)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ)))
    (hFS : FusariSpigaBinaryNormalSubgroupInput) : T1 :=
  (PreE7PrimitiveCatalogueExhaustionData.ofMatchAndAffine M A).T1_of_preE7_primitiveCatalogueExhaustion
    lit hgen hTracey hExceptional hChief hWeight hPrimitive h18 hKP hLMM
    hOuter hcoarse hFS

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
