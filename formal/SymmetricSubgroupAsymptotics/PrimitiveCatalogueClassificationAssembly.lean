import SymmetricSubgroupAsymptotics.PrimitiveCatalogueAffineReduction

/-!
# Literal primitive classification and affine-consumer assembly

The primitive classification does not say that some arbitrarily supplied
semisimple profile exists.  It constructs the natural nonaffine socle profile,
or it constructs the regular normal prime-power subgroup of the affine case.
This file records that exact alternative for the original primitive action and
for the literal primitive component of an actual minimal block.

The published classification and the project-owned affine counting theorem
remain separate inputs.  Their assembler is the promised inhabitant of
`PreE7PrimitiveCatalogueExhaustionData`.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- Concrete affine side of the primitive-socle dichotomy.  A normal
`p`-subgroup acts regularly on the primitive domain.  The elementary-abelian
conclusion follows from the standard primitive affine theorem and is not
needed by the assembly below, so the interface retains the smaller literal
witness used to select the already proved affine consumer. -/
structure PrimitiveAffineProfile
    (L Ω : Type*) [Group L] [MulAction L Ω] where
  p : ℕ
  p_prime : p.Prime
  V : Subgroup L
  [V_normal : V.Normal]
  V_pgroup : IsPGroup p V
  regular : ∀ x y : Ω, ∃! v : V, v • x = y

attribute [instance] PrimitiveAffineProfile.V_normal

namespace Non2UnipotentPrefixFiniteMenu

/-- Published primitive classification, including the exact finite-catalogue
locator on the bounded nonaffine branch.  The output is the natural socle
profile or a literal regular normal prime-power subgroup; it is never a split
on existence of an arbitrary user-supplied profile. -/
structure PreE7PrimitiveCatalogueClassificationInput where
  primitive : ∀ w (U : PreE7NonPairActionClass w), 5 ≤ w →
    MulAction.IsPreprimitive (preE7NonPairAction w U) (Fin w) →
    PrimitiveSemisimpleCatalogueCertificateData
        (preE7NonPairAction w U) w ⊕
      PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w)
  imprimitive : ∀ w (U : PreE7NonPairActionClass w), 5 ≤ w →
    (basePoint : Fin w) →
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint) →
    PrimitiveSemisimpleCatalogueCertificateData block.Component
        (Nat.card block.Fibre) ⊕
      PrimitiveAffineProfile block.Component block.Fibre

/-- Project-owned consumers for the affine side of the literal primitive
classification.  Each output is one of the concrete source/Yoneda objects
already integrated into the numerical recurrence. -/
structure PreE7PrimitiveAffineConsumerData where
  small : ∀ w (U : PreE7NonPairActionClass w), w < 5 →
    PreE7RankTailSourceOrYonedaTopData w U
  primitive : ∀ w (U : PreE7NonPairActionClass w), 5 ≤ w →
    MulAction.IsPreprimitive (preE7NonPairAction w U) (Fin w) →
    PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w) →
    PreE7RankTailSourceOrYonedaTopData w U
  imprimitive : ∀ w (U : PreE7NonPairActionClass w), 5 ≤ w →
    (basePoint : Fin w) →
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint) →
    PrimitiveAffineProfile block.Component block.Fibre →
    PreE7RankTailSourceOrYonedaTopData w U

/-- Assemble the actual primitive/nonaffine catalogue row and the proved
affine consumer into the final exhaustion datum used by T1. -/
noncomputable def preE7PrimitiveCatalogueExhaustionData
    (classification : PreE7PrimitiveCatalogueClassificationInput)
    (affine : PreE7PrimitiveAffineConsumerData) :
    PreE7PrimitiveCatalogueExhaustionData where
  small := affine.small
  primitive := by
    intro w U hw hp
    exact match classification.primitive w U hw hp with
    | .inl nonaffine => .inl nonaffine
    | .inr profile => .inr (affine.primitive w U hw hp profile)
  imprimitive := by
    intro w U hw basePoint block
    exact match classification.imprimitive w U hw basePoint block with
    | .inl nonaffine => .inl nonaffine
    | .inr profile => .inr
        (affine.imprimitive w U hw basePoint block profile)

/-- T1 with the published primitive classification and the project affine
consumer exposed as distinct assumptions. -/
theorem T1_of_preE7_primitiveCatalogueClassification
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
    (classification : PreE7PrimitiveCatalogueClassificationInput)
    (affine : PreE7PrimitiveAffineConsumerData)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ)))
    (hFS : FusariSpigaBinaryNormalSubgroupInput) : T1 :=
  (preE7PrimitiveCatalogueExhaustionData classification affine).T1_of_preE7_primitiveCatalogueExhaustion
    lit hgen hRDT hTracey hExceptional hChief hWeight hPrimitive h18 hKP hLMM
    hOuter hcoarse hFS

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
