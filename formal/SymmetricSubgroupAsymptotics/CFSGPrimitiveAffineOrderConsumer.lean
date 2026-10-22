import SymmetricSubgroupAsymptotics.CFSGPrimitiveAffineOrderConsumerAwaySixtyFour
import SymmetricSubgroupAsymptotics.CFSGPrimitiveAffineBinarySixSource

/-! Complete original primitive-affine sources from actual order and trace
budgets. The degree16 translation source and every original normal axis are
preserved. There is no primitive-composition-length premise. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
namespace CFSGPrimitiveAffineOrderConsumer

def primitiveSource
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (hgen : PermutationSubgroupGeneratorBound)
    (hKP : KovacsPraegerAbelianizationBound)
    {w : ℕ} (U : PreE7NonPairActionClass w) (hw : 5 ≤ w)
    (hp : MulAction.IsPreprimitive (preE7NonPairAction w U) (Fin w))
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w)) :
    PreE7RankTailOwnerSourceData w U ⊕ PreE7RankTailSourceOrYonedaTopData w U := by
  by_cases h16 : w = 16
  · subst w
    exact .inr (PrimitiveAffineSixteenActualColdSource.source P hp 0)
  by_cases h64 : w = 64
  · subst w
    by_cases hs : IsSolvable (P.complement ⟨0, by decide⟩)
    · exact .inl (primitiveAffineEvenSoluble_rankTailOwnerSourceData
        U (by decide) (by decide) (by decide) hp P hs)
    · exact .inl (CFSGPrimitiveAffineBinarySixSource.source64 hindex U hp P hs)
  · exact .inl (primitiveOwnerAwaySixteenAndSixtyFour hindex hgen hKP U hw hp P h16 h64)

end CFSGPrimitiveAffineOrderConsumer
end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
