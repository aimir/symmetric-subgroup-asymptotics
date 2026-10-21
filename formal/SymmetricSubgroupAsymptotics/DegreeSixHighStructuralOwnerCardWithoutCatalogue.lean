import SymmetricSubgroupAsymptotics.DegreeSixHighStructuralOwnerWithoutCatalogue

/-! The actual degree6 owner keeps its order-three complement. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics
theorem degreeSix_high_structuralOwnerWithComplementCard_without_catalogue
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    {A X : Type} [Group A] [Finite A] [Finite X] [MulAction A X]
    [FaithfulSMul A X] [MulAction.IsPretransitive A X]
    (N : Subgroup A) [N.Normal] (hDegree : Nat.card X=6)
    (hHigh : 3*Nat.card X<20*Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)) :
    Nonempty (C1OddIndexTwoOwnerWitness A) ∨
      ∃ W : C1CyclicBinaryModuleOwnerWitness A,Nat.card W.complement=3 := by
  rcases degreeSix_high_oddIndexOwner_or_binaryBlock_without_catalogue
    hgen hindex published8 N hDegree hHigh with hOdd|⟨x,D,hF,hP⟩
  · exact Or.inl hOdd
  · exact Or.inr (D.degreeSix_binaryBlock_ownerWithCard N hF hP hHigh)

end SymmetricSubgroupAsymptotics
