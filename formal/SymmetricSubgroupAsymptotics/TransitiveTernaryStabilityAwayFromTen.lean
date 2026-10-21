import SymmetricSubgroupAsymptotics.TransitiveTernaryRelaxedStabilityWithoutCatalogue

/-! Away from degree10 the proved relaxed bound is the original stability
envelope. This adapter is used only with actual displayed degree data. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

theorem transitiveTernaryHead_stability_without_catalogue_of_ne_ten
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r/3))
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    {A X : Type} [Group A] [Finite A] [Finite X] [MulAction A X]
    [FaithfulSMul A X] [MulAction.IsPretransitive A X] [Nonempty X]
    (h10 : Nat.card X≠10) (N : Subgroup A) [N.Normal] :
    Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)≤
      ternaryStabilityBound (Nat.card X) := by
  simpa only [ternaryRelaxedStabilityBound,if_neg h10] using
    transitiveTernaryHead_relaxed_stability_without_catalogue
      hChief hgen hindex published8 h18 (X := X) N

end SymmetricSubgroupAsymptotics
