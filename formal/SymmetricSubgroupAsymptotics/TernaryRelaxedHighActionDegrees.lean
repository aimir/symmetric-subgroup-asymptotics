import SymmetricSubgroupAsymptotics.TernaryRelaxedHighImprimitiveDegrees
import SymmetricSubgroupAsymptotics.TernaryHighActionDegrees

/-! The actual high-orbit finite menu without the composition catalogue:
only primitive degree10 is added, and primitive degree12 is retained
separately for its semisimple source. All original normal pairs remain. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

theorem ternaryHigh_action_degree_menu_without_catalogue
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r/3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    {A X : Type} [Group A] [Finite A] [Finite X] [MulAction A X]
    [FaithfulSMul A X] [MulAction.IsPretransitive A X]
    (N : Subgroup A) [N.Normal]
    (hhigh : 3*Nat.card X<20*Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)) :
    Nat.card X=3 ∨ Nat.card X=4 ∨ Nat.card X=6 ∨ Nat.card X=9 ∨
      Nat.card X=10 ∨ Nat.card X=12 ∨ Nat.card X=27 := by
  have htwo : 2≤Nat.card X := by
    by_contra h
    letI : Subsingleton X := Finite.card_le_one_iff_subsingleton.mp (by omega)
    have hh := primeRelativeHead_subsingleton_action (A := A) (Ω := X) 3 N
    omega
  letI : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp htwo
  by_cases hp : MulAction.IsPreprimitive A X
  · letI : MulAction.IsPreprimitive A X := hp
    by_cases h3 : Nat.card X=3
    · exact Or.inl h3
    by_cases h4 : Nat.card X=4
    · exact Or.inr (Or.inl h4)
    by_cases h10 : Nat.card X=10
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h10))))
    by_cases h12 : Nat.card X=12
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h12)))))
    have hs := primitiveTernaryStrictHead_awayFromTenTwelve_without_catalogue
      hgen hindex published8 A X h3 h4 h10 h12 N
    omega
  · have hm := ternaryHigh_imprimitive_degree_menu_without_catalogue
      hChief hWeight hgen hindex published8 h18 N hp hhigh
    rcases hm with h6|h9|h12|h18x|h27
    · exact Or.inr (Or.inr (Or.inl h6))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h9)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h12)))))
    · have hr := h18 A X h18x N
      omega
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h27)))))

end SymmetricSubgroupAsymptotics
