import SymmetricSubgroupAsymptotics.TernaryHighEarlierOwnerSoluble
import SymmetricSubgroupAsymptotics.TernaryHighSemisimpleOwnerWithoutCatalogue

/-! Old intrinsic owners retain their original six-width menu: the sole new
high degree10 is nonaffine primitive and hence cannot be an old soluble owner.
The four old branch labels and all their literal action types stay unchanged. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics
open PrimitiveSocleRawStructure
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

private theorem nonaffine_small_not_soluble
    {A X : Type} [Group A] [Finite A] [Finite X] [MulAction A X]
    (D : NonaffineData A X) (hindex : PublishedSimpleIndexBounds)
    (hsmall : Nat.card X<25) : ¬IsSolvable A := by
  intro hsol
  letI : IsSolvable A := hsol
  have hk := D.factorCount_one_of_degree_lt_twentyFive hindex hsmall
  letI : IsSimpleGroup (finiteGroupSocle A) := (D.oneFactorEquiv hk).isSimpleGroup
  letI : Group.IsPerfect (finiteGroupSocle A) :=
    Group.IsPerfect.top_iff.mp (D.chart.normal_subgroup_perfect ⊤)
  exact Group.IsPerfect.not_isSolvable (finiteGroupSocle A) inferInstance

theorem ternaryHigh_earlierOwner_degree_menu_without_catalogue
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r/3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hgen : PrimitiveNormalGeneratorInput) (hindex : PublishedSimpleIndexBounds)
    (published8 : DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    {A X : Type} [Group A] [Finite A] [Finite X] [MulAction A X]
    [FaithfulSMul A X] [MulAction.IsPretransitive A X]
    (N : Subgroup A) [N.Normal]
    (hhigh : 3*Nat.card X<20*Module.finrank (ZMod 3) (primeRelativeCharacters 3 N))
    (hOld : TernaryHighEarlierOwner A X) :
    Nat.card X=3 ∨ Nat.card X=4 ∨ Nat.card X=6 ∨ Nat.card X=9 ∨
      Nat.card X=12 ∨ Nat.card X=27 := by
  have hm := ternaryHigh_action_degree_menu_without_catalogue
    hChief hWeight hgen hindex published8 h18 N hhigh
  rcases hm with h3|h4|h6|h9|h10|h12|h27
  · exact Or.inl h3
  · exact Or.inr (Or.inl h4)
  · exact Or.inr (Or.inr (Or.inl h6))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h9)))
  · have hp : MulAction.IsPreprimitive A X := by
      by_contra hnp
      have hh := ternaryHigh_imprimitive_degree_menu_without_catalogue
        hChief hWeight hgen hindex published8 h18 N hnp hhigh
      rcases hh with h|h|h|h|h <;> omega
    letI : MulAction.IsPreprimitive A X := hp
    letI : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    cases Classical.choice (publishedONanScottStructure A X) with
    | inl D => exact (nonaffine_small_not_soluble D hindex (by omega) hOld.isSolvable).elim
    | inr P =>
        have hh := P.small_ternaryRelativeHead_strict hp (by omega) (by omega) (by omega) N
        omega
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h12))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h27))))

theorem ternaryHigh_earlierOwner_owned_menu_without_catalogue
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r/3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hgen : PrimitiveNormalGeneratorInput) (hindex : PublishedSimpleIndexBounds)
    (published8 : DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    {A X : Type} [Group A] [Finite A] [Finite X] [MulAction A X]
    [FaithfulSMul A X] [MulAction.IsPretransitive A X]
    (N : Subgroup A) [N.Normal]
    (hhigh : 3*Nat.card X<20*Module.finrank (ZMod 3) (primeRelativeCharacters 3 N))
    (hOld : TernaryHighEarlierOwner A X) :
    IsPGroup 3 A ∨ IsNaturalA4Action A X ∨ Nat.card X=6 ∨ Nat.card X=12 := by
  have hm := ternaryHigh_earlierOwner_degree_menu_without_catalogue
    hChief hWeight hgen hindex published8 h18 N hhigh hOld
  have htwo : 2≤Nat.card X := by rcases hm with h|h|h|h|h|h <;> omega
  letI : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp htwo
  have ht := transitiveTernaryHead_relaxed_stability_without_catalogue
    hChief hgen hindex published8 h18 (X := X) N
  rcases hm with h3|h4|h6|h9|h12|h27
  · exact Or.inl (degreeThree_rankOne_isPGroup h3 N (by
      norm_num [h3,ternaryRelaxedStabilityBound,ternaryStabilityBound] at ht hhigh
      omega))
  · exact Or.inr (Or.inl (degreeFour_rankOne_isNaturalA4 h4 N (by
      norm_num [h4,ternaryRelaxedStabilityBound,ternaryStabilityBound] at ht hhigh
      omega)))
  · exact Or.inr (Or.inr (Or.inl h6))
  · exact Or.inl (degreeNine_rankTwo_isPGroup_without_catalogue
      hChief hgen hindex published8 h18 N h9 (by
        norm_num [h9,ternaryRelaxedStabilityBound,ternaryStabilityBound] at ht hhigh
        omega))
  · exact Or.inr (Or.inr (Or.inr h12))
  · have hp : ¬MulAction.IsPreprimitive A X := by
      intro hp
      letI : MulAction.IsPreprimitive A X := hp
      have hh := primitiveTernaryStrictHead_awayFromTenTwelve_without_catalogue
        hgen hindex published8 A X (by omega) (by omega) (by omega) (by omega) N
      omega
    exact Or.inl (highDegreeTwentySeven_imprimitive_isPGroup_without_catalogue
      hChief hgen hindex published8 h18 N hp h27 hhigh)

end SymmetricSubgroupAsymptotics
