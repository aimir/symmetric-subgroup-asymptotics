import SymmetricSubgroupAsymptotics.CFSGSufficientTernaryOwnerExhaustion
import SymmetricSubgroupAsymptotics.CFSGSufficientTernarySmallOwnersDirect
import SymmetricSubgroupAsymptotics.CFSGSufficientSmallPrimitiveCompression
import SymmetricSubgroupAsymptotics.TernaryHighEarlierOwnerBoundedMenu
import SymmetricSubgroupAsymptotics.TernaryHighEarlierOwnerSoluble
import SymmetricSubgroupAsymptotics.TernaryHighSemisimpleOwnerWithoutCatalogue

/-! Direct actual-head forwarding; the ordinary primitive normal-generator input is absent.

 The SAME original six-owner disjunction and actual10/12 semisimple
predicate follow from sufficient consumers. Existing owner predicates and
all physical family definitions are shared, not replaced by new records. -/

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
    (D : NonaffineData A X) (hindex : SufficientSimpleIndexBounds)
    (hsmall : Nat.card X<25) : ¬IsSolvable A := by
  intro hsol
  letI : IsSolvable A := hsol
  have hk := D.factorCount_one_of_sufficient_degree_lt_twentyFive hindex hsmall
  letI : IsSimpleGroup (finiteGroupSocle A) := (D.oneFactorEquiv hk).isSimpleGroup
  letI : Group.IsPerfect (finiteGroupSocle A) :=
    Group.IsPerfect.top_iff.mp (D.chart.normal_subgroup_perfect ⊤)
  exact Group.IsPerfect.not_isSolvable (finiteGroupSocle A) inferInstance

theorem ternaryHigh_earlierOwner_degree_menu_of_sufficientHead
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r/3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
     (hindex : SufficientSimpleIndexBounds)
    (published8 : DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    {A X : Type} [Group A] [Finite A] [Finite X] [MulAction A X]
    [FaithfulSMul A X] [MulAction.IsPretransitive A X]
    (N : Subgroup A) [N.Normal]
    (hhigh : 3*Nat.card X<20*Module.finrank (ZMod 3) (primeRelativeCharacters 3 N))
    (hOld : TernaryHighEarlierOwner A X) :
    Nat.card X=3 ∨ Nat.card X=4 ∨ Nat.card X=6 ∨ Nat.card X=9 ∨
      Nat.card X=12 ∨ Nat.card X=27 := by
  have hm := ternaryHigh_action_degree_menu_of_sufficientHead
    hChief hWeight  hindex published8 h18 N hhigh
  rcases hm with h3|h4|h6|h9|h10|h12|h27
  · exact Or.inl h3
  · exact Or.inr (Or.inl h4)
  · exact Or.inr (Or.inr (Or.inl h6))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h9)))
  · have hp : MulAction.IsPreprimitive A X := by
      by_contra hnp
      have hh := ternaryHigh_imprimitive_degree_menu_of_sufficientHead
        hChief hWeight  hindex published8 h18 N hnp hhigh
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

theorem ternaryHigh_earlierOwner_owned_menu_of_sufficientHead
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r/3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
     (hindex : SufficientSimpleIndexBounds)
    (published8 : DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    {A X : Type} [Group A] [Finite A] [Finite X] [MulAction A X]
    [FaithfulSMul A X] [MulAction.IsPretransitive A X]
    (N : Subgroup A) [N.Normal]
    (hhigh : 3*Nat.card X<20*Module.finrank (ZMod 3) (primeRelativeCharacters 3 N))
    (hOld : TernaryHighEarlierOwner A X) :
    IsPGroup 3 A ∨ IsNaturalA4Action A X ∨ Nat.card X=6 ∨ Nat.card X=12 := by
  have hm := ternaryHigh_earlierOwner_degree_menu_of_sufficientHead
    hChief hWeight  hindex published8 h18 N hhigh hOld
  have htwo : 2≤Nat.card X := by rcases hm with h|h|h|h|h|h <;> omega
  letI : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp htwo
  have ht := transitiveTernaryHead_relaxed_stability_of_sufficientHead
    hChief  hindex published8 h18 (X := X) N
  rcases hm with h3|h4|h6|h9|h12|h27
  · exact Or.inl (degreeThree_rankOne_isPGroup h3 N (by
      norm_num [h3,ternaryRelaxedStabilityBound,ternaryStabilityBound] at ht hhigh
      omega))
  · exact Or.inr (Or.inl (degreeFour_rankOne_isNaturalA4 h4 N (by
      norm_num [h4,ternaryRelaxedStabilityBound,ternaryStabilityBound] at ht hhigh
      omega)))
  · exact Or.inr (Or.inr (Or.inl h6))
  · exact Or.inl (degreeNine_rankTwo_isPGroup_of_sufficientHead
      hChief  hindex published8 h18 N h9 (by
        norm_num [h9,ternaryRelaxedStabilityBound,ternaryStabilityBound] at ht hhigh
        omega))
  · exact Or.inr (Or.inr (Or.inr h12))
  · have hp : ¬MulAction.IsPreprimitive A X := by
      intro hp
      letI : MulAction.IsPreprimitive A X := hp
      have hh := primitiveTernaryStrictHead_awayFromTenTwelve_of_sufficientHead
         hindex published8 A X (by omega) (by omega) (by omega) (by omega) N
      omega
    exact Or.inl (highDegreeTwentySeven_imprimitive_isPGroup_of_sufficientHead
      hChief  hindex published8 h18 N hp h27 hhigh)

end SymmetricSubgroupAsymptotics

set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics
theorem TernaryHighEarlierOwner.degreeTwelve_imprimitive_of_sufficientHead
    {A X : Type} [Group A] [Finite A] [Finite X] [MulAction A X]
    [FaithfulSMul A X] (h : TernaryHighEarlierOwner A X)
    (hindex : PrimitiveSocleRawStructure.SufficientSimpleIndexBounds)
    (h12 : Nat.card X=12) : ¬MulAction.IsPreprimitive A X := by
  intro hp
  letI : MulAction.IsPreprimitive A X := hp
  letI : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  letI : IsSolvable A := h.isSolvable
  cases Classical.choice (PrimitiveSocleRawStructure.publishedONanScottStructure A X) with
  | inr P =>
      have hh := P.degree_isPrimePow hp
      rw [h12] at hh
      exact (show ¬IsPrimePow (12 : ℕ) by decide) hh
  | inl D =>
      have hk := D.factorCount_one_of_sufficient_degree_lt_twentyFive hindex (by omega)
      letI : IsSimpleGroup (finiteGroupSocle A) := (D.oneFactorEquiv hk).isSimpleGroup
      letI : Group.IsPerfect (finiteGroupSocle A) :=
        Group.IsPerfect.top_iff.mp (D.chart.normal_subgroup_perfect ⊤)
      exact Group.IsPerfect.not_isSolvable (finiteGroupSocle A) inferInstance

end SymmetricSubgroupAsymptotics


/-! The high frontier without the composition catalogue retains the original
six structural owners and adds only actual nonaffine primitive degree10/12.
The new cases carry actual-kernel semisimple compression; the original
normal pair and the untouched complement can therefore be retained. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics
open PrimitiveSocleRawStructure
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

/-- Actual primitive semisimple owner on the original point set and group. -/
private theorem high_primitive_ten_twelve_nonaffine
    {A X : Type} [Group A] [Finite A] [Finite X] [MulAction A X]
    [FaithfulSMul A X] [MulAction.IsPreprimitive A X] [Nontrivial X]
    (hdegree : Nat.card X=10 ∨ Nat.card X=12)
    (N : Subgroup A) [N.Normal]
    (hhigh : 3*Nat.card X<20*Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)) :
    Nonempty (NonaffineData A X) := by
  cases Classical.choice (publishedONanScottStructure A X) with
  | inl D => exact ⟨D⟩
  | inr P =>
      have hh := P.small_ternaryRelativeHead_strict inferInstance (by omega)
        (by omega) (by omega) N
      omega

/-- Every high action has an existing intrinsic owner or one of the two
new actual primitive semisimple owners. No global strict-head assertion is
assumed for the two boundary degrees. -/
theorem ternaryHigh_earlierOwner_or_semisimple_of_sufficientHead
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r/3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
     (hindex : SufficientSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    {A X : Type} [Group A] [Finite A] [Finite X] [MulAction A X]
    [FaithfulSMul A X] [MulAction.IsPretransitive A X]
    (N : Subgroup A) [N.Normal]
    (hhigh : 3*Nat.card X<20*Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)) :
    TernaryHighEarlierOwner A X ∨ TernaryHighPrimitiveSemisimpleOwner A X := by
  have hdegree := ternaryHigh_action_degree_menu_of_sufficientHead
    hChief hWeight  hindex published8 h18 N hhigh
  have htwo : 2≤Nat.card X := by
    rcases hdegree with h|h|h|h|h|h|h <;> omega
  letI : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp htwo
  have htop := transitiveTernaryHead_relaxed_stability_of_sufficientHead
    hChief  hindex published8 h18 (X := X) N
  rcases hdegree with h3|h4|h6|h9|h10|h12|h27
  · exact Or.inl (Or.inl (degreeThree_rankOne_isPGroup h3 N (by
      norm_num [h3,ternaryRelaxedStabilityBound,ternaryStabilityBound] at htop hhigh
      omega)))
  · exact Or.inl (Or.inr (Or.inl (degreeFour_rankOne_isNaturalA4 h4 N (by
      norm_num [h4,ternaryRelaxedStabilityBound,ternaryStabilityBound] at htop hhigh
      omega))))
  · rcases degreeSix_high_structuralOwner_of_sufficientHead
       hindex published8 N h6 hhigh with hOdd|hCyclic
    · exact Or.inl (Or.inr (Or.inr (Or.inl hOdd)))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl hCyclic))))
  · exact Or.inl (Or.inl (degreeNine_rankTwo_isPGroup_of_sufficientHead
      hChief  hindex published8 h18 N h9 (by
        norm_num [h9,ternaryRelaxedStabilityBound,ternaryStabilityBound] at htop hhigh
        omega)))
  · have hp : MulAction.IsPreprimitive A X := by
      by_contra hnp
      have hh := ternaryHigh_imprimitive_degree_menu_of_sufficientHead
        hChief hWeight  hindex published8 h18 N hnp hhigh
      rcases hh with h|h|h|h|h <;> omega
    letI : MulAction.IsPreprimitive A X := hp
    exact Or.inr ⟨hp,Or.inl h10,
      high_primitive_ten_twelve_nonaffine (Or.inl h10) N hhigh⟩
  · by_cases hp : MulAction.IsPreprimitive A X
    · letI : MulAction.IsPreprimitive A X := hp
      exact Or.inr ⟨hp,Or.inr h12,
        high_primitive_ten_twelve_nonaffine (Or.inr h12) N hhigh⟩
    · rcases OriginalMinimalBlock.degreeTwelve_high_imprimitive_structuralOwner_of_sufficientHead
        hChief hWeight  hindex published8 h18 N hp h12 hhigh with hPrime|hNine
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hPrime)))))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hNine)))))
  · have hp : ¬MulAction.IsPreprimitive A X := by
      intro hp
      letI : MulAction.IsPreprimitive A X := hp
      have hh := primitiveTernaryStrictHead_awayFromTenTwelve_of_sufficientHead
         hindex published8 A X (by omega) (by omega) (by omega) (by omega) N
      omega
    exact Or.inl (Or.inl (highDegreeTwentySeven_imprimitive_isPGroup_of_sufficientHead
      hChief  hindex published8 h18 N hp h27 hhigh))

/-- The semantic owner constructs its literal semisimple normal kernel and
faithful quotient comparator at the original width. -/
def TernaryHighPrimitiveSemisimpleOwner.compression_of_sufficientHead
    {A X : Type} [Group A] [Finite A] [Finite X] [MulAction A X]
    [FaithfulSMul A X]
    (h : TernaryHighPrimitiveSemisimpleOwner A X)
    (hindex : SufficientSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification) :
    LocalSemisimpleRoundingCompressionData A (Nat.card X) := by
  letI : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by
    rcases h.2.1 with h10|h12 <;> omega)
  letI : MulAction.IsPreprimitive A X := h.1
  exact (Classical.choice h.2.2).smallNonNineRoundingCompression_of_sufficient hindex published8
    (by rcases h.2.1 with h|h <;> omega)
    (by rcases h.2.1 with h|h <;> omega)
    (by rcases h.2.1 with h|h <;> omega)

end SymmetricSubgroupAsymptotics
