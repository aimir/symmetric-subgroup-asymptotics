import SymmetricSubgroupAsymptotics.TernaryRelaxedHighActionDegrees
import SymmetricSubgroupAsymptotics.TernaryDegreeTwentySevenReductionWithoutCatalogue
import SymmetricSubgroupAsymptotics.DegreeSixHighStructuralOwnerWithoutCatalogue
import SymmetricSubgroupAsymptotics.DegreeTwelveImprimitiveStructuralOwnerWithoutCatalogue
import SymmetricSubgroupAsymptotics.PrimitiveSmallNonNineRoundingCompression

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
def TernaryHighPrimitiveSemisimpleOwner (A X : Type) [Group A] [Finite A]
    [Finite X] [MulAction A X] : Prop :=
  MulAction.IsPreprimitive A X ∧ (Nat.card X=10 ∨ Nat.card X=12) ∧
    Nonempty (NonaffineData A X)

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
theorem ternaryHigh_earlierOwner_or_semisimple_without_catalogue
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r/3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hgen : PrimitiveNormalGeneratorInput) (hindex : PublishedSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    {A X : Type} [Group A] [Finite A] [Finite X] [MulAction A X]
    [FaithfulSMul A X] [MulAction.IsPretransitive A X]
    (N : Subgroup A) [N.Normal]
    (hhigh : 3*Nat.card X<20*Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)) :
    TernaryHighEarlierOwner A X ∨ TernaryHighPrimitiveSemisimpleOwner A X := by
  have hdegree := ternaryHigh_action_degree_menu_without_catalogue
    hChief hWeight hgen hindex published8 h18 N hhigh
  have htwo : 2≤Nat.card X := by
    rcases hdegree with h|h|h|h|h|h|h <;> omega
  letI : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp htwo
  have htop := transitiveTernaryHead_relaxed_stability_without_catalogue
    hChief hgen hindex published8 h18 (X := X) N
  rcases hdegree with h3|h4|h6|h9|h10|h12|h27
  · exact Or.inl (Or.inl (degreeThree_rankOne_isPGroup h3 N (by
      norm_num [h3,ternaryRelaxedStabilityBound,ternaryStabilityBound] at htop hhigh
      omega)))
  · exact Or.inl (Or.inr (Or.inl (degreeFour_rankOne_isNaturalA4 h4 N (by
      norm_num [h4,ternaryRelaxedStabilityBound,ternaryStabilityBound] at htop hhigh
      omega))))
  · rcases degreeSix_high_structuralOwner_without_catalogue
      hgen hindex published8 N h6 hhigh with hOdd|hCyclic
    · exact Or.inl (Or.inr (Or.inr (Or.inl hOdd)))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl hCyclic))))
  · exact Or.inl (Or.inl (degreeNine_rankTwo_isPGroup_without_catalogue
      hChief hgen hindex published8 h18 N h9 (by
        norm_num [h9,ternaryRelaxedStabilityBound,ternaryStabilityBound] at htop hhigh
        omega)))
  · have hp : MulAction.IsPreprimitive A X := by
      by_contra hnp
      have hh := ternaryHigh_imprimitive_degree_menu_without_catalogue
        hChief hWeight hgen hindex published8 h18 N hnp hhigh
      rcases hh with h|h|h|h|h <;> omega
    letI : MulAction.IsPreprimitive A X := hp
    exact Or.inr ⟨hp,Or.inl h10,
      high_primitive_ten_twelve_nonaffine (Or.inl h10) N hhigh⟩
  · by_cases hp : MulAction.IsPreprimitive A X
    · letI : MulAction.IsPreprimitive A X := hp
      exact Or.inr ⟨hp,Or.inr h12,
        high_primitive_ten_twelve_nonaffine (Or.inr h12) N hhigh⟩
    · rcases OriginalMinimalBlock.degreeTwelve_high_imprimitive_structuralOwner_without_catalogue
        hChief hWeight hgen hindex published8 h18 N hp h12 hhigh with hPrime|hNine
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hPrime)))))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hNine)))))
  · have hp : ¬MulAction.IsPreprimitive A X := by
      intro hp
      letI : MulAction.IsPreprimitive A X := hp
      have hh := primitiveTernaryStrictHead_awayFromTenTwelve_without_catalogue
        hgen hindex published8 A X (by omega) (by omega) (by omega) (by omega) N
      omega
    exact Or.inl (Or.inl (highDegreeTwentySeven_imprimitive_isPGroup_without_catalogue
      hChief hgen hindex published8 h18 N hp h27 hhigh))

/-- The semantic owner constructs its literal semisimple normal kernel and
faithful quotient comparator at the original width. -/
def TernaryHighPrimitiveSemisimpleOwner.compression
    {A X : Type} [Group A] [Finite A] [Finite X] [MulAction A X]
    [FaithfulSMul A X]
    (h : TernaryHighPrimitiveSemisimpleOwner A X)
    (hindex : PublishedSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification) :
    LocalSemisimpleRoundingCompressionData A (Nat.card X) := by
  letI : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by
    rcases h.2.1 with h10|h12 <;> omega)
  letI : MulAction.IsPreprimitive A X := h.1
  exact (Classical.choice h.2.2).smallNonNineRoundingCompression hindex published8
    (by rcases h.2.1 with h|h <;> omega)
    (by rcases h.2.1 with h|h <;> omega)
    (by rcases h.2.1 with h|h <;> omega)

end SymmetricSubgroupAsymptotics
