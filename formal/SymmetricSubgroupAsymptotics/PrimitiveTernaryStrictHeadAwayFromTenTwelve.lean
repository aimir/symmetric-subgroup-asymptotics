import SymmetricSubgroupAsymptotics.PrimitiveSmallSemisimpleStrictHeadWithoutCatalogue
import SymmetricSubgroupAsymptotics.PrimitiveAffineSmallTernaryConsumers
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawONanScottProof
import SymmetricSubgroupAsymptotics.PrimitiveTernaryStrictHeadPublished
import SymmetricSubgroupAsymptotics.PrimitiveSemisimpleTwoThirdsCompression

/-! The complete strict-head consumer away from the two remaining
small nonaffine degrees10/12. This is a proved range reduction, not a new
published assumption or a claim that either remaining case is closed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
open PrimitiveSocleRawStructure
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

theorem primitiveTernaryStrictHead_awayFromTenTwelve_without_catalogue
    (hgen : PrimitiveNormalGeneratorInput) (hindex : PublishedSimpleIndexBounds)
    (published8 : DegreeEightCanonicalCatalogue.PublishedClassification)
    (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [MulAction.IsPreprimitive G X] [Nontrivial X]
    (h3 : Nat.card X≠3) (h4 : Nat.card X≠4)
    (h10 : Nat.card X≠10) (h12 : Nat.card X≠12)
    (N : Subgroup G) [N.Normal] :
    20*Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)<3*Nat.card X := by
  by_cases hlarge : 34≤Nat.card X
  · exact c1_primitive_relative_tail_faithful hgen hlarge N
  cases Classical.choice (publishedONanScottStructure G X) with
  | inr P =>
      exact P.small_ternaryRelativeHead_strict inferInstance (by omega) h3 h4 N
  | inl D =>
      by_cases h14 : 14≤Nat.card X
      · exact D.ternaryHead_strict_fourteenToThirtyThree hindex h14 (by omega) N
      · exact D.ternaryHead_strict_fiveToThirteen_except_ten_twelve hindex published8
          (D.degree_five_le_of_simpleIndex hindex) (by omega) h10 h12 N

end SymmetricSubgroupAsymptotics
