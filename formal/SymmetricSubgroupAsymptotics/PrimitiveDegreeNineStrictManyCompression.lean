import SymmetricSubgroupAsymptotics.PrimitiveDegreeNineQuotientPointTransport
import SymmetricSubgroupAsymptotics.LocalSemisimpleStrictManyCompression

/-! The actual degree-nine full socle has a faithful quotient action of
degree at most eight. This strict local reduction supplies the original
minimal-block compression whenever the original action has at least two
blocks, without any local parity loss or primitive catalogue. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure

def NonaffineData.degreeNine_strictCompression
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] (D : NonaffineData G X) (hX : Nat.card X = 9)
    (hindex : PublishedSimpleIndexBounds) :
    LocalSemisimpleStrictCompressionData G (Nat.card X) where
  E := finiteGroupSocle G
  chart := D.chart
  quotientDegree := Nat.card (G ⧸ finiteGroupSocle G)
  quotientDegree_pos := Nat.card_pos
  quotientAction := OuterWreathPermutationCompression.regularAction _
  quotientAction_injective := OuterWreathPermutationCompression.regularAction_injective _
  degree_bound := by rw [hX]; decide
  quotientDegree_gap := by
    have hq := D.degreeNine_quotient_card_le_eight_of_card hX hindex
    rw [hX]
    omega

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
