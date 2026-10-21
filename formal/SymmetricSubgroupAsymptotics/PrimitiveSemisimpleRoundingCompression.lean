import SymmetricSubgroupAsymptotics.PrimitiveOuterOrderRoundingGap
import SymmetricSubgroupAsymptotics.LocalSemisimpleRoundingCompression
import SymmetricSubgroupAsymptotics.PrimitiveOuterOrderNumerics

/-! Actual primitive semisimple compression in degrees12..44 follows from
the ordinary retained simple-index estimate. One factor uses its actual
regular quotient action; multiple factors keep the existing compressed
outer-wreath action. No bounded primitive correspondence occurs. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics

/-- The old half-degree bound automatically leaves the new positive
rounding margin, including odd original widths. -/
theorem roundingGap_of_halfDegree {r q : ℕ} (hr : 5≤r) (hq : 2*q≤r) :
    max 2 q+1≤evenWidth r := by
  have he := width_le_evenWidth_add_one r
  omega

namespace PrimitiveSocleRawStructure
open OuterWreathPermutationCompression

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

def NonaffineData.roundingCompression_twelveToFortyFour
    (D : NonaffineData G X) (hindex : PublishedSimpleIndexBounds)
    (hr : 12≤Nat.card X) (h44 : Nat.card X≤44) :
    LocalSemisimpleRoundingCompressionData G (Nat.card X) := by
  by_cases hk : D.factorCount=1
  · exact {
      E := finiteGroupSocle G
      chart := D.chart
      quotientDegree := Nat.card (G⧸finiteGroupSocle G)
      quotientDegree_pos := Nat.card_pos
      quotientAction := regularAction (G⧸finiteGroupSocle G)
      quotientAction_injective := regularAction_injective (G⧸finiteGroupSocle G)
      degree_bound := by omega
      quotientDegree_gap := D.oneFactor_roundingGap_twelveToFortyFour hk hindex hr h44 }
  · refine {
      E := finiteGroupSocle G
      chart := D.chart
      quotientDegree := D.factorCount*Nat.card (Outer D.Simple)
      quotientDegree_pos := Nat.mul_pos D.factorCount_pos Nat.card_pos
      quotientAction := compressedAction D.quotientEmbedding
      quotientAction_injective := compressedAction_injective
        D.quotientEmbedding D.quotientEmbedding_injective D.factorCount_pos
      degree_bound := by omega
      quotientDegree_gap := ?_ }
    apply roundingGap_of_halfDegree (by omega : 5≤Nat.card X)
    obtain ⟨ell,hell⟩ := exists_leastProperIndex D.Simple
    have hf : 5≤ell := nonabelianSimple_leastProperIndex_five_le
      (fun h => D.noncommutative (isMulCommutative_iff.mpr h)) hell.1
    obtain ⟨horder,houter⟩ := hindex D.Simple D.noncommutative ell hell
    have hbase := primitive_outerOrder_square_bound ell (Nat.card (Outer D.Simple)) hf houter
    have hm : 2≤D.factorCount := by have hp:=D.factorCount_pos;omega
    exact (primitiveSocle_degree_le_power hm (by omega : 2≤ell) hbase).trans
      (primitiveSocle_power_le_degree hf horder (D.degreeForm hell))

end PrimitiveSocleRawStructure
end SymmetricSubgroupAsymptotics
