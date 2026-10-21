import SymmetricSubgroupAsymptotics.PrimitiveSemisimpleTwoThirdsCompression

/-! Above degree29 the unchanged logarithmic simple-index estimate
already supplies the sufficient two-thirds quotient margin. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open OuterWreathPermutationCompression

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.oneFactor_twoThirds_quotient_bound_thirty_le
    (D : NonaffineData G X) (hk : D.factorCount=1)
    (hindex : PublishedSimpleIndexBounds) (hr : 30≤Nat.card X) :
    3*Nat.card (G⧸finiteGroupSocle G)≤2*Nat.card X := by
  obtain ⟨ell,_,hf,he,hlog⟩ := D.oneFactor_quotient_log_bound hk hindex
  by_cases hlarge : 30≤ell
  · have h := primitive_outerOrder_large_simple_bound ell
      (Nat.card (G⧸finiteGroupSocle G)) hlarge hlog
    omega
  · have hq := quotient_order_lt_fifteen_of_log (by omega) (by omega) hlog
    omega

def NonaffineData.largeTwoThirdsCompression
    (D : NonaffineData G X) (hindex : PublishedSimpleIndexBounds)
    (hr : 30≤Nat.card X) :
    LocalSemisimpleTwoThirdsCompressionData G (Nat.card X) := by
  by_cases hk : D.factorCount=1
  · exact {
      E := finiteGroupSocle G
      chart := D.chart
      quotientDegree := Nat.card (G⧸finiteGroupSocle G)
      quotientDegree_pos := Nat.card_pos
      quotientAction := regularAction _
      quotientAction_injective := regularAction_injective _
      quotientDegree_small := D.oneFactor_twoThirds_quotient_bound_thirty_le hk hindex hr }
  · refine {
      E := finiteGroupSocle G
      chart := D.chart
      quotientDegree := D.factorCount*Nat.card (Outer D.Simple)
      quotientDegree_pos := Nat.mul_pos D.factorCount_pos Nat.card_pos
      quotientAction := compressedAction D.quotientEmbedding
      quotientAction_injective := compressedAction_injective
        D.quotientEmbedding D.quotientEmbedding_injective D.factorCount_pos
      quotientDegree_small := ?_ }
    obtain ⟨ell,hell⟩ := exists_leastProperIndex D.Simple
    have hf : 5≤ell := nonabelianSimple_leastProperIndex_five_le
      (fun h => D.noncommutative (isMulCommutative_iff.mpr h)) hell.1
    obtain ⟨horder,houter⟩ := hindex D.Simple D.noncommutative ell hell
    have hbase := primitive_outerOrder_square_bound ell (Nat.card (Outer D.Simple)) hf houter
    have hm : 2≤D.factorCount := by have := D.factorCount_pos; omega
    have hdegree := primitiveSocle_power_le_degree hf horder (D.degreeForm hell)
    have hcomp := primitiveSocle_degree_le_power hm (by omega : 2≤ell) hbase
    omega

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
