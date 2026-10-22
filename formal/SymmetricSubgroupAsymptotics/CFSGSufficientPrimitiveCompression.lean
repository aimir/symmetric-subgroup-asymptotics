import SymmetricSubgroupAsymptotics.CFSGSufficientPrimitiveSocleQuotient
import SymmetricSubgroupAsymptotics.PrimitiveSemisimpleRoundingCompression
import SymmetricSubgroupAsymptotics.LocalSemisimpleMarginCompression

/-! Actual nonaffine primitive compression from the sufficient hybrid.
Large components start at64. Components of degrees27..63 use the already
proved rounding-gap source, with exactly the same original full socle and
quotient action. No public T1 interface is changed here. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open OuterWreathPermutationCompression

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.oneFactor_sufficient_twoThirds_tail
    (D : NonaffineData G X) (hk : D.factorCount = 1)
    (hindex : SufficientSimpleIndexBounds) (hr : 64 ≤ Nat.card X) :
    3 * Nat.card (G ⧸ finiteGroupSocle G) ≤ 2 * Nat.card X := by
  obtain ⟨ell, _, hf, he, hb⟩ := D.oneFactor_sufficient_budget hk hindex
  exact CFSGSufficientSimpleIndexNumerics.twoThirds_tail hr
    (hb.log_six_of_le (by omega) he)

theorem NonaffineData.sufficient_multiple_half_degree
    (D : NonaffineData G X) (hk : D.factorCount ≠ 1)
    (hindex : SufficientSimpleIndexBounds) :
    2 * (D.factorCount * Nat.card (Outer D.Simple)) ≤ Nat.card X := by
  obtain ⟨ell, _, hf, hd, hb⟩ := D.sufficient_degree_lower hindex
  have hm : 2 ≤ D.factorCount := by have := D.factorCount_pos; omega
  exact (primitiveSocle_degree_le_power hm (by omega : 2 ≤ ell)
    (hb.square_bound hf)).trans hd

def NonaffineData.sufficientLargeCompression
    (D : NonaffineData G X) (hindex : SufficientSimpleIndexBounds)
    (hr : 64 ≤ Nat.card X) : LocalSemisimpleTwoThirdsCompressionData G (Nat.card X) := by
  by_cases hk : D.factorCount = 1
  · exact {
      E := finiteGroupSocle G
      chart := D.chart
      quotientDegree := Nat.card (G ⧸ finiteGroupSocle G)
      quotientDegree_pos := Nat.card_pos
      quotientAction := regularAction _
      quotientAction_injective := regularAction_injective _
      quotientDegree_small := D.oneFactor_sufficient_twoThirds_tail hk hindex hr }
  · refine {
      E := finiteGroupSocle G
      chart := D.chart
      quotientDegree := D.factorCount * Nat.card (Outer D.Simple)
      quotientDegree_pos := Nat.mul_pos D.factorCount_pos Nat.card_pos
      quotientAction := compressedAction D.quotientEmbedding
      quotientAction_injective := compressedAction_injective
        D.quotientEmbedding D.quotientEmbedding_injective D.factorCount_pos
      quotientDegree_small := ?_ }
    have hh := D.sufficient_multiple_half_degree hk hindex
    omega

def NonaffineData.sufficientRoundingCompression_twentySevenToSixtyThree
    (D : NonaffineData G X) (hindex : SufficientSimpleIndexBounds)
    (hr : 27 ≤ Nat.card X) (h63 : Nat.card X ≤ 63) :
    LocalSemisimpleRoundingCompressionData G (Nat.card X) := by
  apply Classical.choice
  by_cases hk : D.factorCount = 1
  · obtain ⟨ell, _, hf, he, hb⟩ := D.oneFactor_sufficient_budget hk hindex
    exact ⟨{
      E := finiteGroupSocle G
      chart := D.chart
      quotientDegree := Nat.card (G ⧸ finiteGroupSocle G)
      quotientDegree_pos := Nat.card_pos
      quotientAction := regularAction _
      quotientAction_injective := regularAction_injective _
      degree_bound := by omega
      quotientDegree_gap := hb.rounding_gap (by omega) he hr h63 }⟩
  · refine ⟨{
      E := finiteGroupSocle G
      chart := D.chart
      quotientDegree := D.factorCount * Nat.card (Outer D.Simple)
      quotientDegree_pos := Nat.mul_pos D.factorCount_pos Nat.card_pos
      quotientAction := compressedAction D.quotientEmbedding
      quotientAction_injective := compressedAction_injective
        D.quotientEmbedding D.quotientEmbedding_injective D.factorCount_pos
      degree_bound := by omega
      quotientDegree_gap := ?_ }⟩
    exact roundingGap_of_halfDegree (by omega) (D.sufficient_multiple_half_degree hk hindex)

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
