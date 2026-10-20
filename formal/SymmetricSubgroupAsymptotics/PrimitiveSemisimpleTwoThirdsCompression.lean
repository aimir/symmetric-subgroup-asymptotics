import SymmetricSubgroupAsymptotics.PrimitiveOneFactorTwoThirdsOrder
import SymmetricSubgroupAsymptotics.LocalSemisimpleMarginCompression
import SymmetricSubgroupAsymptotics.PrimitiveOuterOrderNumerics

/-! Full primitive semisimple compression with a sufficient two-thirds
margin, using the actual full socle and actual quotient action. The old
half-degree bound and116-row correspondence are not asserted. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open OuterWreathPermutationCompression
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [Nontrivial X] [MulAction.IsPreprimitive G X]

omit [FaithfulSMul G X] [Nontrivial X] [MulAction.IsPreprimitive G X] in
theorem NonaffineData.degree_five_le_of_simpleIndex
    (D : NonaffineData G X) (hindex : PublishedSimpleIndexBounds) : 5≤Nat.card X := by
  obtain ⟨ell,hell⟩ := exists_leastProperIndex D.Simple
  have hf : 5≤ell := nonabelianSimple_leastProperIndex_five_le
    (fun h => D.noncommutative (isMulCommutative_iff.mpr h)) hell.1
  have horder := (hindex D.Simple D.noncommutative ell hell).1
  have hdegree := primitiveSocle_power_le_degree hf horder (D.degreeForm hell)
  have hp : ell≤ell^D.factorCount := by
    simpa only [pow_one] using (pow_le_pow_right₀ (by omega : 1≤ell)
      (show 1≤D.factorCount by have := D.factorCount_pos; omega))
  omega

theorem NonaffineData.oneFactor_twoThirds_quotient_bound
    (D : NonaffineData G X) (hk : D.factorCount=1)
    (catalogue : PublishedPrimitiveCompositionCatalogueCorrespondence)
    (published8 : DegreeEightCanonicalCatalogue.PublishedClassification)
    (published16 : PrimitiveSixteenCanonicalCatalogue.PublishedClassification)
    (hindex : PublishedSimpleIndexBounds) (hf : 5≤Nat.card X) :
    3*Nat.card (G⧸finiteGroupSocle G)≤2*Nat.card X := by
  obtain ⟨ell,_,hfive,helln,hlog⟩ := D.oneFactor_quotient_log_bound hk hindex
  by_cases hlarge : 30≤ell
  · have h := primitive_outerOrder_large_simple_bound ell
      (Nat.card (G⧸finiteGroupSocle G)) hlarge hlog
    omega
  · have hq := quotient_order_lt_fifteen_of_log (by omega) (by omega) hlog
    by_cases hs : Nat.card X<30
    · exact D.oneFactor_twoThirds_quotient_bound_under_thirty hk
        catalogue published8 published16 hindex hf hs
    · omega

/-- Construct the actual local compression datum on every primitive
nonaffine action. Multiple factors keep the standard compressed outer-wreath
action; one factor keeps the regular action of its literal socle quotient. -/
def NonaffineData.twoThirdsCompression
    (D : NonaffineData G X)
    (catalogue : PublishedPrimitiveCompositionCatalogueCorrespondence)
    (published8 : DegreeEightCanonicalCatalogue.PublishedClassification)
    (published16 : PrimitiveSixteenCanonicalCatalogue.PublishedClassification)
    (hindex : PublishedSimpleIndexBounds) (hf : 5≤Nat.card X) :
    LocalSemisimpleTwoThirdsCompressionData G (Nat.card X) := by
  by_cases hk : D.factorCount=1
  · exact {
      E := finiteGroupSocle G
      chart := D.chart
      quotientDegree := Nat.card (G⧸finiteGroupSocle G)
      quotientDegree_pos := Nat.card_pos
      quotientAction := regularAction (G⧸finiteGroupSocle G)
      quotientAction_injective := regularAction_injective (G⧸finiteGroupSocle G)
      quotientDegree_small := D.oneFactor_twoThirds_quotient_bound hk
        catalogue published8 published16 hindex hf }
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
    have hf5 : 5≤ell := nonabelianSimple_leastProperIndex_five_le
      (fun h => D.noncommutative (isMulCommutative_iff.mpr h)) hell.1
    obtain ⟨horder,houter⟩ := hindex D.Simple D.noncommutative ell hell
    have hbase := primitive_outerOrder_square_bound ell (Nat.card (Outer D.Simple)) hf5 houter
    have hm : 2≤D.factorCount := by have := D.factorCount_pos; omega
    have hdegree := primitiveSocle_power_le_degree hf5 horder (D.degreeForm hell)
    have hcomp := primitiveSocle_degree_le_power hm (by omega : 2≤ell) hbase
    omega

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
