import SymmetricSubgroupAsymptotics.PrimitiveDegreeSevenSocleQuotient
import SymmetricSubgroupAsymptotics.CoprimeCosetPermutationCompression
import SymmetricSubgroupAsymptotics.PrimitiveSmallSocleSingleFactor
import SymmetricSubgroupAsymptotics.PrimitiveOuterOrderRoundingGap
import SymmetricSubgroupAsymptotics.LocalSemisimpleRoundingCompression

/-! The actual degree-seven and degree-eleven semisimple quotients admit
strict rounding compression. The boundary orders6 and10 use disjoint
coprime coset actions of degrees5 and7, respectively. No small abstract
group model or primitive correspondence is supplied. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open OuterWreathPermutationCompression

variable {G : Type} [Group G] [Finite G]

def NonaffineData.degreeSeven_roundingCompression [MulAction G (Fin 7)]
    [FaithfulSMul G (Fin 7)] (D : NonaffineData G (Fin 7)) :
    LocalSemisimpleRoundingCompressionData G 7 := by
  apply Classical.choice
  have hq := D.degreeSeven_quotient_card_le_six
  by_cases h6 : Nat.card (G ⧸ finiteGroupSocle G) = 6
  · obtain ⟨d,hd,hd6,_,f,hf⟩ :=
      CoprimeCosetPermutationCompression.order_six_or_ten_faithful_action (Or.inl h6)
    exact ⟨{
      E := finiteGroupSocle G
      chart := D.chart
      quotientDegree := d
      quotientDegree_pos := hd
      quotientAction := f
      quotientAction_injective := hf
      degree_bound := by decide
      quotientDegree_gap := by rw [hd6 h6]; decide }⟩
  · exact ⟨{
      E := finiteGroupSocle G
      chart := D.chart
      quotientDegree := Nat.card (G ⧸ finiteGroupSocle G)
      quotientDegree_pos := Nat.card_pos
      quotientAction := regularAction _
      quotientAction_injective := regularAction_injective _
      degree_bound := by decide
      quotientDegree_gap := by
        have he : evenWidth 7 = 6 := by decide
        rw [he]
        omega }⟩

theorem NonaffineData.degreeEleven_quotient_card_le_ten [MulAction G (Fin 11)]
    (D : NonaffineData G (Fin 11)) (hindex : PublishedSimpleIndexBounds) :
    Nat.card (G ⧸ finiteGroupSocle G) ≤ 10 := by
  have hk := D.factorCount_one_of_degree_lt_twentyFive hindex (by simp)
  obtain ⟨ell,_,hf,he,hlog⟩ := D.oneFactor_quotient_log_bound hk hindex
  have hpow := quotientOrder_twoPow_le_cube_of_log (by omega) hlog
  have he' : ell ≤ 11 := by simpa only [Nat.card_fin] using he
  have hcube : 2 ^ Nat.card (G ⧸ finiteGroupSocle G) ≤ 1331 :=
    hpow.trans (Nat.pow_le_pow_left he' 3)
  by_contra h
  have hlo : 11 ≤ Nat.card (G ⧸ finiteGroupSocle G) := by omega
  have hbad : 2048 ≤ 1331 := calc
    2048 = 2 ^ 11 := by decide
    _ ≤ 2 ^ Nat.card (G ⧸ finiteGroupSocle G) :=
      pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) hlo
    _ ≤ 1331 := hcube
  omega

def NonaffineData.degreeEleven_roundingCompression [MulAction G (Fin 11)]
    (D : NonaffineData G (Fin 11)) (hindex : PublishedSimpleIndexBounds) :
    LocalSemisimpleRoundingCompressionData G 11 := by
  apply Classical.choice
  have hq := D.degreeEleven_quotient_card_le_ten hindex
  by_cases h10 : Nat.card (G ⧸ finiteGroupSocle G) = 10
  · obtain ⟨d,hd,_,hd10,f,hf⟩ :=
      CoprimeCosetPermutationCompression.order_six_or_ten_faithful_action (Or.inr h10)
    exact ⟨{
      E := finiteGroupSocle G
      chart := D.chart
      quotientDegree := d
      quotientDegree_pos := hd
      quotientAction := f
      quotientAction_injective := hf
      degree_bound := by decide
      quotientDegree_gap := by rw [hd10 h10]; decide }⟩
  · exact ⟨{
      E := finiteGroupSocle G
      chart := D.chart
      quotientDegree := Nat.card (G ⧸ finiteGroupSocle G)
      quotientDegree_pos := Nat.card_pos
      quotientAction := regularAction _
      quotientAction_injective := regularAction_injective _
      degree_bound := by decide
      quotientDegree_gap := by
        have he : evenWidth 11 = 10 := by decide
        rw [he]
        omega }⟩

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
