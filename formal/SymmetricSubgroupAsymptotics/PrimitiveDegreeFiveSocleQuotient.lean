import SymmetricSubgroupAsymptotics.PrimitiveSmallSocleSingleFactor
import SymmetricSubgroupAsymptotics.PerfectSmallPermutationEmbedding
import SymmetricSubgroupAsymptotics.PrimitiveSemisimpleRoundingCompression
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawOneFactor

/-! A nonaffine faithful primitive five-point action has actual full
socle order60, and actual socle quotient order at most two. The proof uses
the sign, Lagrange and the retained ordinary simple-index inequality. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure

private theorem fivePoint_simpleOrder_receipt :
    ∀ n : Fin 61, n.val ∣ 60 → 25 < n.val → n.val = 30 ∨ n.val = 60 := by
  decide +kernel

variable {G : Type} [Group G] [Finite G] [MulAction G (Fin 5)]
    [FaithfulSMul G (Fin 5)]

theorem NonaffineData.degreeFive_socle_card
    (D : NonaffineData G (Fin 5)) (hindex : PublishedSimpleIndexBounds) :
    Nat.card (finiteGroupSocle G) = 60 := by
  have hk := D.factorCount_one_of_degree_lt_twentyFive hindex (by simp)
  let S := finiteGroupSocle G
  let e : S ≃* D.Simple := D.oneFactorEquiv hk
  letI : IsSimpleGroup S := e.isSimpleGroup
  have hnc : ¬IsMulCommutative S := by
    intro hs
    apply D.noncommutative
    apply IsMulCommutative.of_comm
    intro a b
    have hh := congrArg e (hs.is_comm.comm (e.symm a) (e.symm b))
    simpa only [map_mul,e.apply_symm_apply] using hh
  letI : Group.IsPerfect S := simple_perfect_of_nonabelian hnc
  let j := perfectPermutationToAlternating (MulAction.toPermHom S (Fin 5))
  have hj : Function.Injective j := perfectPermutationToAlternating_injective _
    (show Function.Injective (MulAction.toPermHom S (Fin 5)) from
      MulAction.toPerm_injective)
  let H := j.range
  have hH : Nat.card H = Nat.card S :=
    (Nat.card_congr (MonoidHom.ofInjective hj).toEquiv).symm
  have hA : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup,Nat.card_fin]
    decide
  have hd : Nat.card S ∣ 60 := by
    have h := H.card_subgroup_dvd_card
    simpa only [hH,hA] using h
  obtain ⟨ell,hell⟩ := exists_leastProperIndex S
  have hf : 5 ≤ ell := nonabelianSimple_leastProperIndex_five_le
    (fun hc => hnc (isMulCommutative_iff.mpr hc)) hell.1
  have hb := (hindex S hnc ell hell).1
  have h25 : 25 < Nat.card S :=
    (Nat.pow_le_pow_left hf 2).trans_lt hb
  have hle : Nat.card S ≤ 60 := Nat.le_of_dvd (by decide) hd
  rcases fivePoint_simpleOrder_receipt ⟨Nat.card S,by omega⟩ hd h25 with ht | ht
  · exact (nonabelianSimple_card_ne_thirty hnc hindex ht).elim
  · exact ht

theorem NonaffineData.degreeFive_quotient_card_le_two
    (D : NonaffineData G (Fin 5)) (hindex : PublishedSimpleIndexBounds) :
    Nat.card (G ⧸ finiteGroupSocle G) ≤ 2 := by
  have hG : Nat.card G ≤ 120 := by
    have hi := Nat.card_le_card_of_injective (MulAction.toPermHom G (Fin 5))
      (show Function.Injective (MulAction.toPermHom G (Fin 5)) from
        MulAction.toPerm_injective)
    simpa only [Nat.card_perm,Nat.card_fin] using hi
  have hm := (finiteGroupSocle G).card_mul_index
  rw [D.degreeFive_socle_card hindex,Subgroup.index_eq_card] at hm
  omega

def NonaffineData.degreeFive_roundingCompression
    (D : NonaffineData G (Fin 5)) (hindex : PublishedSimpleIndexBounds) :
    LocalSemisimpleRoundingCompressionData G 5 where
  E := finiteGroupSocle G
  chart := D.chart
  quotientDegree := Nat.card (G ⧸ finiteGroupSocle G)
  quotientDegree_pos := Nat.card_pos
  quotientAction := OuterWreathPermutationCompression.regularAction _
  quotientAction_injective := OuterWreathPermutationCompression.regularAction_injective _
  degree_bound := by decide
  quotientDegree_gap := by
    have hq := D.degreeFive_quotient_card_le_two hindex
    rw [max_eq_left hq]
    decide

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
