import SymmetricSubgroupAsymptotics.NonabelianEightSocleOne
import SymmetricSubgroupAsymptotics.MonolithicCompleteQuotientReduction
import SymmetricSubgroupAsymptotics.OuterWreathPermutationCompression

/-! A nonabelian order-eight target has a literal central monolith of
order two. Its complete original quotient weight is bounded by the
complete weight of its actual order-four central quotient, plus the
onto-map term to the original group. No proper quotient axis is dropped. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics.NonabelianEightCompleteQuotientReduction

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {G : Type} [Group G] [Finite G]

theorem center_card (hG : Nat.card G = 8) (hnc : ¬IsMulCommutative G) :
    Nat.card (Subgroup.center G) = 2 := by
  have hP : IsPGroup 2 G := IsPGroup.of_card (n := 3) (by simpa using hG)
  letI : Nontrivial G := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  letI : Nontrivial (Subgroup.center G) := hP.center_nontrivial
  have hlo : 1 < Nat.card (Subgroup.center G) := Finite.one_lt_card
  have hhi := nonabelian_cardEight_center_card_le_two hG hnc
  omega

theorem center_le_nonzero_normal (hG : Nat.card G = 8)
    (hnc : ¬IsMulCommutative G) (N : Subgroup G) [N.Normal]
    (hN : N ≠ ⊥) : Subgroup.center G ≤ N := by
  have hP : IsPGroup 2 G := IsPGroup.of_card (n := 3) (by simpa using hG)
  letI : IsSimpleGroup (Subgroup.center G) :=
    isSimpleGroup_of_prime_card (p := 2) (center_card hG hnc)
  obtain ⟨z,hzN,hzC,hzo⟩ := pGroup_normal_contains_central_prime hP N hN
  have hz : z ≠ 1 := by
    intro he
    rw [he,orderOf_one] at hzo
    omega
  have hmeet : N ⊓ Subgroup.center G ≠ ⊥ := by
    intro he
    have hm : z ∈ N ⊓ Subgroup.center G := ⟨hzN,hzC⟩
    rw [he,Subgroup.mem_bot] at hm
    exact hz hm
  have hc := (Subgroup.isSimpleGroup_iff.mp
    (inferInstance : IsSimpleGroup (Subgroup.center G))).2
    (N ⊓ Subgroup.center G) inf_le_right
    (show ((N ⊓ Subgroup.center G).subgroupOf (Subgroup.center G)).Normal from
      inferInstance)
  rcases hc with hb | ht
  · exact (hmeet hb).elim
  · exact ht.symm.le.trans inf_le_left

theorem central_quotient_card (hG : Nat.card G = 8)
    (hnc : ¬IsMulCommutative G) : Nat.card (G ⧸ Subgroup.center G) = 4 := by
  have hm := (Subgroup.center G).card_mul_index
  rw [center_card hG hnc,hG,Subgroup.index_eq_card] at hm
  omega

theorem central_quotient_permutation_four (hG : Nat.card G = 8)
    (hnc : ¬IsMulCommutative G) :
    ∃ d : ℕ, 0 < d ∧ d ≤ 4 ∧
      ∃ f : (G ⧸ Subgroup.center G) →* Equiv.Perm (Fin d),
        Function.Injective f := by
  refine ⟨Nat.card (G ⧸ Subgroup.center G),Nat.card_pos,?_,
    OuterWreathPermutationCompression.regularAction _,
    OuterWreathPermutationCompression.regularAction_injective _⟩
  exact (central_quotient_card hG hnc).le

theorem complete_weight_le (hG : Nat.card G = 8)
    (hnc : ¬IsMulCommutative G) {b : ℕ}
    (J : Subgroup (Equiv.Perm (Fin b))) :
    completeQuotientWeight (R := G) J ≤
      (Nat.card (GroupEpimorphism J G) : ℝ) +
        completeQuotientWeight (R := G ⧸ Subgroup.center G) J :=
  MonolithicCompleteQuotientReduction.complete_weight_le (Subgroup.center G)
    (center_le_nonzero_normal hG hnc) J

theorem complete_weight_le_character_tail (hG : Nat.card G = 8)
    (hnc : ¬IsMulCommutative G) (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) {b : ℕ}
    (J : Subgroup (Equiv.Perm (Fin b))) :
    completeQuotientWeight (R := G) J ≤
      (Nat.card (G ≃* G) : ℝ) *
        (2 : ℝ) ^ ((Real.logb 2 5 / 3) * (b : ℝ)) +
      completeQuotientWeight (R := G ⧸ Subgroup.center G) J := by
  have he := (hZmud.generalCertificate
    (socleNormalGeneratorBound_one_of_nonabelian_cardEight hG hnc)).envelope lit b J
  simp only [ZmudFaithfulCharacterTupleInput.generalCertificate_slope,
    Nat.cast_one,one_mul] at he
  exact (complete_weight_le hG hnc J).trans (add_le_add he le_rfl)

end SymmetricSubgroupAsymptotics.NonabelianEightCompleteQuotientReduction
