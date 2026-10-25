import SymmetricSubgroupAsymptotics.PrimitiveSocleHigherAProperClassPackets
import SymmetricSubgroupAsymptotics.PrimitiveSoclePSLTwoAllProperSubnormalClassGap
import SymmetricSubgroupAsymptotics.PrimitiveSoclePSLThreeProperSubnormalClassGap

/-! Every admissible original type-A simple model pays the proper
subnormal extra exponent. The literal rank/field split reuses the same
proved packets; actual subgroup and both degree forms remain intact. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X]

theorem NonaffineData.proper_subnormal_class_cube_le_of_typeA_all_fields
    (D : NonaffineData G X) (r : ℕ) (hr : 1 ≤ r) (q : CFSG.PrimePower)
    (hsmall : r=1 → 4 ≤ q.order) (e : D.Simple ≃* CFSG.Models.A r q)
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
  by_cases hrone : r=1
  · subst r
    exact D.proper_subnormal_class_cube_le_of_pslTwo_all_fields q (hsmall rfl) e H hH hne
  by_cases hrtwo : r=2
  · subst r
    exact D.proper_subnormal_class_cube_le_of_pslThree_all_fields q e H hH hne
  have hrthree : 3 ≤ r := by omega
  by_cases hcapacity : 7 ≤ q.order ∨ (4 ≤ q.order ∧ 3 ≤ r) ∨
      (3 ≤ q.order ∧ 4 ≤ r) ∨ 7 ≤ r
  · exact D.proper_subnormal_class_cube_le_of_typeA_capacity
      r (by omega) q e hcapacity H hH hne
  have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow q.exponent_pos.ne' q.prime)
  have hrest : (r=3 ∧ (q.order=2 ∨ q.order=3)) ∨
      ((r=4 ∨ r=5 ∨ r=6) ∧ q.order=2) := by omega
  rcases hrest with ⟨rfl, hfield⟩ | ⟨hrank, hfield⟩
  · rcases hfield with htwo | hthree
    · exact D.proper_subnormal_class_cube_le_of_typeA_binary_cyclic
        3 (Or.inl rfl) q htwo e H hH hne
    · exact D.proper_subnormal_class_cube_le_of_typeA_rank_three_card_three q hthree e H hH hne
  · rcases hrank with rfl | rfl | rfl
    · exact D.proper_subnormal_class_cube_le_of_typeA_rank_four_card_two q hfield e H hH hne
    · exact D.proper_subnormal_class_cube_le_of_typeA_binary_cyclic
        5 (Or.inr rfl) q hfield e H hH hne
    · exact D.proper_subnormal_class_cube_le_of_typeA_rank_six_card_two q hfield e H hH hne

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
