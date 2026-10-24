import SymmetricSubgroupAsymptotics.PrimitiveSocleTypeARankOneRefinedClassCubeClassBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleTypeARankOneEvenClassCubeClassBound
import SymmetricSubgroupAsymptotics.RankOneRemainingParameterArithmetic

/-! The same-model rank-one frontier consists only of field orders
4,5,9. Every other order is handled by shared trace/torus budgets,
retaining all socle factors, the exact original subgroup, and both raw
degree forms. Higher-rank A cases are unchanged. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.subnormal_class_cube_or_typeA_three_field_parameters
    (D : NonaffineData G X) (r : ℕ) (hr : 1≤r) (q : CFSG.PrimePower)
    (hsmall : r=1→4≤q.order) (e : D.Simple ≃* CFSG.Models.A r q)
    (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3≤5^(Nat.card X-1) ∨
      (r=1 ∧ (q.order=4 ∨ q.order=5 ∨ q.order=9)) ∨
      (r=2 ∧ q.order≤6) ∨ (r=3 ∧ q.order≤3) ∨ (4≤r ∧ r≤6 ∧ q.order=2) := by
  rcases D.subnormal_class_cube_or_typeA_sharp_class_finite_parameters r hr q e H hH with hc|hp
  · exact Or.inl hc
  · rcases hp with ⟨hrone,hq⟩|hother
    · subst r
      rcases RankOneRemainingParameterArithmetic.field_parameters q (hsmall rfl) hq with
        hexception|heven|hprime|hodd
      · exact Or.inr (Or.inl ⟨rfl,hexception⟩)
      · exact Or.inl (D.subnormal_class_cube_le_of_typeA_rank_one_even_capacity q
          heven.1 heven.2 e H hH)
      · have hqprime : q.order.Prime := by rcases hprime with h|h <;> rw [h] <;> decide
        have hlo : 7≤q.order := by rcases hprime with h|h <;> omega
        have hhi : q.order≤11 := by rcases hprime with h|h <;> omega
        have hmod : q.order%4=3 := by rcases hprime with h|h <;> rw [h] <;> decide
        exact Or.inl (D.subnormal_class_cube_le_of_typeA_rank_one_small_prime_capacity
          q hqprime hlo hhi hmod e H hH)
      · exact Or.inl (D.subnormal_class_cube_le_of_typeA_rank_one_odd_capacity
          q hodd.2 hodd.1 e H hH)
    · exact Or.inr (Or.inr hother)

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
