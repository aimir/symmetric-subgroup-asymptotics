import SymmetricSubgroupAsymptotics.PrimitiveSocleTypeARankOneThreeFieldFrontier
import SymmetricSubgroupAsymptotics.CFSGPSLTwoCardFourAlternatingEquiv
import SymmetricSubgroupAsymptotics.PrimitiveSocleAlternatingAllDegreesClassBound

/-! The actual four-element-field component is A5, so its complete
alternating consumer removes that field in every original degree and
factor count. Only field orders5 and9 remain in the rank-one branch. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X]

theorem NonaffineData.subnormal_class_cube_le_of_typeA_rank_one_card_four
    (D : NonaffineData G X) (q : CFSG.PrimePower) (hq : q.order=4)
    (e : D.Simple ≃* CFSG.Models.A 1 q) (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  letI : IsSimpleGroup (CFSG.Models.A 1 q) := e.symm.isSimpleGroup
  let E := CFSGPSLTwoCardFourAlternatingEquiv.equivAlternatingFive
    (F:=q.Field) (by simpa only [q.card_field] using hq)
  exact D.subnormal_class_cube_le_of_alternating_all_degrees 5 (by decide) (e.trans E) H hH

theorem NonaffineData.subnormal_class_cube_or_typeA_two_field_parameters
    (D : NonaffineData G X) (r : ℕ) (hr : 1≤r) (q : CFSG.PrimePower)
    (hsmall : r=1→4≤q.order) (e : D.Simple ≃* CFSG.Models.A r q)
    (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3≤5^(Nat.card X-1) ∨
      (r=1 ∧ (q.order=5 ∨ q.order=9)) ∨
      (r=2 ∧ q.order≤6) ∨ (r=3 ∧ q.order≤3) ∨ (4≤r ∧ r≤6 ∧ q.order=2) := by
  rcases D.subnormal_class_cube_or_typeA_three_field_parameters r hr q hsmall e H hH with hc|hp
  · exact Or.inl hc
  · rcases hp with ⟨hrone,hq⟩|hother
    · subst r
      rcases hq with hfour|hsmall
      · exact Or.inl (D.subnormal_class_cube_le_of_typeA_rank_one_card_four q hfour e H hH)
      · exact Or.inr (Or.inl ⟨rfl,hsmall⟩)
    · exact Or.inr (Or.inr hother)

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
