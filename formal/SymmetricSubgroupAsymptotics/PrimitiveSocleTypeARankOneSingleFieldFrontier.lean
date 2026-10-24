import SymmetricSubgroupAsymptotics.PrimitiveSocleTypeARankOneTwoFieldFrontier
import SymmetricSubgroupAsymptotics.CFSGPSLTwoCardFiveAlternatingEquiv

/-! Both original field-order4 and field-order5 rank-one models are
identified with A5 and use its complete all-degree consumer. The sole
remaining rank-one field order is9; higher A ranks are unchanged. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X]

theorem NonaffineData.subnormal_class_cube_le_of_typeA_rank_one_card_five
    (D : NonaffineData G X) (q : CFSG.PrimePower) (hq : q.order=5)
    (e : D.Simple ≃* CFSG.Models.A 1 q) (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  letI : IsSimpleGroup (CFSG.Models.A 1 q) := e.symm.isSimpleGroup
  let E := CFSGPSLTwoCardFiveAlternatingEquiv.equivAlternatingFive
    (F:=q.Field) (by simpa only [q.card_field] using hq)
  exact D.subnormal_class_cube_le_of_alternating_all_degrees 5 (by decide) (e.trans E) H hH

theorem NonaffineData.subnormal_class_cube_or_typeA_single_field_parameters
    (D : NonaffineData G X) (r : ℕ) (hr : 1≤r) (q : CFSG.PrimePower)
    (hsmall : r=1→4≤q.order) (e : D.Simple ≃* CFSG.Models.A r q)
    (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3≤5^(Nat.card X-1) ∨
      (r=1 ∧ q.order=9) ∨ (r=2 ∧ q.order≤6) ∨
      (r=3 ∧ q.order≤3) ∨ (4≤r ∧ r≤6 ∧ q.order=2) := by
  rcases D.subnormal_class_cube_or_typeA_two_field_parameters r hr q hsmall e H hH with hc|hp
  · exact Or.inl hc
  · rcases hp with ⟨hrone,hq⟩|hother
    · subst r
      rcases hq with hfive|hnine
      · exact Or.inl (D.subnormal_class_cube_le_of_typeA_rank_one_card_five q hfive e H hH)
      · exact Or.inr (Or.inl ⟨rfl,hnine⟩)
    · exact Or.inr (Or.inr hother)

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
