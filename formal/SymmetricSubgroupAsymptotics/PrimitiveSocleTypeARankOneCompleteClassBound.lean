import SymmetricSubgroupAsymptotics.PrimitiveSocleTypeARankOneSingleFieldFrontier
import SymmetricSubgroupAsymptotics.CFSGTypeARankOneCardNine
import SymmetricSubgroupAsymptotics.PrimitiveSocleOrderThreeSixtyClassBound

/-! The complete rank-one A primitive class bound, uniform in every
field, every original degree and socle factor count. The final field
uses proved literal order-360 data and index-gap recognition; no
exceptional-isomorphism premise or finite action census is introduced. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X]

theorem NonaffineData.subnormal_class_cube_le_of_typeA_rank_one_card_nine
    (D : NonaffineData G X) (q : CFSG.PrimePower) (hq : q.order=9)
    (e : D.Simple ≃* CFSG.Models.A 1 q) (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  refine D.subnormal_class_cube_le_of_order_three_sixty ?_ ?_ ?_ H hH
  · rw [Nat.card_congr e.toEquiv]
    exact CFSGTypeARankOneCardNine.card_eq q hq
  · have hc : Nat.card (ConjClasses D.Simple) ≤ Nat.card (ConjClasses (CFSG.Models.A 1 q)) :=
      Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
        (ConjClasses.map_surjective e.symm.surjective)
    exact hc.trans (CFSGTypeARankOneCardNine.class_card_le q hq)
  · rw [CFSGReduction.outer_card_congr e]
    exact CFSGTypeARankOneCardNine.outer_card_le q hq

theorem NonaffineData.subnormal_class_cube_or_typeA_higher_rank_parameters
    (D : NonaffineData G X) (r : ℕ) (hr : 1≤r) (q : CFSG.PrimePower)
    (hsmall : r=1→4≤q.order) (e : D.Simple ≃* CFSG.Models.A r q)
    (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3≤5^(Nat.card X-1) ∨
      (r=2 ∧ q.order≤6) ∨ (r=3 ∧ q.order≤3) ∨ (4≤r ∧ r≤6 ∧ q.order=2) := by
  rcases D.subnormal_class_cube_or_typeA_single_field_parameters r hr q hsmall e H hH with hc|hp
  · exact Or.inl hc
  · rcases hp with ⟨hrone,hq⟩|hother
    · subst r
      exact Or.inl (D.subnormal_class_cube_le_of_typeA_rank_one_card_nine q hq e H hH)
    · exact Or.inr hother

theorem NonaffineData.subnormal_class_cube_le_of_typeA_rank_one_all_fields
    (D : NonaffineData G X) (q : CFSG.PrimePower) (hq : 4≤q.order)
    (e : D.Simple ≃* CFSG.Models.A 1 q) (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3≤5^(Nat.card X-1) := by
  rcases D.subnormal_class_cube_or_typeA_higher_rank_parameters 1 (by decide) q
    (fun _=>hq) e H hH with hc|hp
  · exact hc
  · omega

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
