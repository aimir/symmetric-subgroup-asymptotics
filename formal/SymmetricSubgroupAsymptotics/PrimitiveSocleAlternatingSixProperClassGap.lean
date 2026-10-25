import SymmetricSubgroupAsymptotics.PrimitiveSocleSmallHeadProperClassGap
import SymmetricSubgroupAsymptotics.PrimitiveSocleAlternatingProperSubnormalClassGap
import SymmetricSubgroupAsymptotics.AlternatingSixClassBound

/-! The genuine four-element outer group at A6 is retained. The
same faithful degree-six action permits an actual socle quotient of
order at most two, while every other degree absorbs outer order four. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X]

theorem NonaffineData.proper_subnormal_class_cube_le_of_alternating_six_component
    (D : NonaffineData G X) (e : D.Simple ≃* alternatingGroup (Fin 6))
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
  refine D.proper_subnormal_class_cube_le_of_small_model_head
    (alternatingGroup (Fin 6)) e 6 360 7 4 (by decide) ?_
    AlternatingSixClassBound.alternating_six_class_card_le_seven
    (CFSGAlternatingOuterBound.outer_card_le_four 6 (by decide))
    (CFSGAlternatingMinimumIndex.degree_le_proper_index 6 (by decide))
    (by decide) (by decide) (by decide) (by decide) (by decide) H hH hne
  rw [nat_card_alternatingGroup, Nat.card_fin]
  decide

theorem NonaffineData.proper_subnormal_class_cube_le_of_alternating_all_components
    (D : NonaffineData G X) (m : ℕ) (hm : 5 ≤ m)
    (e : D.Simple ≃* alternatingGroup (Fin m))
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
  by_cases hsix : m=6
  · subst m
    exact D.proper_subnormal_class_cube_le_of_alternating_six_component e H hH hne
  · exact D.proper_subnormal_class_cube_le_of_alternating_component m hm hsix e H hH hne

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
