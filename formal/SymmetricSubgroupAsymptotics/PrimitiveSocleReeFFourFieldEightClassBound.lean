import SymmetricSubgroupAsymptotics.PrimitiveSocleReeFFourOrderCubeTailClassBound
import SymmetricSubgroupAsymptotics.CFSGReeFFourFieldEightPrimeIndex
import SymmetricSubgroupAsymptotics.ReeFFourFieldEightClassNumerics

/-! The exact original field-eight prime-index certificate pays the full
component cube, retaining all socle factors and both raw degree forms. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open CFSGReduction
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.subgroup_class_cube_le_of_reeFFour_field_eight
    (D : NonaffineData G X) (e : D.Simple ≃* CFSG.Models.ReeF4 1) (H : Subgroup G) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  letI : IsSimpleGroup (CFSG.Models.ReeF4 1) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.ReeF4 1) := Finite.of_equiv D.Simple e.toEquiv
  refine D.subgroup_class_cube_le_of_component_order_cube 109 (by decide) ?_ ?_ ?_ H
  · intro K hK
    have hm : K.map e.toMonoidHom≠⊤ := by
      intro ht
      apply hK
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
    have hi := CFSGReeFFourFieldEightPrimeIndex.proper_index_le (K.map e.toMonoidHom) hm
    have hidx : (K.map e.toMonoidHom).index=K.index := K.index_map_equiv e
    exact hi.trans_eq hidx
  · rw [Nat.card_congr e.toEquiv,outer_card_congr e]
    exact (Nat.pow_le_pow_left (Nat.mul_le_mul
      (CFSGReeFFourWeightedFixedOrderUpper.original_ree_order_le 1)
      (CFSGReeFFourOriginalOuterBound.outer_card_le 1 (by decide))) 3).trans
        ReeFFourFieldEightClassNumerics.component_order_cube
  · rw [Nat.card_congr e.toEquiv]
    exact ReeFFourFieldEightClassNumerics.order_lower.trans
      (CFSGReeFFourOriginalOrderLower.original_ree_order_ge 1 (by decide))

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
