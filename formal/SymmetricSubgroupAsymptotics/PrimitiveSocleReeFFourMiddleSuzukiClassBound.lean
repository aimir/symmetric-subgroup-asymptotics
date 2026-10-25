import SymmetricSubgroupAsymptotics.PrimitiveSocleReeFFourOrderCubeTailClassBound
import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleSuzukiIndex
import SymmetricSubgroupAsymptotics.ReeFFourMiddleSuzukiClassNumerics

/-! The actual middle Suzuki Borel pays every original Ree F4
component for m>=2, retaining all factors and both degree forms. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open CFSGReduction
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.subgroup_class_cube_le_of_reeFFour_middle_suzuki
    (D : NonaffineData G X) (m : ℕ) (hm : 2 ≤ m)
    (e : D.Simple ≃* CFSG.Models.ReeF4 m) (H : Subgroup G) :
    Nat.card (ConjClasses H)^3≤5^(Nat.card X-1) := by
  letI : IsSimpleGroup (CFSG.Models.ReeF4 m) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.ReeF4 m) := Finite.of_equiv D.Simple e.toEquiv
  have hmpos : 0 < m := by omega
  have hq : 2≤2^(2*m+1) :=
    Nat.pow_le_pow_right (by decide : 0<(2 : ℕ)) (by omega : 1≤2*m+1)
  refine D.subgroup_class_cube_le_of_component_order_cube
    (ReeFFourMiddleSuzukiClassNumerics.indexBound m)
    ((by decide : 3≤248).trans (ReeFFourMiddleSuzukiClassNumerics.index_ge_248 m hm))
    ?_ ?_ ?_ H
  · intro K hK
    have hproper : K.map e.toMonoidHom≠⊤ := by
      intro ht
      apply hK
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
    have hi := CFSGReeFFourMiddleSuzukiIndex.middle_suzuki_le_proper_index
      m hmpos (K.map e.toMonoidHom) hproper
    have hidx : (K.map e.toMonoidHom).index=K.index := K.index_map_equiv e
    exact hi.trans_eq hidx
  · rw [Nat.card_congr e.toEquiv,outer_card_congr e]
    exact (Nat.pow_le_pow_left (Nat.mul_le_mul
      (CFSGReeFFourWeightedFixedOrderUpper.original_ree_order_le m)
      (CFSGReeFFourOriginalOuterBound.outer_card_le m hmpos)) 3).trans
        (ReeFFourMiddleSuzukiClassNumerics.component_order_cube m hm)
  · rw [Nat.card_congr e.toEquiv]
    exact (by decide : 1024≤(2 : ℕ)^24).trans
      ((Nat.pow_le_pow_left hq 24).trans
        (CFSGReeFFourOriginalOrderLower.original_ree_order_ge m hmpos))

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
