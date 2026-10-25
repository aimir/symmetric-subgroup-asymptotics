import SymmetricSubgroupAsymptotics.PrimitiveSocleComponentOrderCubeClassBound
import SymmetricSubgroupAsymptotics.CFSGReeFFourWeightedFixedOrderUpper
import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalOuterBound
import SymmetricSubgroupAsymptotics.CFSGReeFFourPermutationDegree
import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalOrderLower
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport
import SymmetricSubgroupAsymptotics.ReeFFourOrderCubeTailNumerics

/-! The original Ree F4 component for every parameter m>=4. The actual
field-index and order/outer bounds pay the component order cube, with
all original socle factors and both primitive degree forms retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open CFSGReduction ReeFFourOrderCubeTailNumerics
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.subgroup_class_cube_le_of_reeFFour_order_tail
    (D : NonaffineData G X) (m : ℕ) (hm : 4 ≤ m)
    (e : D.Simple ≃* CFSG.Models.ReeF4 m) (H : Subgroup G) :
    Nat.card (ConjClasses H)^3≤5^(Nat.card X-1) := by
  letI : IsSimpleGroup (CFSG.Models.ReeF4 m) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.ReeF4 m) := Finite.of_equiv D.Simple e.toEquiv
  have hmpos : 0 < m := by omega
  have hq := field_ge_512 m hm
  refine D.subgroup_class_cube_le_of_component_order_cube (fieldOrder m)
    ((by decide : 3≤512).trans hq) ?_ ?_ ?_ H
  · intro K hK
    have hproper : K.map e.toMonoidHom≠⊤ := by
      intro ht
      apply hK
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
    have hi := CFSGReeFFourPermutationDegree.order_le_proper_index
      m hmpos (K.map e.toMonoidHom) hproper
    have hidx : (K.map e.toMonoidHom).index=K.index := K.index_map_equiv e
    exact hi.trans_eq hidx
  · rw [Nat.card_congr e.toEquiv,outer_card_congr e]
    exact (Nat.pow_le_pow_left (Nat.mul_le_mul
      (CFSGReeFFourWeightedFixedOrderUpper.original_ree_order_le m)
      (CFSGReeFFourOriginalOuterBound.outer_card_le m hmpos)) 3).trans
        (component_order_cube m hm)
  · rw [Nat.card_congr e.toEquiv]
    exact (by decide : 1024≤(2 : ℕ)^24).trans
      ((Nat.pow_le_pow_left ((by decide : 2≤512).trans hq) 24).trans
        (CFSGReeFFourOriginalOrderLower.original_ree_order_ge m hmpos))

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
