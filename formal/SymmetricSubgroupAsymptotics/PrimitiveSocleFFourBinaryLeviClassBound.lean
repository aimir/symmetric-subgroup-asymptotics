import SymmetricSubgroupAsymptotics.PrimitiveSocleComponentOrderCubeClassBound
import SymmetricSubgroupAsymptotics.CFSGFFourBinaryQuadraticLeviIndex
import SymmetricSubgroupAsymptotics.CFSGFFourOriginalOrderUpper
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport

/-! Binary F4 on the original primitive component, using its actual
quadratic Levi index. Every socle factor and both degree forms remain. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open CFSGReduction
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.subgroup_class_cube_le_of_fFour_binary
    (D : NonaffineData G X) (q : CFSG.PrimePower) (hq : q.order=2)
    (e : D.Simple ≃* CFSG.Models.F4 q) (H : Subgroup G) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  letI : IsSimpleGroup (CFSG.Models.F4 q) := e.symm.isSimpleGroup
  have hn : ¬IsMulCommutative (CFSG.Models.F4 q) :=
    fun h=>D.noncommutative ((isMulCommutative_congr e).mpr h)
  refine D.subgroup_class_cube_le_of_component_order_cube 128 (by decide) ?_ ?_ ?_ H
  · intro K hK
    have hproper : K.map e.toMonoidHom ≠ ⊤ := by
      intro ht
      apply hK
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
    have hi := CFSGFFourBinaryQuadraticLeviIndex.typeFFour_binary_levi_le_proper_index
      q hq (K.map e.toMonoidHom) hproper
    exact hi.trans_eq (K.index_map_equiv e)
  · rw [Nat.card_congr e.toEquiv,outer_card_congr e]
    have hc := Nat.pow_le_pow_left
      (CFSGFFourOriginalOrderUpper.typeFFour_order_mul_outer_le q hn) 3
    rw [hq] at hc
    exact hc.trans (by decide +kernel)
  · rw [Nat.card_congr e.toEquiv]
    exact (by decide : 1024≤2^15).trans
      (CFSGFFourBinaryQuadraticLeviIndex.typeFFour_binary_order_fifteen_le q hq)

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
