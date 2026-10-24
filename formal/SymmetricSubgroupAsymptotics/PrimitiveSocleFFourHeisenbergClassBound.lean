import SymmetricSubgroupAsymptotics.PrimitiveSocleComponentOrderCubeClassBound
import SymmetricSubgroupAsymptotics.CFSGFFourE6HeisenbergIndex
import SymmetricSubgroupAsymptotics.CFSGFFourOriginalOrderUpper
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport
import SymmetricSubgroupAsymptotics.FFourHeisenbergOrderCubeNumerics

/-! Every original F4 primitive component at field order at least three
pays the full component order cube at its actual Heisenberg index.
All socle factors, the subgroup and both raw degree forms are retained.
The binary field is deliberately not claimed here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open CFSGReduction
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.subgroup_class_cube_le_of_fFour_field_ge_three
    (D : NonaffineData G X) (q : CFSG.PrimePower) (hq : 3 ≤ q.order)
    (e : D.Simple ≃* CFSG.Models.F4 q) (H : Subgroup G) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  letI : IsSimpleGroup (CFSG.Models.F4 q) := e.symm.isSimpleGroup
  have hn : ¬IsMulCommutative (CFSG.Models.F4 q) :=
    fun h=>D.noncommutative ((isMulCommutative_congr e).mpr h)
  have hb : 3 ≤ 2*q.order^4 := by
    have hp := Nat.pow_le_pow_left hq 4
    omega
  refine D.subgroup_class_cube_le_of_component_order_cube (2*q.order^4) hb ?_ ?_ ?_ H
  · intro K hK
    have hproper : K.map e.toMonoidHom ≠ ⊤ := by
      intro ht
      apply hK
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
    have hi := CFSGFFourE6HeisenbergIndex.typeFFour_heisenberg_le_proper_index
      q (K.map e.toMonoidHom) hproper
    have hindex : (K.map e.toMonoidHom).index=K.index := K.index_map_equiv e
    exact ((Nat.mul_le_mul_right (q.order^4) q.prime_isPrime.two_le).trans hi).trans_eq hindex
  · rw [Nat.card_congr e.toEquiv,outer_card_congr e]
    have hc := Nat.pow_le_pow_left
      (CFSGFFourOriginalOrderUpper.typeFFour_order_mul_outer_le q hn) 3
    exact hc.trans (by
      simpa only [←pow_mul] using FFourHeisenbergOrderCubeNumerics.field_power_cube_le q.order hq)
  · rw [Nat.card_congr e.toEquiv]
    exact ((by decide : 1024 ≤ 3^9).trans (Nat.pow_le_pow_left hq 9)).trans
      (CFSGFFourE6HeisenbergIndex.typeFFour_order_nine_le q)

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
