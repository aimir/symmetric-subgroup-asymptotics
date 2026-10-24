import SymmetricSubgroupAsymptotics.PrimitiveSocleComponentOrderCubeClassBound
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddlePairingIndex
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckSharpComponentOrderBudget
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport
import SymmetricSubgroupAsymptotics.GTwoMiddlePairingClassNumerics

/-! Original G2 primitive class cubes in good characteristic, at all
field orders at least five. The characteristic-three degeneration and
the field of order four remain explicit. Every socle factor and both
primitive degree forms use the same actual model. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open CFSGReduction
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.subgroup_class_cube_le_of_gTwo_good_characteristic
    (D : NonaffineData G X) (q : CFSG.PrimePower) (hq : 5 ≤ q.order)
    (hchar : q.prime ≠ 3) (e : D.Simple ≃* CFSG.Models.G2 q) (H : Subgroup G) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  letI : IsSimpleGroup (CFSG.Models.G2 q) := e.symm.isSimpleGroup
  have hn : ¬IsMulCommutative (CFSG.Models.G2 q) :=
    fun h=>D.noncommutative ((isMulCommutative_congr e).mpr h)
  have hb : 3 ≤ q.prime*q.order^2 := by
    have hp := Nat.pow_le_pow_left hq 2
    have hm := Nat.mul_le_mul_right (q.order^2) q.prime_isPrime.two_le
    omega
  refine D.subgroup_class_cube_le_of_component_order_cube (q.prime*q.order^2) hb ?_ ?_ ?_ H
  · intro K hK
    have hproper : K.map e.toMonoidHom ≠ ⊤ := by
      intro ht
      apply hK
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
    have hi := CFSGGTwoD4GeckMiddlePairingIndex.typeGTwo_middle_le_proper_index
      q hchar (K.map e.toMonoidHom) hproper
    exact hi.trans_eq (K.index_map_equiv e)
  · rw [Nat.card_congr e.toEquiv,outer_card_congr e]
    have hc := Nat.pow_le_pow_left
      (CFSGGTwoD4GeckSharpComponentOrderBudget.order_mul_outer_le q (by omega) hn) 3
    exact hc.trans (by simpa only [←pow_mul] using
      GTwoMiddlePairingClassNumerics.primePower_middle_index_budget q hq)
  · rw [Nat.card_congr e.toEquiv]
    have hc := CFSGGTwoD4GeckOriginalProjection.original_order_lower q.Field
    rw [q.card_field] at hc
    exact ((by decide : 1024 ≤ 5^12).trans (Nat.pow_le_pow_left hq 12)).trans hc

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
