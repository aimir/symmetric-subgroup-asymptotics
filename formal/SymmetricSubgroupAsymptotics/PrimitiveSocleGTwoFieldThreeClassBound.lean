import SymmetricSubgroupAsymptotics.PrimitiveSocleComponentOrderCubeClassBound
import SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleIndex
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckSharpComponentOrderBudget
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckFixedBruhatOrderUpper

/-! The original field-three G2 component pays its full order cube at
the actual two-orbit index54. Every socle factor and both original
primitive degree forms are retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open CFSGReduction
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.subgroup_class_cube_le_of_gTwo_field_three
    (D : NonaffineData G X) (q : CFSG.PrimePower) (hq : q.order=3)
    (e : D.Simple ≃* CFSG.Models.G2 q) (H : Subgroup G) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  letI : IsSimpleGroup (CFSG.Models.G2 q) := e.symm.isSimpleGroup
  have hn : ¬IsMulCommutative (CFSG.Models.G2 q) :=
    fun h => D.noncommutative ((isMulCommutative_congr e).mpr h)
  have hp3 : q.prime∣3^1 := by
    change q.prime∣3
    rw [←hq]
    exact dvd_pow_self _ q.exponent_pos.ne'
  have hp : q.prime=3 := Nat.prime_eq_prime_of_dvd_pow q.prime_isPrime (by decide) hp3
  have hf : q.exponent=1 := Nat.pow_right_injective (by decide : 2≤3)
    (by simpa only [CFSG.PrimePower.order,hp] using hq)
  refine D.subgroup_class_cube_le_of_component_order_cube 54 (by decide) ?_ ?_ ?_ H
  · intro K hK
    have hproper : K.map e.toMonoidHom ≠ ⊤ := by
      intro ht
      apply hK
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
    have hi := CFSGGTwoCharacteristicThreeMiddleIndex.typeGTwo_field_three_le_proper_index
      q hq (K.map e.toMonoidHom) hproper
    exact hi.trans_eq (K.index_map_equiv e)
  · rw [Nat.card_congr e.toEquiv,outer_card_congr e]
    have horder := CFSGGTwoD4GeckFixedBruhatOrderUpper.typeGTwo_order_le q hn
    have houter := CFSGGTwoD4GeckOriginalOuterBound.typeGTwo_outer_card_le_two_exponent q
    have hc := Nat.pow_le_pow_left (Nat.mul_le_mul horder houter) 3
    have hb : (24*q.exponent*q.order^14*(2*q.exponent))^3 ≤ 5^(54-1) := by
      rw [hq,hf]
      decide +kernel
    exact hc.trans hb
  · rw [Nat.card_congr e.toEquiv]
    have hc := CFSGGTwoD4GeckOriginalProjection.original_order_lower q.Field
    rw [q.card_field] at hc
    exact ((by decide : 1024 ≤ 3^12).trans (Nat.pow_le_pow_left (show 3≤q.order by omega) 12)).trans hc

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
