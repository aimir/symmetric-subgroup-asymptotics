import SymmetricSubgroupAsymptotics.PrimitiveSocleModelProperClassCapacity
import SymmetricSubgroupAsymptotics.PrimitiveSocleFFourHeisenbergClassBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleFFourBinaryLeviClassBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleTrialityCompleteClassBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleTrialityBinaryClassBound

/-! Existing actual Heisenberg and binary Levi/tensor packets pay
proper-subnormal extra capacity for every original F4 and triality
model. No ordinary class conclusion is promoted without its metadata. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open CFSGReduction
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.proper_subnormal_class_cube_le_of_fFour_all_fields
    (D : NonaffineData G X) (q : CFSG.PrimePower) (e : D.Simple ≃* CFSG.Models.F4 q)
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
  letI : IsSimpleGroup (CFSG.Models.F4 q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.F4 q) := Finite.of_equiv D.Simple e.toEquiv
  have hn : ¬IsMulCommutative (CFSG.Models.F4 q) :=
    fun h => D.noncommutative ((isMulCommutative_congr e).mpr h)
  by_cases hq : 3 ≤ q.order
  · have hb : 3 ≤ 2*q.order^4 := by have hp := Nat.pow_le_pow_left hq 4; omega
    refine D.proper_subnormal_class_cube_le_of_model_order_capacity
      (CFSG.Models.F4 q) e (2*q.order^4) hb ?_ ?_ ?_ H hH hne
    · intro K hK
      exact (Nat.mul_le_mul_right (q.order^4) q.prime_isPrime.two_le).trans
        (CFSGFFourE6HeisenbergIndex.typeFFour_heisenberg_le_proper_index q K hK)
    · have hc := Nat.pow_le_pow_left
        (CFSGFFourOriginalOrderUpper.typeFFour_order_mul_outer_le q hn) 3
      exact hc.trans (by simpa only [← pow_mul] using
        FFourHeisenbergOrderCubeNumerics.field_power_cube_le q.order hq)
    · exact ((by decide : 1024 ≤ 3^9).trans (Nat.pow_le_pow_left hq 9)).trans
        (CFSGFFourE6HeisenbergIndex.typeFFour_order_nine_le q)
  · have htwo : 2 ≤ q.order := q.prime_isPrime.two_le.trans
      (Nat.le_self_pow q.exponent_pos.ne' q.prime)
    have hq2 : q.order=2 := by omega
    refine D.proper_subnormal_class_cube_le_of_model_order_capacity
      (CFSG.Models.F4 q) e 128 (by decide)
      (CFSGFFourBinaryQuadraticLeviIndex.typeFFour_binary_levi_le_proper_index q hq2)
      ?_ ?_ H hH hne
    · have hc := Nat.pow_le_pow_left
        (CFSGFFourOriginalOrderUpper.typeFFour_order_mul_outer_le q hn) 3
      rw [hq2] at hc
      exact hc.trans (by decide +kernel)
    · exact (by decide : 1024 ≤ 2^15).trans
        (CFSGFFourBinaryQuadraticLeviIndex.typeFFour_binary_order_fifteen_le q hq2)

theorem NonaffineData.proper_subnormal_class_cube_le_of_triality_all_fields
    (D : NonaffineData G X) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.TrialityD4 q)
    (H : Subgroup G) (hH : H.IsSubnormal) (hne : H ≠ ⊤) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-2) := by
  letI : IsSimpleGroup (CFSG.Models.TrialityD4 q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.TrialityD4 q) := Finite.of_equiv D.Simple e.toEquiv
  have hn : ¬IsMulCommutative (CFSG.Models.TrialityD4 q) :=
    fun h => D.noncommutative ((isMulCommutative_congr e).mpr h)
  have horder : Nat.card (CFSG.Models.TrialityD4 q)*Nat.card (Outer (CFSG.Models.TrialityD4 q))
      ≤ q.order^35 :=
    (Nat.mul_le_mul (CFSGTrialityGeckOriginalOrderUpper.original_order_le_power q hn)
      (CFSGTrialityGeckProperIndexOrderBudget.original_outer_card_le_power q)).trans_eq (by ring)
  by_cases hq : 3 ≤ q.order
  · have hb : 3 ≤ 2*q.order^4 := by have hp := Nat.pow_le_pow_left hq 4; omega
    refine D.proper_subnormal_class_cube_le_of_model_order_capacity
      (CFSG.Models.TrialityD4 q) e (2*q.order^4) hb ?_ ?_ ?_ H hH hne
    · intro K hK
      exact (Nat.mul_le_mul_right (q.order^4) q.prime_isPrime.two_le).trans
        (CFSGTrialityGeckMiddlePairingIndex.typeTriality_middle_le_proper_index q K hK)
    · calc
        _ ≤ (q.order^35)^3 := Nat.pow_le_pow_left horder 3
        _ = q.order^105 := by rw [← pow_mul]
        _ ≤ q.order^198 := Nat.pow_le_pow_right (by omega) (by decide)
        _ ≤ 5^(2*q.order^4-1) :=
          FFourHeisenbergOrderCubeNumerics.field_power_cube_le q.order hq
    · exact ((by decide : 1024 ≤ 3^24).trans (Nat.pow_le_pow_left hq 24)).trans
        (CFSGTrialityGeckOriginalOrderLower.original_card_lower q)
  · have htwo : 2 ≤ q.order := q.prime_isPrime.two_le.trans
      (Nat.le_self_pow q.exponent_pos.ne' q.prime)
    have hq2 : q.order=2 := by omega
    refine D.proper_subnormal_class_cube_le_of_model_order_capacity
      (CFSG.Models.TrialityD4 q) e 64 (by decide)
      (CFSGTrialityBinaryRegularModuleIndex.typeTriality_binary_regular_le_proper_index q hq2)
      ?_ ?_ H hH hne
    · exact (Nat.pow_le_pow_left horder 3).trans (by rw [hq2]; decide +kernel)
    · have hnum : 1024 ≤ q.order^24 := by rw [hq2]; decide
      exact hnum.trans (CFSGTrialityGeckOriginalOrderLower.original_card_lower q)

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
