import SymmetricSubgroupAsymptotics.CFSGTypeAOriginalOrderUpper
import SymmetricSubgroupAsymptotics.CFSGTypeAIndexReindex
import SymmetricSubgroupAsymptotics.CFSGTypeAOuterCardinality
import SymmetricSubgroupAsymptotics.CFSGPSLTwoPermutationDegree
import SymmetricSubgroupAsymptotics.CFSGPSLTwoOuterBound
import SymmetricSubgroupAsymptotics.FieldRankIndexOrderNumerics

/-! A literal order-plus-outer budget for EVERY proper subgroup of the
original A model, including rank one. The higher-rank original root
space supplies q^r<=index; PSL2 supplies q<=2*index, sufficient for a
fixed eleven-power budget. No exceptional-field enumeration is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTypeAProperIndexOrderBudget
open CFSGReduction PrimitiveSocleRawStructure

theorem typeA_higher_field_power_le_proper_index (r : ℕ) (hr : 2 ≤ r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.A r q)]
    (H : Subgroup (CFSG.Models.A r q)) (hH : H≠⊤) : q.order^r ≤ H.index := by
  simpa only [q.card_field] using
    CFSGTypeAIndexReindex.field_power_le_proper_index (F:=q.Field) r hr H hH

theorem typeA_higher_outer_card_le_index_square (r : ℕ) (hr : 2 ≤ r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.A r q)]
    (H : Subgroup (CFSG.Models.A r q)) (hH : H≠⊤) :
    Nat.card (Outer (CFSG.Models.A r q)) ≤ H.index^2 := by
  have hraw : Nat.card (Outer (CFSG.Models.A r q)) ≤ 2*(r+1)*q.exponent := by
    simpa only [CFSGFiniteFieldAutomorphisms.primePower_card_ringAut q] using
      CFSGTypeAOuterCardinality.outer_card_le (F:=q.Field) q.prime (by omega : 3≤r+1)
  have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
  have hf : q.exponent ≤ q.order := q.exponent.lt_two_pow_self.le.trans
    (Nat.pow_le_pow_left q.prime_isPrime.two_le q.exponent)
  have hrq : r+1 ≤ q.order^r :=
    (Nat.succ_le_of_lt r.lt_two_pow_self).trans (Nat.pow_le_pow_left hq r)
  have h2q : 2*q.order ≤ q.order^r := by
    calc
      2*q.order ≤ q.order*q.order := Nat.mul_le_mul_right _ hq
      _ = q.order^2 := (pow_two _).symm
      _ ≤ q.order^r := Nat.pow_le_pow_right (by omega) hr
  have hi := typeA_higher_field_power_le_proper_index r hr q H hH
  calc
    Nat.card (Outer (CFSG.Models.A r q)) ≤ 2*(r+1)*q.exponent := hraw
    _ ≤ 2*(q.order^r)*q.order := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hrq) hf
    _ = q.order^r*(2*q.order) := by ring
    _ ≤ q.order^r*q.order^r := Nat.mul_le_mul_left _ h2q
    _ ≤ H.index*H.index := Nat.mul_le_mul hi hi
    _ = H.index^2 := (pow_two _).symm

theorem typeA_rank_one_order_outer_le_index_eleven (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.A 1 q)]
    (H : Subgroup (CFSG.Models.A 1 q)) (hH : H≠⊤) :
    Nat.card (CFSG.Models.A 1 q)*Nat.card (Outer (CFSG.Models.A 1 q)) ≤ H.index^11 := by
  have hm : 2 ≤ H.index := H.one_lt_index_of_ne_top hH
  have hqm : q.order ≤ 2*H.index := by
    simpa only [q.card_field] using
      CFSGPSLTwoGeometry.field_card_le_twice_proper_index (F:=q.Field) H hH
  have hqm2 : q.order ≤ H.index^2 := hqm.trans (by nlinarith)
  have hf : q.exponent ≤ q.order := q.exponent.lt_two_pow_self.le.trans
    (Nat.pow_le_pow_left q.prime_isPrime.two_le q.exponent)
  have ho : Nat.card (Outer (CFSG.Models.A 1 q)) ≤ H.index^3 := by
    calc
      Nat.card (Outer (CFSG.Models.A 1 q)) ≤ 2*q.exponent :=
        CFSGPSLTwoOuterBound.typeA_rank_one_outer_card q
      _ ≤ 2*q.order := Nat.mul_le_mul_left _ hf
      _ ≤ 2*H.index^2 := Nat.mul_le_mul_left _ hqm2
      _ ≤ H.index*H.index^2 := Nat.mul_le_mul_right _ hm
      _ = H.index^3 := by ring
  have hs : Nat.card (CFSG.Models.A 1 q) ≤ H.index^8 := by
    calc
      Nat.card (CFSG.Models.A 1 q) ≤ q.order^4 := typeA_order_le_matrix_power 1 q
      _ ≤ (H.index^2)^4 := Nat.pow_le_pow_left hqm2 4
      _ = H.index^8 := by rw [←pow_mul]
  exact (Nat.mul_le_mul hs ho).trans_eq (by rw [←pow_add])

theorem typeA_order_mul_outer_le_proper_index_log_power
    (r : ℕ) (hr : 1 ≤ r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.A r q)]
    (H : Subgroup (CFSG.Models.A r q)) (hH : H≠⊤) :
    Nat.card (CFSG.Models.A r q)*Nat.card (Outer (CFSG.Models.A r q)) ≤
      H.index^(4*Nat.log 2 H.index+23) := by
  have hm : 2 ≤ H.index := H.one_lt_index_of_ne_top hH
  by_cases hone : r=1
  · subst r
    exact (typeA_rank_one_order_outer_le_index_eleven q H hH).trans
      (Nat.pow_le_pow_right (by omega) (by omega))
  · have hr2 : 2 ≤ r := by omega
    have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
      (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
    have hi := typeA_higher_field_power_le_proper_index r hr2 q H hH
    have hs : Nat.card (CFSG.Models.A r q) ≤ H.index^(4*Nat.log 2 H.index+1) :=
      (typeA_order_le_matrix_power r q).trans
        ((Nat.pow_le_pow_right (by omega : 0<q.order)
          (by nlinarith : (r+1)^2≤2*(r+1)^2)).trans
          (FieldRankIndexOrderNumerics.matrix_power_le_index_log_power q.order r H.index hq hr2 hi))
    calc
      Nat.card (CFSG.Models.A r q)*Nat.card (Outer (CFSG.Models.A r q)) ≤
          H.index^(4*Nat.log 2 H.index+1)*H.index^2 := Nat.mul_le_mul hs
        (typeA_higher_outer_card_le_index_square r hr2 q H hH)
      _ = H.index^(4*Nat.log 2 H.index+3) := by rw [←pow_add]
      _ ≤ H.index^(4*Nat.log 2 H.index+23) := Nat.pow_le_pow_right (by omega) (by omega)

end SymmetricSubgroupAsymptotics.CFSGTypeAProperIndexOrderBudget
