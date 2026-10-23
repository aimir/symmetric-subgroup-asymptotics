import SymmetricSubgroupAsymptotics.CFSGSymplecticOriginalOrderUpper
import SymmetricSubgroupAsymptotics.CFSGSymplecticIndexStarLower
import SymmetricSubgroupAsymptotics.CFSGSymplecticOuterCardinality
import SymmetricSubgroupAsymptotics.CFSGFiniteFieldAutomorphismsParameters
import Mathlib.Data.Nat.Log

/-! An actual order-plus-outer budget at every proper index for the
ORIGINAL C model. The stronger original root-star bound pays the full
matrix space uniformly in rank; the actual outer reconstruction is
bounded separately. No order, index or automorphism callback remains. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticProperIndexOrderBudget
open CFSGReduction PrimitiveSocleRawStructure

theorem matrix_power_le_index_log_power (q r m : ℕ) (hq : 2 ≤ q) (hr : 2 ≤ r)
    (hindex : q^(r-1) ≤ m) : q^(4*r^2) ≤ m^(4*Nat.log 2 m+12) := by
  have hqpos : 0<q := by omega
  have hm : 2 ≤ m := hq.trans ((Nat.le_self_pow (by omega : r-1≠0) q).trans hindex)
  have hlog : r-1 ≤ Nat.log 2 m := Nat.le_log_of_pow_le (by decide)
    ((Nat.pow_le_pow_left hq (r-1)).trans hindex)
  have hrank : r ≤ Nat.log 2 m+1 := by omega
  have hexp : 4*r^2 ≤ (r-1)*(4*r+8) := by
    have hrs : r-1+1=r := by omega
    nlinarith
  calc
    q^(4*r^2) ≤ q^((r-1)*(4*r+8)) := Nat.pow_le_pow_right hqpos hexp
    _ = (q^(r-1))^(4*r+8) := pow_mul _ _ _
    _ ≤ m^(4*r+8) := Nat.pow_le_pow_left hindex _
    _ ≤ m^(4*Nat.log 2 m+12) := Nat.pow_le_pow_right (by omega) (by omega)

theorem typeC_outer_card_le_proper_index_cube (r : ℕ) (hr : 2 ≤ r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.C r q)]
    (H : Subgroup (CFSG.Models.C r q)) (hH : H≠⊤) :
    Nat.card (Outer (CFSG.Models.C r q)) ≤ H.index^3 := by
  have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
  have hf : q.exponent ≤ q.order := q.exponent.lt_two_pow_self.le.trans
    (Nat.pow_le_pow_left q.prime_isPrime.two_le q.exponent)
  have hi : q.order ≤ H.index :=
    (Nat.le_self_pow (by omega : r-1≠0) q.order).trans
      (typeC_field_power_le_proper_index r hr q H hH)
  have hc : 3 ≤ q.order^2 := (by decide : 3≤2^2).trans (Nat.pow_le_pow_left hq 2)
  calc
    Nat.card (Outer (CFSG.Models.C r q)) ≤ 3*Nat.card (q.Field≃+*q.Field) :=
      typeC_outer_card_le r hr q
    _ = 3*q.exponent := by rw [CFSGFiniteFieldAutomorphisms.primePower_card_ringAut q]
    _ ≤ 3*q.order := Nat.mul_le_mul_left _ hf
    _ ≤ q.order^2*q.order := Nat.mul_le_mul_right _ hc
    _ = q.order^3 := (pow_succ _ 2).symm
    _ ≤ H.index^3 := Nat.pow_le_pow_left hi 3

theorem typeC_order_mul_outer_le_proper_index_log_power
    (r : ℕ) (hr : 2 ≤ r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.C r q)]
    (H : Subgroup (CFSG.Models.C r q)) (hH : H≠⊤) :
    Nat.card (CFSG.Models.C r q)*Nat.card (Outer (CFSG.Models.C r q)) ≤
      H.index^(4*Nat.log 2 H.index+23) := by
  have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
  have hi := typeC_field_power_le_proper_index r hr q H hH
  have hm : 2 ≤ H.index := hq.trans
    ((Nat.le_self_pow (by omega : r-1≠0) q.order).trans hi)
  calc
    Nat.card (CFSG.Models.C r q)*Nat.card (Outer (CFSG.Models.C r q)) ≤
        H.index^(4*Nat.log 2 H.index+12)*H.index^3 := Nat.mul_le_mul
      ((typeC_order_le_matrix_power r hr q).trans
        (matrix_power_le_index_log_power q.order r H.index hq hr hi))
      (typeC_outer_card_le_proper_index_cube r hr q H hH)
    _ = H.index^(4*Nat.log 2 H.index+15) := by rw [←pow_add]
    _ ≤ H.index^(4*Nat.log 2 H.index+23) := Nat.pow_le_pow_right (by omega) (by omega)

end SymmetricSubgroupAsymptotics.CFSGSymplecticProperIndexOrderBudget
