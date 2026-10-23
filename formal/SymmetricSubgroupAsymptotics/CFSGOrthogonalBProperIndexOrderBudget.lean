import SymmetricSubgroupAsymptotics.CFSGOrthogonalBOriginalMatrixBounds
import Mathlib.Data.Nat.Log

/-! The actual ORIGINAL B bounds pay one uniform proper-index order
budget in both characteristics. The literal root-star lower bound
controls the odd-dimensional matrix size for every classifier rank. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBProperIndexOrderBudget
open CFSGOrthogonalBOriginalMatrixBounds PrimitiveSocleRawStructure

theorem matrix_power_le_index_log_power (q r m : ℕ) (hq : 2 ≤ q) (hr : 3 ≤ r)
    (hindex : q^(r-1) ≤ m) : q^((2*r+1)^2) ≤ m^(4*Nat.log 2 m+17) := by
  have hqpos : 0<q := by omega
  have hm : 2 ≤ m := hq.trans ((Nat.le_self_pow (by omega : r-1≠0) q).trans hindex)
  have hlog : r-1 ≤ Nat.log 2 m := Nat.le_log_of_pow_le (by decide)
    ((Nat.pow_le_pow_left hq (r-1)).trans hindex)
  have hrank : r ≤ Nat.log 2 m+1 := by omega
  have hexp : (2*r+1)^2 ≤ (r-1)*(4*r+13) := by
    have hrs : r-1+1=r := by omega
    nlinarith
  calc
    q^((2*r+1)^2) ≤ q^((r-1)*(4*r+13)) := Nat.pow_le_pow_right hqpos hexp
    _ = (q^(r-1))^(4*r+13) := pow_mul _ _ _
    _ ≤ m^(4*r+13) := Nat.pow_le_pow_left hindex _
    _ ≤ m^(4*Nat.log 2 m+17) := Nat.pow_le_pow_right (by omega) (by omega)

theorem typeB_outer_card_le_proper_index_square (r : ℕ) (hr : 3 ≤ r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.B r q)]
    (H : Subgroup (CFSG.Models.B r q)) (hH : H≠⊤) :
    Nat.card (Outer (CFSG.Models.B r q)) ≤ H.index^2 := by
  have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
  have hf : q.exponent ≤ q.order := q.exponent.lt_two_pow_self.le.trans
    (Nat.pow_le_pow_left q.prime_isPrime.two_le q.exponent)
  have hi : q.order^2 ≤ H.index :=
    (Nat.pow_le_pow_right (by omega : 0<q.order) (by omega : 2≤r-1)).trans
      (typeB_field_power_le_proper_index r hr q H hH)
  have hc : 3 ≤ q.order^3 := (by decide : 3≤2^3).trans (Nat.pow_le_pow_left hq 3)
  calc
    Nat.card (Outer (CFSG.Models.B r q)) ≤ 3*q.exponent := typeB_outer_card_le_three_exponent r hr q
    _ ≤ 3*q.order := Nat.mul_le_mul_left _ hf
    _ ≤ q.order^3*q.order := Nat.mul_le_mul_right _ hc
    _ = q.order^4 := (pow_succ _ 3).symm
    _ = (q.order^2)^2 := by rw [←pow_mul]
    _ ≤ H.index^2 := Nat.pow_le_pow_left hi 2

theorem typeB_order_mul_outer_le_proper_index_log_power
    (r : ℕ) (hr : 3 ≤ r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.B r q)]
    (H : Subgroup (CFSG.Models.B r q)) (hH : H≠⊤) :
    Nat.card (CFSG.Models.B r q)*Nat.card (Outer (CFSG.Models.B r q)) ≤
      H.index^(4*Nat.log 2 H.index+23) := by
  have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
  have hi := typeB_field_power_le_proper_index r hr q H hH
  have hm : 2 ≤ H.index := hq.trans
    ((Nat.le_self_pow (by omega : r-1≠0) q.order).trans hi)
  calc
    Nat.card (CFSG.Models.B r q)*Nat.card (Outer (CFSG.Models.B r q)) ≤
        H.index^(4*Nat.log 2 H.index+17)*H.index^2 := Nat.mul_le_mul
      ((typeB_order_le_matrix_power r hr q).trans
        (matrix_power_le_index_log_power q.order r H.index hq hr hi))
      (typeB_outer_card_le_proper_index_square r hr q H hH)
    _ = H.index^(4*Nat.log 2 H.index+19) := by rw [←pow_add]
    _ ≤ H.index^(4*Nat.log 2 H.index+23) := Nat.pow_le_pow_right (by omega) (by omega)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBProperIndexOrderBudget
