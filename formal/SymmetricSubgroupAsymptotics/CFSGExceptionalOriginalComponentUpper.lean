import SymmetricSubgroupAsymptotics.CFSGExceptionalOriginalOrderUpper
import SymmetricSubgroupAsymptotics.CFSGExceptionalOriginalOuterBound
import SymmetricSubgroupAsymptotics.CFSGFiniteFieldAutomorphismsParameters

/-! Original exceptional group order times original outer order, with
uniform field-power ceilings. The loose cubic outer ceiling includes
the field of two and uses only the already-proved actual outer bounds. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGExceptionalOriginalComponentUpper
open CFSGExceptionalOriginalOrderUpper CFSGExceptionalOriginalOuterBound
open CFSGFiniteFieldAutomorphisms PrimitiveSocleRawStructure

private theorem six_mul_le_binary_cube (n:ℕ) : 6*n≤(2^n)^3 := by
  induction n with
  | zero=>norm_num
  | succ n ih=>
    by_cases hn:n=0
    · subst n
      norm_num
    calc
      6*(n+1)≤8*(6*n) := by omega
      _≤8*(2^n)^3 := Nat.mul_le_mul_left 8 ih
      _=(2^(n+1))^3 := by rw [pow_succ]; ring

theorem six_exponent_le_order_cube (q:CFSG.PrimePower) : 6*q.exponent≤q.order^3 :=
  (six_mul_le_binary_cube q.exponent).trans
    (Nat.pow_le_pow_left (Nat.pow_le_pow_left q.prime_isPrime.two_le q.exponent) 3)

theorem E6_outer_le_cube (q:CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.E6 q)] :
    Nat.card (Outer (CFSG.Models.E6 q))≤q.order^3 := by
  have h:=serreTypeE6_outer_card_le q.Field q.prime
  rw [primePower_card_ringAut] at h
  exact h.trans (six_exponent_le_order_cube q)

theorem E7_outer_le_cube (q:CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.E7 q)] :
    Nat.card (Outer (CFSG.Models.E7 q))≤q.order^3 := by
  have h:=serreTypeE7_outer_card_le q.Field q.prime
  rw [primePower_card_ringAut] at h
  exact h.trans ((by omega:2*q.exponent≤6*q.exponent).trans (six_exponent_le_order_cube q))

theorem E8_outer_le_cube (q:CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.E8 q)] :
    Nat.card (Outer (CFSG.Models.E8 q))≤q.order^3 := by
  have h:=serreTypeE8_outer_card_le q.Field q.prime
  rw [primePower_card_ringAut] at h
  exact h.trans ((by omega:1*q.exponent≤6*q.exponent).trans (six_exponent_le_order_cube q))

theorem E6_order_mul_outer_le (q:CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.E6 q)]
    (hn:¬IsMulCommutative (CFSG.Models.E6 q)) :
    Nat.card (CFSG.Models.E6 q)*Nat.card (Outer (CFSG.Models.E6 q))≤q.order^129 := by
  have h:=serreTypeE6_order_le q.Field q.prime hn
  rw [q.card_field] at h
  exact (Nat.mul_le_mul h (E6_outer_le_cube q)).trans_eq (by ring)

theorem E7_order_mul_outer_le (q:CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.E7 q)]
    (hn:¬IsMulCommutative (CFSG.Models.E7 q)) :
    Nat.card (CFSG.Models.E7 q)*Nat.card (Outer (CFSG.Models.E7 q))≤q.order^192 := by
  have h:=serreTypeE7_order_le q.Field q.prime hn
  rw [q.card_field] at h
  exact (Nat.mul_le_mul h (E7_outer_le_cube q)).trans_eq (by ring)

theorem E8_order_mul_outer_le (q:CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.E8 q)]
    (hn:¬IsMulCommutative (CFSG.Models.E8 q)) :
    Nat.card (CFSG.Models.E8 q)*Nat.card (Outer (CFSG.Models.E8 q))≤q.order^323 := by
  have h:=serreTypeE8_order_le q.Field q.prime hn
  rw [q.card_field] at h
  exact (Nat.mul_le_mul h (E8_outer_le_cube q)).trans_eq (by ring)

end SymmetricSubgroupAsymptotics.CFSGExceptionalOriginalComponentUpper
