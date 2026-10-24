import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! One numerical induction pays the complete rank-two symplectic order
cube once the actual proper-index lower bound is the field square. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticRankTwoSquareNumerics

theorem order_cube_budget (q : ℕ) (hq : 7 ≤ q) : q^39 ≤ 5^(q^2-1) := by
  induction q, hq using Nat.le_induction with
  | base => decide
  | succ q hq ih =>
    have h3 : (q+1)^3 ≤ 2*q^3 := by
      have h2 := Nat.mul_le_mul_right q hq
      have h3 := Nat.mul_le_mul_right (q*q) hq
      nlinarith
    have hstep : (q+1)^39 ≤ 2^13*q^39 := by
      calc
        (q+1)^39 = ((q+1)^3)^13 := by rw [← pow_mul]
        _ ≤ (2*q^3)^13 := Nat.pow_le_pow_left h3 13
        _ = 2^13*q^39 := by rw [mul_pow, ← pow_mul]
    have he : (q+1)^2-1 = (q^2-1)+(2*q+1) := by
      have hp : 1 ≤ q^2 := by nlinarith
      have hs : (q+1)^2 = q^2+2*q+1 := by ring
      omega
    calc
      (q+1)^39 ≤ 2^13*q^39 := hstep
      _ ≤ 5^15*5^(q^2-1) := Nat.mul_le_mul (by decide) ih
      _ ≤ 5^(2*q+1)*5^(q^2-1) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (by omega))
      _ = 5^((q+1)^2-1) := by rw [← pow_add, Nat.add_comm, he]

end SymmetricSubgroupAsymptotics.CFSGSymplecticRankTwoSquareNumerics
