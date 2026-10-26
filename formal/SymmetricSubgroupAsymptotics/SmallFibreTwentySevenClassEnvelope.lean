import SymmetricSubgroupAsymptotics.SmallFibreTwelveClassEnvelope

/-! Constant27 top budgets retain the unsigned binary reserve. Strong
local−2 bounds hold for binary degree>=8 and ternary degree>=9. Ternary
degree8 pays the ordinary global−1 exponent; it is not asserted to pay−2. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.SmallFibreTwentySevenClassEnvelope

theorem binary_gap (n : ℕ) (hn : 8≤n) :
    (28*2^(n-2))^3≤5^(2*n-2) := by
  induction n,hn using Nat.le_induction with
  | base => decide +kernel
  | succ n hn ih =>
    calc
      (28*2^((n+1)-2))^3=8*(28*2^(n-2))^3 := by
        rw [show (n+1)-2=(n-2)+1 by omega,pow_succ]
        ring
      _≤8*5^(2*n-2) := Nat.mul_le_mul_left _ ih
      _≤25*5^(2*n-2) := Nat.mul_le_mul_right _ (by decide : (8:ℕ)≤25)
      _=5^(2*(n+1)-2) := by
        rw [show 2*(n+1)-2=(2*n-2)+2 by omega,pow_add]
        ring

theorem ternary_gap (n : ℕ) (hn : 9≤n) :
    (3^n*27)^3≤5^(3*n-2) := by
  induction n,hn using Nat.le_induction with
  | base => decide +kernel
  | succ n hn ih =>
    calc
      (3^(n+1)*27)^3=27*(3^n*27)^3 := by rw [pow_succ];ring
      _≤27*5^(3*n-2) := Nat.mul_le_mul_left _ ih
      _≤125*5^(3*n-2) := Nat.mul_le_mul_right _ (by decide : (27:ℕ)≤125)
      _=5^(3*(n+1)-2) := by
        rw [show 3*(n+1)-2=(3*n-2)+3 by omega,pow_add]
        ring

theorem ternary_ordinary (n : ℕ) (hn : 8≤n) :
    (3^n*27)^3≤5^(3*n-1) := by
  induction n,hn using Nat.le_induction with
  | base => decide +kernel
  | succ n hn ih =>
    calc
      (3^(n+1)*27)^3=27*(3^n*27)^3 := by rw [pow_succ];ring
      _≤27*5^(3*n-1) := Nat.mul_le_mul_left _ ih
      _≤125*5^(3*n-1) := Nat.mul_le_mul_right _ (by decide : (27:ℕ)≤125)
      _=5^(3*(n+1)-1) := by
        rw [show 3*(n+1)-1=(3*n-1)+3 by omega,pow_add]
        ring

end SymmetricSubgroupAsymptotics.SmallFibreTwentySevenClassEnvelope
