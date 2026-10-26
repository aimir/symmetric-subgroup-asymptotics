import SymmetricSubgroupAsymptotics.SmallFibreTwelveClassEnvelope

/-! The genuine binary unsigned29 reserve and ternary28 top ceiling
pay the extra cube exponent from nine original blocks onward. The
ternary eight-block case is not asserted. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.SmallFibreTwentyEightClassEnvelope

theorem binary_unsigned_gap (n : ℕ) (hn : 9≤n) :
    (29*2^(n-2))^3≤5^(2*n-2) := by
  induction n,hn using Nat.le_induction with
  | base => decide +kernel
  | succ n hn ih =>
    calc
      (29*2^((n+1)-2))^3=8*(29*2^(n-2))^3 := by
        rw [show (n+1)-2=(n-2)+1 by omega,pow_succ]
        ring
      _≤8*5^(2*n-2) := Nat.mul_le_mul_left _ ih
      _≤25*5^(2*n-2) := Nat.mul_le_mul_right _ (by decide : (8:ℕ)≤25)
      _=5^(2*(n+1)-2) := by
        rw [show 2*(n+1)-2=(2*n-2)+2 by omega,pow_add]
        ring

theorem ternary_gap (n : ℕ) (hn : 9≤n) :
    (3^n*28)^3≤5^(3*n-2) := by
  induction n,hn using Nat.le_induction with
  | base => decide +kernel
  | succ n hn ih =>
    calc
      (3^(n+1)*28)^3=27*(3^n*28)^3 := by rw [pow_succ]; ring
      _≤27*5^(3*n-2) := Nat.mul_le_mul_left _ ih
      _≤125*5^(3*n-2) := Nat.mul_le_mul_right _ (by decide : (27:ℕ)≤125)
      _=5^(3*(n+1)-2) := by
        rw [show 3*(n+1)-2=(3*n-2)+3 by omega,pow_add]
        ring

end SymmetricSubgroupAsymptotics.SmallFibreTwentyEightClassEnvelope
