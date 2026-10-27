import SymmetricSubgroupAsymptotics.SmallFibreTwentyEightClassEnvelope

/-! The unsigned binary reserve and direct ternary budget for an actual
top class ceiling75, from eleven blocks onward. No group or action data
is supplied by these scalar lemmas. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.SmallFibreSeventyFiveClassEnvelope

theorem binary_unsigned_gap (n : ℕ) (hn : 11 ≤ n) :
    (76 * 2 ^ (n - 2)) ^ 3 ≤ 5 ^ (2 * n - 2) := by
  induction n,hn using Nat.le_induction with
  | base => decide +kernel
  | succ n hn ih =>
    calc
      (76 * 2 ^ ((n + 1) - 2)) ^ 3 = 8 * (76 * 2 ^ (n - 2)) ^ 3 := by
        rw [show (n + 1) - 2 = (n - 2) + 1 by omega,pow_succ]
        ring
      _ ≤ 8 * 5 ^ (2 * n - 2) := Nat.mul_le_mul_left _ ih
      _ ≤ 25 * 5 ^ (2 * n - 2) := Nat.mul_le_mul_right _ (by decide : (8 : ℕ) ≤ 25)
      _ = 5 ^ (2 * (n + 1) - 2) := by
        rw [show 2 * (n + 1) - 2 = (2 * n - 2) + 2 by omega,pow_add]
        ring

theorem ternary_gap (n : ℕ) (hn : 11 ≤ n) :
    (3 ^ n * 75) ^ 3 ≤ 5 ^ (3 * n - 2) := by
  induction n,hn using Nat.le_induction with
  | base => decide +kernel
  | succ n hn ih =>
    calc
      (3 ^ (n + 1) * 75) ^ 3 = 27 * (3 ^ n * 75) ^ 3 := by
        rw [pow_succ]
        ring
      _ ≤ 27 * 5 ^ (3 * n - 2) := Nat.mul_le_mul_left _ ih
      _ ≤ 125 * 5 ^ (3 * n - 2) := Nat.mul_le_mul_right _ (by decide : (27 : ℕ) ≤ 125)
      _ = 5 ^ (3 * (n + 1) - 2) := by
        rw [show 3 * (n + 1) - 2 = (3 * n - 2) + 3 by omega,pow_add]
        ring

end SymmetricSubgroupAsymptotics.SmallFibreSeventyFiveClassEnvelope
