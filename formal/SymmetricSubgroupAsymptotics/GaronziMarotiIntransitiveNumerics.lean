import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-! Exact integral exponent arithmetic for the intransitive GM step.
The exceptional degrees two and three use their literal class budgets,
not an incorrectly extended GM bound on those degrees. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.GaronziMarotiIntransitiveNumerics

private theorem small_cube_le (a r : ℕ) (hr : r ≤ 3) (ha : a ≤ r) :
    a^3 ≤ 5^r := by
  apply (Nat.pow_le_pow_left ha 3).trans
  interval_cases r <;> norm_num

theorem product_cube_le (a b r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s)
    (hn : 4 ≤ r+s)
    (haSmall : r ≤ 3 → a ≤ r) (hbSmall : s ≤ 3 → b ≤ s)
    (haLarge : 4 ≤ r → a^3 ≤ 5^(r-1))
    (hbLarge : 4 ≤ s → b^3 ≤ 5^(s-1)) :
    (a*b)^3 ≤ 5^(r+s-1) := by
  by_cases hr4 : 4 ≤ r
  · by_cases hs4 : 4 ≤ s
    · calc
        (a*b)^3 = a^3*b^3 := mul_pow _ _ _
        _ ≤ 5^(r-1)*5^(s-1) := Nat.mul_le_mul (haLarge hr4) (hbLarge hs4)
        _ = 5^((r-1)+(s-1)) := (pow_add _ _ _).symm
        _ ≤ 5^(r+s-1) := Nat.pow_le_pow_right (by decide) (by omega)
    · have hs3 : s ≤ 3 := by omega
      calc
        (a*b)^3 = a^3*b^3 := mul_pow _ _ _
        _ ≤ 5^(r-1)*5^s := Nat.mul_le_mul (haLarge hr4)
          (small_cube_le b s hs3 (hbSmall hs3))
        _ = 5^((r-1)+s) := (pow_add _ _ _).symm
        _ = 5^(r+s-1) := by congr 1; omega
  · have hr3 : r ≤ 3 := by omega
    by_cases hs4 : 4 ≤ s
    · calc
        (a*b)^3 = a^3*b^3 := mul_pow _ _ _
        _ ≤ 5^r*5^(s-1) := Nat.mul_le_mul (small_cube_le a r hr3 (haSmall hr3))
          (hbLarge hs4)
        _ = 5^(r+(s-1)) := (pow_add _ _ _).symm
        _ = 5^(r+s-1) := by congr 1; omega
    · have hs3 : s ≤ 3 := by omega
      apply (Nat.pow_le_pow_left (Nat.mul_le_mul (haSmall hr3) (hbSmall hs3)) 3).trans
      interval_cases r <;> interval_cases s <;> norm_num at *

end SymmetricSubgroupAsymptotics.GaronziMarotiIntransitiveNumerics
