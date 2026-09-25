import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-! Integer arithmetic for the local ternary grid-width coefficient.
No assertion about an induced representation is assumed here. -/
set_option autoImplicit false
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics

def ternaryLocalWidth (t : ℕ) : ℕ :=
  if t = 0 then 1 else if t = 1 then 1 else if t = 2 then 3
  else 7 * 3 ^ (t - 3)

@[simp] theorem ternaryLocalWidth_zero : ternaryLocalWidth 0 = 1 := rfl
@[simp] theorem ternaryLocalWidth_one : ternaryLocalWidth 1 = 1 := rfl
@[simp] theorem ternaryLocalWidth_two : ternaryLocalWidth 2 = 3 := rfl

theorem ternaryLocalWidth_eq_of_three_le (t : ℕ) (ht : 3 ≤ t) :
    ternaryLocalWidth t = 7 * 3 ^ (t - 3) := by
  simp [ternaryLocalWidth, show t ≠ 0 by omega, show t ≠ 1 by omega,
    show t ≠ 2 by omega]

theorem ternaryLocalWidth_mul_twentyseven (t : ℕ) (ht : 3 ≤ t) :
    ternaryLocalWidth t * 27 = 7 * 3 ^ t := by
  have hp : 3 ^ t = 3 ^ (t - 3) * 27 := by
    calc
      3 ^ t = 3 ^ ((t - 3) + 3) := congrArg (fun n : ℕ => 3 ^ n) (by omega)
      _ = 3 ^ (t - 3) * 27 := by rw [pow_add]; norm_num
  rw [ternaryLocalWidth_eq_of_three_le t ht, hp]
  omega

theorem ternaryLocalWidth_mul_three_le (t : ℕ) (ht : 1 ≤ t) :
    ternaryLocalWidth t * 3 ≤ 3 ^ t := by
  by_cases h3 : 3 ≤ t
  · have h := ternaryLocalWidth_mul_twentyseven t h3
    omega
  · have h : t = 1 ∨ t = 2 := by omega
    rcases h with rfl | rfl <;> norm_num

theorem ternaryLocalWidth_le_pow (t : ℕ) : ternaryLocalWidth t ≤ 3 ^ t := by
  by_cases ht : t = 0
  · subst t; norm_num
  · have h := ternaryLocalWidth_mul_three_le t (by omega)
    omega

/-- Positive orbit exponents may be unequal. The sum of their actual
orbit sizes, rather than a count of a replacement model, is the input. -/
theorem ternaryLocalWidth_sum_le_third {ι : Type*} [Fintype ι]
    (j : ι → ℕ) (s : ℕ) (hj : ∀ i, 1 ≤ j i)
    (hs : ∑ i, 3 ^ j i = s) : ∑ i, ternaryLocalWidth (j i) ≤ s / 3 := by
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 3)).mpr
  calc
    (∑ i, ternaryLocalWidth (j i)) * 3 =
        ∑ i, ternaryLocalWidth (j i) * 3 := Finset.sum_mul _ _ _
    _ ≤ ∑ i, 3 ^ j i := Finset.sum_le_sum (fun i _ =>
      ternaryLocalWidth_mul_three_le (j i) (hj i))
    _ = s := hs

theorem ternaryLocalWidth_sum_eq_seven_twentyseven {ι : Type*} [Fintype ι]
    (j : ι → ℕ) (s : ℕ) (hj : ∀ i, 3 ≤ j i)
    (hs : ∑ i, 3 ^ j i = s) :
    ∑ i, ternaryLocalWidth (j i) = 7 * s / 27 := by
  have h : (∑ i, ternaryLocalWidth (j i)) * 27 = 7 * s := by
    calc
      _ = ∑ i, ternaryLocalWidth (j i) * 27 := Finset.sum_mul _ _ _
      _ = ∑ i, 7 * 3 ^ j i := Finset.sum_congr rfl (fun i _ =>
        ternaryLocalWidth_mul_twentyseven (j i) (hj i))
      _ = 7 * s := by rw [← Finset.mul_sum, hs]
  omega

theorem ternaryLocalWidth_weighted_sum_le_third {ι : Type*} [Fintype ι]
    (a : ℕ) (j : ι → ℕ) (s : ℕ) (hj : ∀ i, 1 ≤ j i)
    (hs : ∑ i, 3 ^ j i = s) :
    ∑ i, a * ternaryLocalWidth (j i) ≤ a * (s / 3) := by
  rw [← Finset.mul_sum]
  exact Nat.mul_le_mul_left a (ternaryLocalWidth_sum_le_third j s hj hs)

theorem ternaryLocalWidth_weighted_sum_eq_seven_twentyseven
    {ι : Type*} [Fintype ι] (a : ℕ) (j : ι → ℕ) (s : ℕ)
    (hj : ∀ i, 3 ≤ j i) (hs : ∑ i, 3 ^ j i = s) :
    ∑ i, a * ternaryLocalWidth (j i) = a * (7 * s / 27) := by
  rw [← Finset.mul_sum, ternaryLocalWidth_sum_eq_seven_twentyseven j s hj hs]

end SymmetricSubgroupAsymptotics
