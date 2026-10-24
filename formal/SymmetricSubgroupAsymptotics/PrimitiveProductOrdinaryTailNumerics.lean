import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-! Scalar dyadic budgets for the ordinary product-index socle recurrence.
The estimates do not assert a simple-group generator bound or an outer
automorphism bound. They are independent of any permutation-generator input. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.PrimitiveProductOrdinaryTailNumerics

private theorem polynomial_step (m : ℕ) (hm : 10 ≤ m) :
    9*(m+2)*((m+2)^2+5*(m+2))^2 ≤
      4*(9*(m+1)*((m+1)^2+5*(m+1))^2) := by
  obtain ⟨k,rfl⟩ : ∃ k : ℕ, m = k+10 := ⟨m-10,by omega⟩
  nlinarith only [Nat.zero_le (k^5),Nat.zero_le (k^4),Nat.zero_le (k^3),
    Nat.zero_le (k^2),Nat.zero_le k]

theorem linear_budget (m : ℕ) (hm : 10 ≤ m) : 36*(m+1) ≤ 2^m := by
  induction m,hm using Nat.le_induction with
  | base => decide
  | succ m hm ih =>
    calc
      36*(m+1+1) ≤ 2*(36*(m+1)) := by omega
      _ ≤ 2*2^m := Nat.mul_le_mul_left _ ih
      _ = 2^(m+1) := by rw [pow_succ]; omega

theorem polynomial_budget (m : ℕ) (hm : 10 ≤ m) :
    9*(m+1)*((m+1)^2+5*(m+1))^2 ≤ 4*4^m := by
  induction m,hm using Nat.le_induction with
  | base => decide
  | succ m hm ih =>
    calc
      9*(m+1+1)*((m+1+1)^2+5*(m+1+1))^2 ≤
          4*(9*(m+1)*((m+1)^2+5*(m+1))^2) := by
        simpa only [Nat.add_assoc] using polynomial_step m hm
      _ ≤ 4*(4*4^m) := Nat.mul_le_mul_left _ ih
      _ = 4*4^(m+1) := by rw [pow_succ]; omega

end SymmetricSubgroupAsymptotics.PrimitiveProductOrdinaryTailNumerics
