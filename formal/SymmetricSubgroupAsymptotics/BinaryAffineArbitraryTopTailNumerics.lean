import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-! Two uniform polynomial-versus-exponential budgets for arbitrary
top degrees. They are scalar inequalities, not assertions that the
actual weighted-chief or real-logarithmic inputs have been assembled. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.BinaryAffineArbitraryTopTailNumerics

private theorem first_step (d : ℕ) (hd : 7≤d) :
    3*(d+1)*((d+1)^2+4)^2 ≤ 4*(3*d*(d^2+4)^2) := by
  obtain ⟨k,rfl⟩ : ∃ k : ℕ, d=k+7 := ⟨d-7,by omega⟩
  nlinarith only [Nat.zero_le (k^5),Nat.zero_le (k^4),Nat.zero_le (k^3),
    Nat.zero_le (k^2),Nat.zero_le k]

private theorem second_step (d : ℕ) (hd : 7≤d) :
    3*(2*(d+1)^2+2)^2 ≤ 4*(3*(2*d^2+2)^2) := by
  obtain ⟨k,rfl⟩ : ∃ k : ℕ, d=k+7 := ⟨d-7,by omega⟩
  nlinarith only [Nat.zero_le (k^4),Nat.zero_le (k^3),Nat.zero_le (k^2),
    Nat.zero_le k]

theorem small_log_budget (d : ℕ) (hd : 7≤d) :
    3*d*(d^2+4)^2 ≤ 4*4^d := by
  induction d,hd using Nat.le_induction with
  | base => decide
  | succ d hd ih =>
    calc
      3*(d+1)*((d+1)^2+4)^2 ≤ 4*(3*d*(d^2+4)^2) := first_step d hd
      _ ≤ 4*(4*4^d) := Nat.mul_le_mul_left _ ih
      _ = 4*4^(d+1) := by rw [pow_succ]; omega

theorem large_log_budget (d : ℕ) (hd : 7≤d) :
    3*(2*d^2+2)^2 ≤ 2*4^d := by
  induction d,hd using Nat.le_induction with
  | base => decide
  | succ d hd ih =>
    calc
      3*(2*(d+1)^2+2)^2 ≤ 4*(3*(2*d^2+2)^2) := second_step d hd
      _ ≤ 4*(2*4^d) := Nat.mul_le_mul_left _ ih
      _ = 2*4^(d+1) := by rw [pow_succ]; omega

end SymmetricSubgroupAsymptotics.BinaryAffineArbitraryTopTailNumerics
