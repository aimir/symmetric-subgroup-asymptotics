import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-! Exact arithmetic scope left after the two infinite affine class
bounds. This enumerates prime powers, not groups or action catalogues. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.SmallAffinePrimePowerDegrees

def ResidualDegree (n : ℕ) : Prop :=
  n=4 ∨ n=5 ∨ n=7 ∨ n=8 ∨ n=9 ∨ n=16 ∨ n=25 ∨ n=27 ∨ n=32 ∨ n=49

theorem residual_of_small_prime_power (p e n : ℕ) (hp : Nat.Prime p)
    (heq : n=p^e) (hn4 : 4 ≤ n) (hn64 : n < 64)
    (hprime : ¬ (11 ≤ n ∧ Nat.Prime n)) : ResidualDegree n := by
  by_cases he0 : e=0
  · simp only [he0,pow_zero] at heq
    omega
  by_cases he1 : e=1
  · have hnprime : Nat.Prime n := by simpa only [heq,he1,pow_one] using hp
    have hn11 : n < 11 := by
      by_contra h
      exact hprime ⟨Nat.le_of_not_gt h, hnprime⟩
    unfold ResidualDegree
    interval_cases n <;> norm_num at *
  have he2 : 2 ≤ e := by omega
  have hple : p^2 ≤ p^e := Nat.pow_le_pow_right hp.pos he2
  have hp7 : p ≤ 7 := by
    rw [← heq,pow_two] at hple
    nlinarith
  have htwo : (2:ℕ)^e ≤ p^e := Nat.pow_le_pow_left hp.two_le _
  have he6 : e < 6 := by
    apply (Nat.pow_lt_pow_iff_right (by decide : 1 < (2:ℕ))).mp
    calc
      (2:ℕ)^e ≤ p^e := htwo
      _ = n := heq.symm
      _ < 2^6 := by norm_num; exact hn64
  unfold ResidualDegree
  interval_cases p <;> interval_cases e <;> norm_num at *
  all_goals omega

end SymmetricSubgroupAsymptotics.SmallAffinePrimePowerDegrees
