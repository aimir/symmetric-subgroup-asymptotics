import SymmetricSubgroupAsymptotics.PrimeGridMiddleCapacity
import Mathlib.Order.Monotone.Basic

/-! Exact middle-binomial rates decrease with the number of coordinates.
This permits a lower primary exponent on every actual Sylow orbit; the
ambient index need not itself be a prime power. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CentralBinomialNormalizedAntitone

theorem middle_succ_le_twice (n : ℕ) :
    (n+1).choose ((n+1)/2) ≤ 2*n.choose (n/2) := by
  by_cases hn : n = 0
  · subst n
    decide
  · have hk : 0 < (n+1)/2 := by omega
    rw [Nat.choose_succ_left n ((n+1)/2) hk]
    have hleft := Nat.choose_le_middle (((n+1)/2)-1) n
    have hright := Nat.choose_le_middle ((n+1)/2) n
    omega

theorem normalized_succ_le (n : ℕ) :
    ((n+1).choose ((n+1)/2) : ℝ)/(2 : ℝ)^(n+1) ≤
      (n.choose (n/2) : ℝ)/(2 : ℝ)^n := by
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ)^(n+1))
    (by positivity : (0 : ℝ) < (2 : ℝ)^n)).mpr
  have h : ((n+1).choose ((n+1)/2) : ℝ) ≤ 2*(n.choose (n/2) : ℝ) := by
    exact_mod_cast middle_succ_le_twice n
  calc
    ((n+1).choose ((n+1)/2) : ℝ)*(2 : ℝ)^n ≤
        (2*(n.choose (n/2) : ℝ))*(2 : ℝ)^n :=
      mul_le_mul_of_nonneg_right h (by positivity)
    _ = (n.choose (n/2) : ℝ)*(2 : ℝ)^(n+1) := by rw [pow_succ]; ring

theorem normalized_antitone :
    Antitone (fun n : ℕ => (n.choose (n/2) : ℝ)/(2 : ℝ)^n) :=
  antitone_nat_of_succ_le normalized_succ_le

/-- A genuine divisor-exponent rate, including exponent zero.  Only the
lower bound on the literal orbit exponent is needed here. -/
theorem primeGrid_primary_choose (p r e : ℕ) (hp : 0 < p) (her : e ≤ r) :
    (primeGridMiddleWidth p r : ℝ) ≤ (p : ℝ)^r*
      ((e*(p-1)).choose ((e*(p-1))/2) : ℝ)/(2 : ℝ)^(e*(p-1)) := by
  have hmono := normalized_antitone (Nat.mul_le_mul_right (p-1) her)
  calc
    (primeGridMiddleWidth p r : ℝ) ≤ (p : ℝ)^r*
        ((r*(p-1)).choose ((r*(p-1))/2) : ℝ)/(2 : ℝ)^(r*(p-1)) :=
      primeGridMiddleWidth_normalized p r hp
    _ = (p : ℝ)^r*
        (((r*(p-1)).choose ((r*(p-1))/2) : ℝ)/(2 : ℝ)^(r*(p-1))) := by ring
    _ ≤ (p : ℝ)^r*
        (((e*(p-1)).choose ((e*(p-1))/2) : ℝ)/(2 : ℝ)^(e*(p-1))) :=
      mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = (p : ℝ)^r*
        ((e*(p-1)).choose ((e*(p-1))/2) : ℝ)/(2 : ℝ)^(e*(p-1)) := by ring

end SymmetricSubgroupAsymptotics.CentralBinomialNormalizedAntitone
