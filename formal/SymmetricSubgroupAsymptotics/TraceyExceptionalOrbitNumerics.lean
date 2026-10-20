import SymmetricSubgroupAsymptotics.TraceyBinaryFiveSixteenths
import Mathlib.Data.Nat.Choose.Sum

/-! Numerical deductions from the literal binomial orbit multiplicities in
Tracey, Corollary 3.12. No module estimate is a hypothesis here. -/
set_option autoImplicit false
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics

/-- Paying three binary parts per orbit still suffices. -/
theorem tracey_binomial_orbit_capacity_sum (e t₁ t : ℕ) (ht : t₁ ≤ t) :
    (∑ k ∈ Finset.range (e + 1),
      (e.choose k * 2 ^ t₁) * (3 * 2 ^ (t - t₁))) =
      3 * 2 ^ (e + t) := by
  calc
    _ = (∑ k ∈ Finset.range (e + 1), e.choose k) *
        (3 * (2 ^ t₁ * 2 ^ (t - t₁))) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = 3 * 2 ^ (e + t) := by
      rw [Nat.sum_range_choose, ← pow_add, Nat.add_sub_of_le ht, pow_add]
      ring

/-- The exclusion of the PSL₂(3) case gives `a ≥ 3`. Even the coarse
three-binary-parts payment then costs at most one quarter of the degree. -/
theorem tracey_binomial_orbit_capacity_quarter (a e t : ℕ)
    (ha : 3 ≤ a) (he : 1 ≤ e) :
    4 * (3 * 2 ^ (e + t)) ≤ 3 * 2 ^ (e * a + t) := by
  have hexp : e + t + 2 ≤ e * a + t := by nlinarith
  have hp := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hexp
  have hpow : 2 ^ (e + t + 2) = 4 * 2 ^ (e + t) := by
    rw [pow_add]
    norm_num
    ring
  rw [hpow] at hp
  nlinarith

theorem tracey_binomial_orbit_capacity_five_sixteenths (a e t : ℕ)
    (ha : 3 ≤ a) (he : 1 ≤ e) :
    16 * (3 * 2 ^ (e + t)) ≤ 5 * (3 * 2 ^ (e * a + t)) := by
  have h := tracey_binomial_orbit_capacity_quarter a e t ha he
  omega

end SymmetricSubgroupAsymptotics
