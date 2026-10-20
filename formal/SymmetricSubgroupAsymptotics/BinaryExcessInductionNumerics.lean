import SymmetricSubgroupAsymptotics.BinaryZeroCutWideParameters

/-! The elementary-top branch of the binary excess induction closes by
a discrete Pascal recurrence, without an asymptotic binomial estimate. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics

/-- From pair degree32 onward, the natural-module middle width plus the
entire elementary top rank fits into half the pair degree. -/
theorem binary_middle_add_rank_le_half_power (k : ℕ) (hk : 5 ≤ k) :
    k.choose (k / 2) + k ≤ 2 ^ (k - 1) := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    have hm := binary_middle_succ_le_twice k
    have hp : 2 ^ k = 2 * 2 ^ (k - 1) := by
      conv_lhs => rw [show k = (k - 1) + 1 by omega]
      rw [pow_succ]
      exact Nat.mul_comm _ _
    calc
      (k + 1).choose ((k + 1) / 2) + (k + 1) ≤
          2 * k.choose (k / 2) + 2 * k := by omega
      _ = 2 * (k.choose (k / 2) + k) := by ring
      _ ≤ 2 * 2 ^ (k - 1) := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ ((k + 1) - 1) := by simpa only [Nat.add_sub_cancel] using hp.symm

end SymmetricSubgroupAsymptotics
