import SymmetricSubgroupAsymptotics.BinaryZeroCutWideParameters

/-! Numerical consequences of an actual binary section separator.
The fixed-space bound is retained explicitly, including its role in
the natural subtraction in the image-line budget. These are scalar
inequalities, not existence of a group-theoretic cut or its installation. -/
set_option autoImplicit false

namespace SymmetricSubgroupAsymptotics

/-- The normalized middle binomial coefficient is at most 3/8 from
pair exponent three onward. -/
theorem binary_middle_le_three_eighths (k : ℕ) (hk : 3 ≤ k) :
    8 * k.choose (k/2) ≤ 3 * 2^k := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
      calc
        8 * (k+1).choose ((k+1)/2) ≤ 8 * (2*k.choose (k/2)) :=
          Nat.mul_le_mul_left 8 (binary_middle_succ_le_twice k)
        _ = 2 * (8*k.choose (k/2)) := by ring
        _ ≤ 2 * (3*2^k) := Nat.mul_le_mul_left 2 ih
        _ = 3 * 2^(k+1) := by rw [pow_succ]; ring

/-- The doubled previous middle width consumes at most 3/8 of the
original pair degree. -/
theorem binary_previous_middle_budget (k : ℕ) (hk : 4 ≤ k) :
    8 * (2*(k-1).choose ((k-1)/2)) ≤ 3*2^k := by
  have hm := binary_middle_le_three_eighths (k-1) (by omega)
  have hp : 2^k = 2 * 2^(k-1) := by
    conv_lhs => rw [← Nat.sub_add_cancel (show 1 ≤ k by omega)]
    rw [pow_succ]
    exact Nat.mul_comm _ _
  rw [hp]
  omega

/-- The actual fixed-space bound prevents truncation from discarding t
in the line-slice budget D−t. -/
theorem binary_fixed_rank_le_previous_middle (k t : ℕ) (hk : 1 ≤ k)
    (ht : t ≤ k.choose (k/2)) :
    t ≤ 2*(k-1).choose ((k-1)/2) := by
  have hm := binary_middle_succ_le_twice (k-1)
  rw [Nat.sub_add_cancel hk] at hm
  exact ht.trans hm

/-- A section of at most half the pair degree has strict central-cut
cost from the ordinary separator alone, for every pair exponent k≥4.
The hypothesis t≤B_k is essential when D−t is a natural subtraction. -/
theorem binary_small_section_separator_cost (k t ell q : ℕ)
    (hk : 4 ≤ k) (ht : t ≤ k.choose (k/2))
    (hsection : 2*(t+ell) ≤ 2^k)
    (hseparator : 2*q ≤ ell + max 1 (2*(k-1).choose ((k-1)/2)-t)) :
    2*t + 2*q + 2 ≤ 2^k := by
  have htD := binary_fixed_rank_le_previous_middle k t (by omega) ht
  have hD := binary_previous_middle_budget k hk
  have hlarge : 16 ≤ 2^k := by
    have h := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hk
    exact h
  have heven : 2^k = 2 * 2^(k-1) := by
    conv_lhs => rw [← Nat.sub_add_cancel (show 1 ≤ k by omega)]
    rw [pow_succ]
    exact Nat.mul_comm _ _
  omega

theorem binary_small_section_separator_cost_le_sub_two (k t ell q : ℕ)
    (hk : 4 ≤ k) (ht : t ≤ k.choose (k/2))
    (hsection : 2*(t+ell) ≤ 2^k)
    (hseparator : 2*q ≤ ell + max 1 (2*(k-1).choose ((k-1)/2)-t)) :
    2*t + 2*q ≤ 2^k-2 := by
  have h := binary_small_section_separator_cost k t ell q hk ht hsection hseparator
  omega

/-- Independent functionals give q≤t; their common kernel has dimension
t−q and the literal central-cut cost is 2(t−q)+4q. -/
theorem binary_small_section_central_cut_cost (k t ell q : ℕ)
    (hk : 4 ≤ k) (ht : t ≤ k.choose (k/2)) (hq : q ≤ t)
    (hsection : 2*(t+ell) ≤ 2^k)
    (hseparator : 2*q ≤ ell + max 1 (2*(k-1).choose ((k-1)/2)-t)) :
    2*(t-q) + 4*q ≤ 2^k-2 := by
  have h := binary_small_section_separator_cost_le_sub_two k t ell q
    hk ht hsection hseparator
  omega

/-- Once a separate actual faithful-section theorem identifies or bounds
the quotient's central involution rank by B_k, the new character test's
sufficient rank inequality follows at physical width 2*2^k. -/
theorem binary_middle_rank_seven_character_budget (k z : ℕ)
    (hk : 4 ≤ k) (hz : z ≤ k.choose (k/2)) :
    16*z ≤ 3*(2*2^k) := by
  have h := binary_middle_le_three_eighths k (by omega)
  omega

end SymmetricSubgroupAsymptotics
