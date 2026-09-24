import SymmetricSubgroupAsymptotics.Statements

/-! Finiteness and positivity of the actual counts and exact benchmark. -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace SymmetricSubgroupAsymptotics

theorem subgroup_finite (n : ℕ) : Finite (Subgroup (Equiv.Perm (Fin n))) :=
  inferInstance

theorem subspace_finite (r : ℕ) : Finite (Submodule (ZMod 2) (Fin r → ZMod 2)) :=
  inferInstance

theorem subgroupCount_pos (n : ℕ) : 0 < subgroupCount n := by
  exact Nat.card_pos

theorem binarySubspaceCount_pos (r : ℕ) : 0 < binarySubspaceCount r := by
  exact Nat.card_pos

@[simp] theorem binarySubspaceCount_zero : binarySubspaceCount 0 = 1 := by
  simp [binarySubspaceCount]

@[simp] theorem subgroupCount_zero : subgroupCount 0 = 1 := by
  simp [subgroupCount]

@[simp] theorem subgroupCount_one : subgroupCount 1 = 1 := by
  simp [subgroupCount]

/-- Every denominator in the finite Gaussian product is strictly positive. -/
theorem binaryGaussian_denominator_pos {k i : ℕ} (hi : i < k) :
    (0 : ℚ) < 2 ^ k - 2 ^ i :=
  sub_pos.mpr (pow_lt_pow_right₀ (by norm_num : (1 : ℚ) < 2) hi)

theorem binaryGaussianCoefficient_pos {r k : ℕ} (hk : k ≤ r) :
    0 < binaryGaussianCoefficient r k := by
  unfold binaryGaussianCoefficient
  apply Finset.prod_pos
  intro i hi
  have hik : i < k := Finset.mem_range.mp hi
  exact div_pos (binaryGaussian_denominator_pos (lt_of_lt_of_le hik hk))
    (binaryGaussian_denominator_pos hik)

@[simp] theorem binaryGaussianCoefficient_zero (r : ℕ) :
    binaryGaussianCoefficient r 0 = 1 := by
  simp [binaryGaussianCoefficient]

theorem binaryGaussianSum_pos (r : ℕ) : 0 < binaryGaussianSum r := by
  unfold binaryGaussianSum
  apply Finset.sum_pos'
  · intro k hk
    exact (binaryGaussianCoefficient_pos (by simpa using hk)).le
  · exact ⟨0, by simp, by simp⟩

@[simp] theorem binaryGaussianSum_zero : binaryGaussianSum 0 = 1 := by
  simp [binaryGaussianSum]

theorem criticalCoefficient_nonneg (r : ℕ) : 0 ≤ criticalCoefficient r := by
  unfold criticalCoefficient
  apply Finset.sum_nonneg
  intro a ha
  apply Finset.sum_nonneg
  intro b hb
  apply Finset.sum_nonneg
  intro d hd
  split_ifs <;> positivity

theorem criticalCoefficient_pos (r : ℕ) : 0 < criticalCoefficient r := by
  unfold criticalCoefficient
  apply Finset.sum_pos'
  · intro a ha
    apply Finset.sum_nonneg
    intro b hb
    apply Finset.sum_nonneg
    intro d hd
    split_ifs <;> positivity
  · refine ⟨r, by simp, ?_⟩
    apply Finset.sum_pos'
    · intro b hb
      apply Finset.sum_nonneg
      intro d hd
      split_ifs <;> positivity
    · refine ⟨0, by simp, ?_⟩
      apply Finset.sum_pos'
      · intro d hd
        split_ifs <;> positivity
      · refine ⟨0, by simp, ?_⟩
        simp only [mul_zero, add_zero, ite_true, pow_zero, Nat.factorial_zero,
          Nat.cast_one, mul_one]
        positivity

@[simp] theorem criticalCoefficient_zero : criticalCoefficient 0 = 1 := by
  norm_num [criticalCoefficient]

theorem parityCoefficient_pos (n : ℕ) : 0 < parityCoefficient n := by
  unfold parityCoefficient
  apply add_pos_of_pos_of_nonneg (criticalCoefficient_pos _)
  split_ifs
  · exact div_nonneg (criticalCoefficient_nonneg _) (by norm_num)
  · exact le_rfl

theorem exactBenchmark_pos (n : ℕ) : 0 < exactBenchmark n := by
  unfold exactBenchmark
  exact mul_pos (mul_pos (by exact_mod_cast Nat.factorial_pos n)
    (by exact_mod_cast binaryGaussianSum_pos (halfDegree n)))
    (by exact_mod_cast parityCoefficient_pos n)

@[simp] theorem exactBenchmark_zero : exactBenchmark 0 = 1 := by
  simp [exactBenchmark, parityCoefficient, halfDegree, parity]

@[simp] theorem exactBenchmark_one : exactBenchmark 1 = 1 := by
  simp [exactBenchmark, parityCoefficient, halfDegree, parity]

theorem parity_lt_two (n : ℕ) : parity n < 2 := by
  exact Nat.mod_lt n (by decide)

theorem parity_cases (n : ℕ) : parity n = 0 ∨ parity n = 1 := by
  have := parity_lt_two n
  omega

end SymmetricSubgroupAsymptotics
