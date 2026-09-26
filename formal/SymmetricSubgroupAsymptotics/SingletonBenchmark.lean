import SymmetricSubgroupAsymptotics.Foundations
import SymmetricSubgroupAsymptotics.SingletonExtension

/-! The original singleton normalizer is one. Its physical label factor
is absorbed exactly by the odd factorial, with the nonnegative S3 term
of the odd benchmark retained. No asymptotic coefficient estimate enters.
-/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

theorem exactBenchmark_odd_ge_singleton_even (n : ℕ) :
    ((2*n+1 : ℕ) : ℝ) * exactBenchmark (2*n) ≤ exactBenchmark (2*n+1) := by
  have hhalfEven : halfDegree (2*n) = n := by unfold halfDegree; omega
  have hhalfOdd : halfDegree (2*n+1) = n := by unfold halfDegree; omega
  have hparityEven : parity (2*n) = 0 := by unfold parity; omega
  have hcoefEven : parityCoefficient (2*n) = criticalCoefficient n := by
    simp only [parityCoefficient, hhalfEven, hparityEven, zero_ne_one, false_and,
      ite_false, add_zero]
  have hcoefOdd : criticalCoefficient n ≤ parityCoefficient (2*n+1) := by
    rw [parityCoefficient, hhalfOdd]
    apply le_add_of_nonneg_right
    split_ifs
    · exact div_nonneg (criticalCoefficient_nonneg _) (by norm_num)
    · exact le_rfl
  have hcommon : 0 ≤ ((2*n+1).factorial : ℝ) * (binaryGaussianSum n : ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) (by exact_mod_cast (binaryGaussianSum_pos n).le)
  calc
    _ = ((2*n+1).factorial : ℝ) * (binaryGaussianSum n : ℝ) *
        (criticalCoefficient n : ℝ) := by
      rw [exactBenchmark, hhalfEven, hcoefEven, Nat.factorial_succ, Nat.cast_mul]
      ring
    _ ≤ ((2*n+1).factorial : ℝ) * (binaryGaussianSum n : ℝ) *
        (parityCoefficient (2*n+1) : ℝ) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hcoefOdd) hcommon
    _ = exactBenchmark (2*n+1) := by rw [exactBenchmark, hhalfOdd]

/-- The genuine extension family inherits the normalized even count,
for an arbitrary finite original source family and its literal values. -/
theorem singletonExtension_card_div_benchmark_le {F : Type*} [Finite F]
    (n : ℕ) (value : F → Subgroup (Equiv.Perm (Fin (2*n)))) :
    (Nat.card (SingletonExtension.FinFamily (2*n) value) : ℝ) /
        exactBenchmark (2*n+1) ≤ (Nat.card F : ℝ) / exactBenchmark (2*n) := by
  have hcard : (Nat.card (SingletonExtension.FinFamily (2*n) value) : ℝ) ≤
      ((2*n+1 : ℕ) : ℝ) * (Nat.card F : ℝ) := by
    exact_mod_cast SingletonExtension.card_finFamily_le (2*n) value
  apply (div_le_div_iff₀ (exactBenchmark_pos _) (exactBenchmark_pos _)).mpr
  calc
    _ ≤ (((2*n+1 : ℕ) : ℝ) * (Nat.card F : ℝ)) * exactBenchmark (2*n) :=
      mul_le_mul_of_nonneg_right hcard (exactBenchmark_pos _).le
    _ = (Nat.card F : ℝ) * (((2*n+1 : ℕ) : ℝ) * exactBenchmark (2*n)) := by ring
    _ ≤ (Nat.card F : ℝ) * exactBenchmark (2*n+1) :=
      mul_le_mul_of_nonneg_left (exactBenchmark_odd_ge_singleton_even n) (Nat.cast_nonneg _)

end SymmetricSubgroupAsymptotics
