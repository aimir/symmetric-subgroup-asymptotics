import SymmetricSubgroupAsymptotics.BinaryCarrierOddSingleton
import SymmetricSubgroupAsymptotics.BinaryCarrierS3Completion
import SymmetricSubgroupAsymptotics.BinaryMixturePolynomialDecay

/-! The actual union of the singleton and natural-S3 positive-support
mixture sectors on one original odd point set. Witnesses and overlaps are
forgotten. This completes these two sectors of the selected finite alphabet;
it does not assert that they cover all odd permutation subgroups.
-/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryCarrierOddMixtureCompletion

/-- Literal disjunction on the ambient subgroup, rather than a tagged
sum whose two presentations would be counted as different subgroups. -/
abbrev Family (N : ℕ) :=
  {H : Subgroup (Equiv.Perm (Fin (2*N+1))) //
    (∃ K : BinaryCarrierOddSingleton.Family N, K.1 = H) ∨
      (∃ K : BinaryCarrierS3Completion.Family N, K.1 = H)}

private instance singletonFamilyFinite (N : ℕ) :
    Finite (BinaryCarrierOddSingleton.Family N) := by
  unfold BinaryCarrierOddSingleton.Family SingletonExtension.AllChartsFamily
  infer_instance

private instance s3FamilyFinite (N : ℕ) : Finite (BinaryCarrierS3Completion.Family N) := by
  unfold BinaryCarrierS3Completion.Family BinaryCarrierS3Union.Family
  infer_instance

def decode (N : ℕ) :
    BinaryCarrierOddSingleton.Family N ⊕ BinaryCarrierS3Completion.Family N → Family N
  | .inl K => ⟨K.1, Or.inl ⟨K,rfl⟩⟩
  | .inr K => ⟨K.1, Or.inr ⟨K,rfl⟩⟩

theorem decode_surjective (N : ℕ) : Function.Surjective (decode N) := by
  rintro ⟨H,hH⟩
  rcases hH with ⟨K,rfl⟩ | ⟨K,rfl⟩
  · exact ⟨.inl K,rfl⟩
  · exact ⟨.inr K,rfl⟩

/-- The bound is valid without disjointness or unique marker witnesses. -/
theorem card_le_sum (N : ℕ) :
    Nat.card (Family N) ≤ Nat.card (BinaryCarrierOddSingleton.Family N) +
      Nat.card (BinaryCarrierS3Completion.Family N) := by
  calc
    _ ≤ Nat.card (BinaryCarrierOddSingleton.Family N ⊕ BinaryCarrierS3Completion.Family N) :=
      Nat.card_le_card_of_surjective (decode N) (decode_surjective N)
    _ = _ := Nat.card_sum

theorem card_div_benchmark_le_sum (N : ℕ) :
    (Nat.card (Family N) : ℝ) / exactBenchmark (2*N+1) ≤
      (Nat.card (BinaryCarrierOddSingleton.Family N) : ℝ) / exactBenchmark (2*N+1) +
        (Nat.card (BinaryCarrierS3Completion.Family N) : ℝ) / exactBenchmark (2*N+1) := by
  have hcard : (Nat.card (Family N) : ℝ) ≤
      (Nat.card (BinaryCarrierOddSingleton.Family N) : ℝ) +
        (Nat.card (BinaryCarrierS3Completion.Family N) : ℝ) := by
    exact_mod_cast card_le_sum N
  simpa only [add_div] using
    div_le_div_of_nonneg_right hcard (exactBenchmark_pos (2*N+1)).le

/-- Both actual sectors already have their original weights and full
physical labelling installed. Their union costs at most the factor two. -/
theorem eventually_card_div_benchmark_le_two :
    ∀ᶠ N : ℕ in Filter.atTop,
      (Nat.card (Family N) : ℝ) / exactBenchmark (2*N+1) ≤
        2 * (2 : ℝ)^(-(29/2980864)*(N : ℝ)) := by
  filter_upwards [BinaryCarrierOddSingleton.eventually_card_div_benchmark_le,
    BinaryCarrierS3Completion.eventually_card_div_benchmark_le] with N hsingleton hS3
  calc
    _ ≤ (Nat.card (BinaryCarrierOddSingleton.Family N) : ℝ) / exactBenchmark (2*N+1) +
        (Nat.card (BinaryCarrierS3Completion.Family N) : ℝ) / exactBenchmark (2*N+1) :=
      card_div_benchmark_le_sum N
    _ ≤ (2 : ℝ)^(-(29/2980864)*(N : ℝ)) +
        (2 : ℝ)^(-(29/2980864)*(N : ℝ)) := add_le_add hsingleton hS3
    _ = _ := by ring

/-- Constant absorption leaves an explicit exponential rate in the
half-degree. No count, normalizer, or global odd-coverage hypothesis enters. -/
theorem eventually_card_div_benchmark_le :
    ∀ᶠ N : ℕ in Filter.atTop,
      (Nat.card (Family N) : ℝ) / exactBenchmark (2*N+1) ≤
        (2 : ℝ)^(-(29/5961728)*(N : ℝ)) := by
  filter_upwards [eventually_card_div_benchmark_le_two,
    BinaryMixtureNumerics.eventually_polynomial_mul_two_rpow_le
      2 (by norm_num) 0 (29/2980864) (by norm_num)] with N hN habsorb
  apply hN.trans
  simpa only [pow_zero, mul_one,
    show (29/2980864 : ℝ)/2 = 29/5961728 by norm_num] using habsorb

end SymmetricSubgroupAsymptotics.BinaryCarrierOddMixtureCompletion
