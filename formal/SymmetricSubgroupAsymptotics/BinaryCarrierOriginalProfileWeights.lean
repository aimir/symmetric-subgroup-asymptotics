import SymmetricSubgroupAsymptotics.BinaryCarrierOriginalCyclicFourHall
import SymmetricSubgroupAsymptotics.BinaryCarrierProfileWeights

/-! The complete finite profile-weight sum for the same thirteen original
colours as the mixed Hall consumer: the regular C4 translation action and
the twelve distinct physical carrier actions. Exact normalizer orders are
retained but need not be evaluated to obtain a uniform upper bound. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.BinaryCarrierOriginalCyclicFourHall

theorem originalTarget_card : Fintype.card Target = 13 := by decide

/-- Any specified finite collection of the thirteen original multiplicity
functions costs at most exp(13), after the critical weight is factored out. -/
theorem original_profile_weight_sum_le (p : CriticalProfile)
    (S : Finset (Target → ℕ)) :
    ∑ m ∈ S, 1 / BinaryCarrierMixedProfile.originalDenominator points action p m ≤
      (p.weight : ℝ) * Real.exp 13 := by
  simpa only [originalTarget_card, Nat.cast_ofNat] using
    BinaryCarrierProfileWeights.sum_reciprocal_le points action p S

/-- The original critical profiles are summed exactly at their own rank;
their coefficient shift to the complete degree remains explicit downstream. -/
theorem original_critical_profile_weight_sum_le (R : ℕ)
    (S : CriticalProfile → Finset (Target → ℕ)) :
    ∑ p : criticalProfiles R, ∑ m ∈ S p.1,
      1 / BinaryCarrierMixedProfile.originalDenominator points action p.1 m ≤
        (criticalCoefficient R : ℝ) * Real.exp 13 := by
  simpa only [originalTarget_card, Nat.cast_ofNat] using
    BinaryCarrierProfileWeights.critical_profile_sum_reciprocal_le points action R S

theorem original_profile_count_sum_le (p : CriticalProfile)
    (S : Finset (Target → ℕ)) (v : (Target → ℕ) → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hv : ∀ m ∈ S, v m ≤ C) :
    ∑ m ∈ S, v m / BinaryCarrierMixedProfile.originalDenominator points action p m ≤
      (p.weight : ℝ) * Real.exp 13 * C := by
  simpa only [originalTarget_card, Nat.cast_ofNat] using
    BinaryCarrierProfileWeights.sum_div_le points action p S v C hC hv

/-- Summing every critical profile at one rank pays its exact coefficient,
after the entire specified finite noncritical-profile sum. -/
theorem original_critical_profile_count_sum_le (R : ℕ)
    (S : CriticalProfile → Finset (Target → ℕ))
    (v : CriticalProfile → (Target → ℕ) → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hv : ∀ p ∈ criticalProfiles R, ∀ m ∈ S p, v p m ≤ M) :
    ∑ p : criticalProfiles R, ∑ m ∈ S p.1,
      v p.1 m / BinaryCarrierMixedProfile.originalDenominator points action p.1 m ≤
        (criticalCoefficient R : ℝ) * Real.exp 13 * M := by
  calc
    _ ≤ ∑ p : criticalProfiles R, (p.1.weight : ℝ) * Real.exp 13 * M :=
      Finset.sum_le_sum fun p _ =>
        original_profile_count_sum_le p.1 (S p.1) (v p.1) M hM (hv p.1 p.2)
    _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_mul, criticalProfile_weight_sum_real]

/-- Normalize at the full half-degree R+C, paying the whole critical
coefficient shift C. Neither the support shift nor the Gaussian count is
replaced by a count of carrier colours or master occurrences. -/
theorem original_shifted_profile_count_sum_le (R C : ℕ)
    (S : CriticalProfile → Finset (Target → ℕ))
    (v : CriticalProfile → (Target → ℕ) → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hv : ∀ p ∈ criticalProfiles R, ∀ m ∈ S p,
      v p m ≤ (binaryGaussianSum (R+C) : ℝ) * M) :
    (∑ p : criticalProfiles R, ∑ m ∈ S p.1,
      v p.1 m / BinaryCarrierMixedProfile.originalDenominator points action p.1 m) /
        ((criticalCoefficient (R+C) : ℝ) * (binaryGaussianSum (R+C) : ℝ)) ≤
          Real.exp 13 * (2 * ((R+C : ℕ) : ℝ))^C * M := by
  have hG : (0 : ℝ) < binaryGaussianSum (R+C) := by
    exact_mod_cast binaryGaussianSum_pos (R+C)
  have hc : (0 : ℝ) < criticalCoefficient (R+C) := by
    exact_mod_cast criticalCoefficient_pos (R+C)
  have hshift : (criticalCoefficient R : ℝ) ≤
      (2 * ((R+C : ℕ) : ℝ))^C * (criticalCoefficient (R+C) : ℝ) := by
    have h := criticalCoefficient_shift_le (R+C) C (by omega)
    rw [Nat.add_sub_cancel] at h
    exact_mod_cast h
  apply (div_le_iff₀ (mul_pos hc hG)).mpr
  calc
    _ ≤ (criticalCoefficient R : ℝ) * Real.exp 13 *
        ((binaryGaussianSum (R+C) : ℝ) * M) :=
      original_critical_profile_count_sum_le R S v _ (mul_nonneg hG.le hM) hv
    _ ≤ ((2 * ((R+C : ℕ) : ℝ))^C * (criticalCoefficient (R+C) : ℝ)) *
        Real.exp 13 * ((binaryGaussianSum (R+C) : ℝ) * M) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hshift (Real.exp_pos _).le)
        (mul_nonneg hG.le hM)
    _ = _ := by ring

end SymmetricSubgroupAsymptotics.BinaryCarrierOriginalCyclicFourHall
