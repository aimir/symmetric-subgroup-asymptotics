import SymmetricSubgroupAsymptotics.BinaryCarrierParameterProfiles

/-! The shared exact (a,T) physical bin belongs to the complete original
profile family at support 2a+4T. This installs the original small-support
estimate in the same bin interface as the Hall and reserve regimes. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.BinaryCarrierParameterSmallSupport

open BinaryCarrierOriginalCyclicFourHall BinaryCarrierSmallSupportProfiles
open BinaryCarrierParameterProfiles

theorem weightedSum_le_support (R a T : ℕ) :
    weightedSum R a T ≤ BinaryCarrierSmallSupportPhysical.weightedSum R (2*a+4*T) := by
  unfold weightedSum BinaryCarrierSmallSupportPhysical.weightedSum
  apply Finset.sum_le_sum
  intro p _
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset _ _)
  intro q _ _
  apply div_nonneg
  · exact Nat.cast_nonneg _
  · unfold BinaryCarrierMixedProfile.originalDenominator
    positivity

/-- The bound holds for the same literal physical bin as the other two
regimes. Only its actual positive support and the physical cutoff occur. -/
theorem eventually_physical_card_div_le :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ R a T : ℕ,
      n=R+2*a+4*T → 0<2*a+4*T →
      ((2*a+4*T : ℕ) : ℝ) ≤ Real.sqrt (n : ℝ)/4 →
      (Nat.card (PhysicalFamily R a T (Fin (2*(R+2*a+4*T)))) : ℝ) /
        exactBenchmark (2*(R+2*a+4*T)) ≤ (2 : ℝ)^(-(n : ℝ)/4) := by
  filter_upwards [eventually_weighted_profile_sum_le] with n hn
  intro R a T hN hC hcut
  apply (card_div_benchmark_le_weightedSum R a T).trans
  have hRC : R+(2*a+4*T)=n := by omega
  have hs := hn R (2*a+4*T) hRC hC hcut
    (fun _ => BinaryCarrierSmallSupportPhysical.profilesAtSupport (2*a+4*T))
    (fun _ _ q hq => (BinaryCarrierSmallSupportPhysical.mem_profilesAtSupport _ _).mp hq)
  have hden : 0 ≤ (criticalCoefficient (R+2*a+4*T) : ℝ) *
      (binaryGaussianSum (R+2*a+4*T) : ℝ) := by
    exact mul_nonneg (by exact_mod_cast (criticalCoefficient_pos _).le)
      (by exact_mod_cast (binaryGaussianSum_pos _).le)
  apply (div_le_div_of_nonneg_right (weightedSum_le_support R a T) hden).trans
  simpa only [BinaryCarrierSmallSupportPhysical.weightedSum, hN] using hs

end SymmetricSubgroupAsymptotics.BinaryCarrierParameterSmallSupport
