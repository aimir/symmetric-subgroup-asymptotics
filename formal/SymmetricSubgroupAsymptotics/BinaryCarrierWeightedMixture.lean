import SymmetricSubgroupAsymptotics.BinaryCarrierParameterSmallSupport
import SymmetricSubgroupAsymptotics.BinaryCarrierHallProfiles
import SymmetricSubgroupAsymptotics.BinaryCarrierReserveProfiles

/-! Uniform decay of the actual original weighted profile bin. The proof
combines the three weighted estimates directly; it does not reverse the
upper bound from a physical union to a weighted profile sum. Every critical
profile and every original noncritical profile in the bin is retained.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.BinaryCarrierWeightedMixture

open BinaryCarrierParameterProfiles

/-- Small-support decay in the same weighted-bin interface as the Hall
and reserve bounds. The support family contains the exact parameter bin. -/
theorem eventually_small_support_weightedSum_div_le :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ R a T : ℕ,
      R+2*a+4*T=n → 0<2*a+4*T →
      ((2*a+4*T : ℕ) : ℝ) ≤ Real.sqrt (n : ℝ)/4 →
      weightedSum R a T /
        ((criticalCoefficient n : ℝ) * (binaryGaussianSum n : ℝ)) ≤
          (2 : ℝ)^(-(n : ℝ)/4) := by
  filter_upwards [BinaryCarrierSmallSupportProfiles.eventually_weighted_profile_sum_le]
    with n hn
  intro R a T hN hC hcut
  have hRC : R+(2*a+4*T)=n := by omega
  have hs := hn R (2*a+4*T) hRC hC hcut
    (fun _ => BinaryCarrierSmallSupportPhysical.profilesAtSupport (2*a+4*T))
    (fun _ _ q hq => (BinaryCarrierSmallSupportPhysical.mem_profilesAtSupport _ _).mp hq)
  have hden : 0 ≤ (criticalCoefficient n : ℝ) * (binaryGaussianSum n : ℝ) :=
    mul_nonneg (by exact_mod_cast (criticalCoefficient_pos n).le)
      (by exact_mod_cast (binaryGaussianSum_pos n).le)
  apply (div_le_div_of_nonneg_right
    (BinaryCarrierParameterSmallSupport.weightedSum_le_support R a T) hden).trans
  simpa only [BinaryCarrierSmallSupportPhysical.weightedSum] using hs

private theorem small_rate_le (n : ℕ) :
    (2 : ℝ)^(-(n : ℝ)/4) ≤ (2 : ℝ)^(-(29/1490432)*(n : ℝ)) := by
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

private theorem hall_rate_le (n : ℕ) :
    (2 : ℝ)^(-(n : ℝ)/50) ≤ (2 : ℝ)^(-(29/1490432)*(n : ℝ)) := by
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

/-- Every original positive-support weighted bin lies in one of the
three proved regimes. This is a bound on the complete profile sum, not
on its possibly overlapping physical union. No count premise is supplied. -/
theorem eventually_weightedSum_div_le :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ R a T : ℕ,
      R+2*a+4*T=n → 0<2*a+4*T →
      weightedSum R a T /
        ((criticalCoefficient n : ℝ) * (binaryGaussianSum n : ℝ)) ≤
          (2 : ℝ)^(-(29/1490432)*(n : ℝ)) := by
  filter_upwards [eventually_small_support_weightedSum_div_le,
    BinaryCarrierHallProfiles.eventually_weightedSum_div_le,
    BinaryCarrierReserveProfiles.eventually_weightedSum_div_le] with n hsmall hhall hreserve
  intro R a T hN hC
  by_cases hcut : ((2*a+4*T : ℕ) : ℝ) ≤ Real.sqrt (n : ℝ)/4
  · exact (hsmall R a T hN hC hcut).trans (small_rate_le n)
  · by_cases hHall : 140*T ≤ a
    · have ha : 1 ≤ a := by omega
      exact (hhall R a T hN.symm ha hHall).trans (hall_rate_le n)
    · exact hreserve R a T hN (Nat.lt_of_not_ge hHall) (lt_of_not_ge hcut)

end SymmetricSubgroupAsymptotics.BinaryCarrierWeightedMixture
