import SymmetricSubgroupAsymptotics.BinaryCarrierParameterUnion
import SymmetricSubgroupAsymptotics.BinaryCarrierParameterSmallSupport
import SymmetricSubgroupAsymptotics.BinaryCarrierHallProfiles
import SymmetricSubgroupAsymptotics.BinaryCarrierReserveProfiles

/-!
# Completion of the original finite-alphabet binary mixture

This is the literal union of all positive-support profiles made from the
original regular C4 action and the twelve specified carrier actions, with
all original critical coordinates allowed. The three counting regimes
are installed from proved theorems on the same physical bins. No count,
weight or asymptotic estimate is a premise of the final result.

The conclusion is confined to this finite alphabet on even degree. It
does not classify all binary permutation groups or close T1, nonbinary
fusion, odd-degree markers, or physical owner exclusions.
-/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryCarrierMixtureCompletion

open BinaryCarrierParameterProfiles BinaryCarrierParameterUnion

/-- The common rate before summing the original parameter bins. -/
def binRate : ℝ := 29/1490432

theorem binRate_pos : 0 < binRate := by norm_num [binRate]

/-- Actual subgroups of the one original labelled set, with positive
noncritical support and an original thirteen-colour full-profile chart. -/
abbrev Family (n : ℕ) := BinaryCarrierParameterUnion.Family n (fun _ _ => True)

private theorem small_rate_le (n : ℕ) :
    (2 : ℝ)^(-(n : ℝ)/4) ≤ (2 : ℝ)^(-binRate*(n : ℝ)) := by
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  norm_num [binRate] at *
  nlinarith

private theorem hall_rate_le (n : ℕ) :
    (2 : ℝ)^(-(n : ℝ)/50) ≤ (2 : ℝ)^(-binRate*(n : ℝ)) := by
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  norm_num [binRate] at *
  nlinarith

/-- Every positive-support original bin lies in one of the three proved
regimes. The Hall boundary and small-support boundary are both included. -/
theorem eventually_bin_card_div_benchmark_le :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ b : bins n (fun _ _ => True),
      (Nat.card (PhysicalFamily (n-(2*b.1.1+4*b.1.2)) b.1.1 b.1.2 (Fin (2*n))) : ℝ) /
        exactBenchmark (2*n) ≤ (2 : ℝ)^(-binRate*(n : ℝ)) := by
  filter_upwards [BinaryCarrierParameterSmallSupport.eventually_physical_card_div_le,
    BinaryCarrierHallProfiles.eventually_physical_card_div_le,
    BinaryCarrierReserveProfiles.eventually_card_div_benchmark_le] with n hsmall hhall hreserve
  intro b
  have hb := bin_properties n (fun _ _ => True) b
  have hN := bin_degree n (fun _ _ => True) b
  by_cases hcut : ((2*b.1.1+4*b.1.2 : ℕ) : ℝ) ≤ Real.sqrt (n : ℝ)/4
  · have h := hsmall (n-(2*b.1.1+4*b.1.2)) b.1.1 b.1.2 hN.symm hb.1 hcut
    rw [hN] at h
    exact h.trans (small_rate_le n)
  · by_cases hHall : 140*b.1.2 ≤ b.1.1
    · have ha : 1 ≤ b.1.1 := by omega
      have h := hhall (n-(2*b.1.1+4*b.1.2)) b.1.1 b.1.2 hN.symm ha hHall
      rw [hN] at h
      exact h.trans (hall_rate_le n)
    · have h := hreserve (n-(2*b.1.1+4*b.1.2)) b.1.1 b.1.2 hN
        (Nat.lt_of_not_ge hHall) (lt_of_not_ge hcut)
      exact h

/-- All original parameter bins are included and their polynomial number
is absorbed. The exact benchmark and original profile denominators were
retained throughout the three branches and the physical union. -/
theorem eventually_card_div_benchmark_le :
    ∀ᶠ n : ℕ in Filter.atTop,
      (Nat.card (Family n) : ℝ) / exactBenchmark (2*n) ≤
        (2 : ℝ)^(-(29/2980864)*(n : ℝ)) := by
  have h := BinaryCarrierParameterUnion.eventually_card_div_benchmark_le
    (fun _ _ _ => True) binRate binRate_pos eventually_bin_card_div_benchmark_le
  have hr : binRate/2 = (29/2980864 : ℝ) := by norm_num [binRate]
  simpa only [Family, hr] using h

end SymmetricSubgroupAsymptotics.BinaryCarrierMixtureCompletion
