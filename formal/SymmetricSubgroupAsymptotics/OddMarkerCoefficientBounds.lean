import SymmetricSubgroupAsymptotics.OddMarkerBinaryErrorTransfer
import SymmetricSubgroupAsymptotics.FusionCold

/-!
# Numerical bounds for the odd binary-error coefficients

The odd repeated-marker frontier multiplies the current and predecessor
binary-error recurrences by two explicit coefficients.  This file proves
that the current coefficient has only linear growth and the predecessor
coefficient has only cubic growth.  Consequently either coefficient can be
absorbed into any exponentially decaying scalar or row estimate.
-/

set_option autoImplicit false
noncomputable section
open Filter

namespace SymmetricSubgroupAsymptotics.OddMarkerCoefficientBounds

open MarkerZeroDefect BinaryPairMomentNormalized
  OddMarkerBinaryErrorTransfer

theorem alpha_nonneg (N : ℕ) : 0 ≤ alpha N := by
  unfold alpha
  exact div_nonneg (by exact_mod_cast criticalCoefficient_nonneg N)
    (by exact_mod_cast (analyticParityCoefficient_positive 1 N).le)

theorem alpha_le_one (N : ℕ) : alpha N ≤ 1 := by
  have hlowerQ : criticalCoefficient N ≤ analyticParityCoefficient 1 N := by
    unfold analyticParityCoefficient
    split_ifs
    · linarith [criticalCoefficient_nonneg (N - 1)]
    · simp
  have hlower : (criticalCoefficient N : ℝ) ≤
      (analyticParityCoefficient 1 N : ℝ) := by
    exact_mod_cast hlowerQ
  unfold alpha
  apply (div_le_one (by exact_mod_cast analyticParityCoefficient_positive 1 N)).mpr
  exact hlower

theorem beta_le_third (N : ℕ) : beta N ≤ (1 / 3 : ℝ) := by
  unfold beta
  linarith [alpha_le_one N]

private theorem fourthRoot_six_mul_le (N : ℕ) :
    (6 * (N : ℝ)) ^ (1 / 4 : ℝ) ≤ 6 * (N : ℝ) + 1 := by
  have hx0 : 0 ≤ 6 * (N : ℝ) := by positivity
  by_cases hx : 1 ≤ 6 * (N : ℝ)
  · calc
      (6 * (N : ℝ)) ^ (1 / 4 : ℝ) ≤ 6 * (N : ℝ) :=
        Real.rpow_le_self_of_one_le hx (by norm_num)
      _ ≤ 6 * (N : ℝ) + 1 := by linarith
  · have hx1 : 6 * (N : ℝ) ≤ 1 := le_of_not_ge hx
    calc
      (6 * (N : ℝ)) ^ (1 / 4 : ℝ) ≤ 1 :=
        Real.rpow_le_one hx0 hx1 (by norm_num)
      _ ≤ 6 * (N : ℝ) + 1 := by linarith

theorem currentCoefficient_nonneg (N : ℕ) :
    0 ≤ currentCoefficient N := by
  unfold currentCoefficient
  exact add_nonneg (alpha_nonneg N)
    (mul_nonneg (OddMarkerBinaryErrorTransfer.beta_nonneg N) (by positivity))

/-- A deliberately coarse polynomial envelope.  Its role is only to expose
the subexponential size of the exact odd current coefficient. -/
theorem currentCoefficient_le (N : ℕ) :
    currentCoefficient N ≤ 4 * ((N : ℝ) + 1) := by
  have hr := fourthRoot_six_mul_le N
  have hb := beta_le_third N
  have hs0 : 0 ≤ 7 + (6 * (N : ℝ)) ^ (1 / 4 : ℝ) := by positivity
  have hs : 7 + (6 * (N : ℝ)) ^ (1 / 4 : ℝ) ≤
      8 + 6 * (N : ℝ) := by linarith
  calc
    currentCoefficient N =
        alpha N + beta N * (7 + (6 * (N : ℝ)) ^ (1 / 4 : ℝ)) := rfl
    _ ≤ 1 + (1 / 3 : ℝ) * (7 + (6 * (N : ℝ)) ^ (1 / 4 : ℝ)) := by
      apply add_le_add (alpha_le_one N)
      exact mul_le_mul_of_nonneg_right hb hs0
    _ ≤ 1 + (1 / 3 : ℝ) * (8 + 6 * (N : ℝ)) := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hs (by norm_num))
    _ ≤ 4 * ((N : ℝ) + 1) := by
      have hN : 0 ≤ (N : ℝ) := by positivity
      linarith

theorem predecessorCoefficient_nonneg (N : ℕ) :
    0 ≤ predecessorCoefficient N := by
  unfold predecessorCoefficient
  exact mul_nonneg (by positivity)
    (div_nonneg (pairScale_pos (N - 1)).le (pairScale_pos N).le)

private theorem pairScale_predecessor_ratio_le (N : ℕ) (hN : 1 ≤ N) :
    pairScale (N - 1) / pairScale N ≤
      2 * eulerProduct⁻¹ ^ 2 * ((N : ℝ) + 1) ^ 2 := by
  have hG0 : 0 < (binaryGaussianSum (N - 1) : ℝ) := by
    exact_mod_cast binaryGaussianSum_pos (N - 1)
  have hG1 : 0 < (binaryGaussianSum N : ℝ) := by
    exact_mod_cast binaryGaussianSum_pos N
  have hc0 : 0 < (criticalCoefficient (N - 1) : ℝ) := by
    exact_mod_cast criticalCoefficient_pos (N - 1)
  have hc1 : 0 < (criticalCoefficient N : ℝ) := by
    exact_mod_cast criticalCoefficient_pos N
  have hG := fusionGaussianRatio_le (N - 1) 1
  have hGpre :
      (binaryGaussianSum (N - 1) : ℝ) / binaryGaussianSum N ≤
        eulerProduct⁻¹ ^ 2 * (((N - 1 : ℕ) : ℝ) + 1) *
          (2 : ℝ) ^ (-((N - 1 : ℕ) : ℝ) / 2) := by
    simpa [Nat.sub_add_cancel hN] using hG
  have hcast : (((N - 1 : ℕ) : ℝ) + 1) = (N : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel hN
  have hG' :
      (binaryGaussianSum (N - 1) : ℝ) / binaryGaussianSum N ≤
        eulerProduct⁻¹ ^ 2 * (N : ℝ) *
          (2 : ℝ) ^ (-((N - 1 : ℕ) : ℝ) / 2) := by
    rw [← hcast]
    exact hGpre
  have hp : (2 : ℝ) ^ (-((N - 1 : ℕ) : ℝ) / 2) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
    have hprev : 0 ≤ (((N - 1 : ℕ) : ℝ)) := by positivity
    linarith
  have hG'' :
      (binaryGaussianSum (N - 1) : ℝ) / binaryGaussianSum N ≤
        eulerProduct⁻¹ ^ 2 * (N : ℝ) := by
    calc
      _ ≤ eulerProduct⁻¹ ^ 2 * (N : ℝ) *
          (2 : ℝ) ^ (-((N - 1 : ℕ) : ℝ) / 2) := hG'
      _ ≤ eulerProduct⁻¹ ^ 2 * (N : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      _ = _ := by ring
  have hcQ := criticalCoefficient_shift_le N 1 hN
  simp only [pow_one] at hcQ
  have hcR : (criticalCoefficient (N - 1) : ℝ) ≤
      2 * (N : ℝ) * criticalCoefficient N := by
    exact_mod_cast hcQ
  have hcRatio :
      (criticalCoefficient (N - 1) : ℝ) / criticalCoefficient N ≤
        2 * (N : ℝ) := by
    apply (div_le_iff₀ hc1).mpr
    simpa only [mul_assoc] using hcR
  have hsplit : pairScale (N - 1) / pairScale N =
      ((binaryGaussianSum (N - 1) : ℝ) / binaryGaussianSum N) *
        ((criticalCoefficient (N - 1) : ℝ) / criticalCoefficient N) := by
    unfold pairScale
    field_simp [hG1.ne', hc1.ne']
    <;> ring
  rw [hsplit]
  calc
    _ ≤ (eulerProduct⁻¹ ^ 2 * (N : ℝ)) * (2 * (N : ℝ)) :=
      mul_le_mul hG'' hcRatio
        (div_nonneg hc0.le hc1.le) (by positivity)
    _ = 2 * eulerProduct⁻¹ ^ 2 * (N : ℝ) ^ 2 := by ring
    _ ≤ 2 * eulerProduct⁻¹ ^ 2 * ((N : ℝ) + 1) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_left₀ (by positivity) (by linarith) 2

/-- The predecessor coefficient is also polynomial despite containing the
exact adjacent benchmark ratio. -/
theorem predecessorCoefficient_le (N : ℕ) (hN : 1 ≤ N) :
    predecessorCoefficient N ≤
      2 * eulerProduct⁻¹ ^ 2 * ((N : ℝ) + 1) ^ 3 := by
  have hr := pairScale_predecessor_ratio_le N hN
  have hf : (((N - 1 : ℕ) : ℝ) / 4) ≤ (N : ℝ) + 1 := by
    have h0 : 0 ≤ (N : ℝ) := by positivity
    have hs : ((N - 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.sub_le N 1
    linarith
  unfold predecessorCoefficient
  calc
    (((N - 1 : ℕ) : ℝ) / 4) * (pairScale (N - 1) / pairScale N) ≤
        ((N : ℝ) + 1) *
          (2 * eulerProduct⁻¹ ^ 2 * ((N : ℝ) + 1) ^ 2) :=
      mul_le_mul hf hr
        (div_nonneg (pairScale_pos (N - 1)).le (pairScale_pos N).le)
        (by positivity)
    _ = 2 * eulerProduct⁻¹ ^ 2 * ((N : ℝ) + 1) ^ 3 := by ring

/-- Linear growth costs at most half of any prescribed exponential rate. -/
theorem eventually_currentCoefficient_mul_exponential_le {c : ℝ} (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop,
      currentCoefficient N * (2 : ℝ) ^ (-c * (N : ℝ)) ≤
        8 * (2 : ℝ) ^ (-(c / 2) * (N : ℝ)) := by
  filter_upwards [eventually_shifted_natpow_mul_exponential_le 1 1 hc] with N hpoly
  calc
    currentCoefficient N * (2 : ℝ) ^ (-c * (N : ℝ)) ≤
        (4 * ((N : ℝ) + 1)) * (2 : ℝ) ^ (-c * (N : ℝ)) :=
      mul_le_mul_of_nonneg_right (currentCoefficient_le N) (by positivity)
    _ = 4 * ((((N + 1 : ℕ) : ℝ) ^ 1) *
        (2 : ℝ) ^ (-c * (N : ℝ))) := by push_cast; ring
    _ ≤ 4 * (((2 : ℕ) : ℝ) ^ 1 *
        (2 : ℝ) ^ (-(c / 2) * (N : ℝ))) :=
      mul_le_mul_of_nonneg_left hpoly (by norm_num)
    _ = 8 * (2 : ℝ) ^ (-(c / 2) * (N : ℝ)) := by ring

/-- Cubic growth likewise costs at most half of any prescribed rate. -/
theorem eventually_predecessorCoefficient_mul_exponential_le
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop,
      predecessorCoefficient N * (2 : ℝ) ^ (-c * (N : ℝ)) ≤
        (16 * eulerProduct⁻¹ ^ 2) *
          (2 : ℝ) ^ (-(c / 2) * (N : ℝ)) := by
  filter_upwards [eventually_ge_atTop 1,
    eventually_shifted_natpow_mul_exponential_le 1 3 hc] with N hN hpoly
  calc
    predecessorCoefficient N * (2 : ℝ) ^ (-c * (N : ℝ)) ≤
        (2 * eulerProduct⁻¹ ^ 2 * ((N : ℝ) + 1) ^ 3) *
          (2 : ℝ) ^ (-c * (N : ℝ)) :=
      mul_le_mul_of_nonneg_right (predecessorCoefficient_le N hN) (by positivity)
    _ = (2 * eulerProduct⁻¹ ^ 2) *
        ((((N + 1 : ℕ) : ℝ) ^ 3) *
          (2 : ℝ) ^ (-c * (N : ℝ))) := by push_cast; ring
    _ ≤ (2 * eulerProduct⁻¹ ^ 2) *
        ((((2 : ℕ) : ℝ) ^ 3) *
          (2 : ℝ) ^ (-(c / 2) * (N : ℝ))) :=
      mul_le_mul_of_nonneg_left hpoly (by positivity)
    _ = (16 * eulerProduct⁻¹ ^ 2) *
        (2 : ℝ) ^ (-(c / 2) * (N : ℝ)) := by norm_num; ring

end SymmetricSubgroupAsymptotics.OddMarkerCoefficientBounds

end
