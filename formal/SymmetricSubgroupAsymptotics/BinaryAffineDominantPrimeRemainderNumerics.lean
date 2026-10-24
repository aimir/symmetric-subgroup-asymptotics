import SymmetricSubgroupAsymptotics.BinaryAffineDominantPrimeSwitchNumerics
import Mathlib.Data.Nat.Choose.Sum

/-! Explicit errors for the dominant-prime endpoint argument. These
bounds include the top ratio and leave its natural ceiling error as an
actual other-endpoint coefficient; no error is silently dropped. The
quadratic margin includes dimension one. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.BinaryAffineDominantPrimeRemainderNumerics

theorem other_endpoint_le (M : ℕ) (hM : 2^40 ≤ M) (d B x : ℝ)
    (hd0 : 0 ≤ d) (hd6 : d ≤ 6) (hB0 : 0 ≤ B) (hB37 : B ≤ 37)
    (hx0 : 0 ≤ x) (hxM : x ≤ M) :
    (B/(M : ℝ))*Real.sqrt (d+Real.logb 2 (M : ℝ)+8*x) ≤ 1/1024 := by
  have hMR : (1099511627776 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hlog := BinaryAffineDominantPrimeSwitchNumerics.logb_nat_le_sub_one M (by omega)
  have hlog0 : 0 ≤ Real.logb 2 (M : ℝ) :=
    (Real.logb_pos (by norm_num : (1 : ℝ) < 2) (by linarith : (1 : ℝ) < M)).le
  have hrad0 : 0 ≤ d+Real.logb 2 (M : ℝ)+8*x := by positivity
  have hrad : d+Real.logb 2 (M : ℝ)+8*x ≤ 10*(M : ℝ) := by linarith
  have hBsq : B^2 ≤ (37 : ℝ)^2 :=
    (sq_le_sq₀ hB0 (by norm_num : (0 : ℝ) ≤ 37)).mpr hB37
  have hprod := mul_le_mul hBsq hrad hrad0 (by norm_num : (0 : ℝ) ≤ 37^2)
  have hquad := mul_le_mul_of_nonneg_right hMR hM0.le
  apply (sq_le_sq₀ (mul_nonneg (div_nonneg hB0 hM0.le) (Real.sqrt_nonneg _))
    (by norm_num : (0 : ℝ) ≤ 1/1024)).mp
  rw [mul_pow,Real.sq_sqrt hrad0,div_pow,div_mul_eq_mul_div]
  apply (div_le_iff₀ (pow_pos hM0 2)).mpr
  nlinarith only [hprod,hquad,hM0.le]

theorem top_ratio_le (d L : ℝ) (hd : 0 ≤ d) (hL : 512 ≤ L) :
    Real.sqrt (1+d/L) ≤ 1+d/1024 := by
  have hfrac := div_le_div_of_nonneg_left hd (by norm_num : (0 : ℝ) < 512) hL
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity,?_⟩
  nlinarith [sq_nonneg d]

theorem triangular_succ_le_two_pow (d : ℕ) : d+d*(d-1)/2+1 ≤ 2^d := by
  by_cases hd : 2 ≤ d
  · have hsub : Finset.range 3 ⊆ Finset.range (d+1) := Finset.range_mono (by omega)
    have hh := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun i (_ : i ∈ Finset.range (d+1)) (_ : i ∉ Finset.range 3) =>
        Nat.zero_le (d.choose i))
    rw [Nat.sum_range_choose] at hh
    norm_num [Finset.sum_range_succ,Nat.choose_two_right] at hh
    omega
  · have hsmall : d = 0 ∨ d = 1 := by omega
    rcases hsmall with rfl | rfl <;> norm_num

theorem quadratic_margin (d : ℕ) (hd : 1 ≤ d) :
    (99/100 : ℝ)*((d+d*(d-1)/2 : ℕ) : ℝ) + 1 + ((d : ℝ)+1)/1024 ≤ (2 : ℝ)^d := by
  have hA : (d : ℝ) ≤ ((d+d*(d-1)/2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_add_right d (d*(d-1)/2)
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have htail : (99/100 : ℝ)*((d+d*(d-1)/2 : ℕ) : ℝ) + 1 + ((d : ℝ)+1)/1024 ≤
      ((d+d*(d-1)/2 : ℕ) : ℝ)+1 := by nlinarith only [hA,hdR]
  have hpow : ((d+d*(d-1)/2 : ℕ) : ℝ)+1 ≤ (2 : ℝ)^d := by
    exact_mod_cast triangular_succ_le_two_pow d
  exact htail.trans hpow

end SymmetricSubgroupAsymptotics.BinaryAffineDominantPrimeRemainderNumerics
