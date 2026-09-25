import SymmetricSubgroupAsymptotics.GaussianAsymptotics
import SymmetricSubgroupAsymptotics.AsymptoticTransfer
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecificLimits.Normed

/-! Quantitative classical contributions to the elementary benchmark. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology
open Filter

namespace SymmetricSubgroupAsymptotics

/-- The Gaussian theta constant selected by the rank parity. -/
def gaussianKappa (r : ℕ) : ℝ := if r % 2 = 0 then kappaEven else kappaOdd

/-- The maximal dimension exponent in the binary Gaussian sum. -/
def gaussianPower (r : ℕ) : ℕ := (r / 2) * (r - r / 2)

theorem gaussianKappa_pos (r : ℕ) : 0 < gaussianKappa r := by
  unfold gaussianKappa
  split_ifs <;> first | exact kappaEven_pos | exact kappaOdd_pos

private theorem log_stirlingSeq_tail (n : ℕ) (hn : 0 < n) (m : ℕ) :
    Real.log (Stirling.stirlingSeq n) - Real.log (Stirling.stirlingSeq (n + m)) ≤
      1 / (12 * (n : ℝ)) := by
  let f (k : ℕ) := Real.log (Stirling.stirlingSeq (n + k))
  let g (k : ℕ) : ℝ := 1 / (12 * (n + k))
  have hstep (k : ℕ) (hk : k ∈ Finset.range m) : f k - f (k + 1) ≤ g k - g (k + 1) := by
    dsimp [f, g]
    have hnk : (0 : ℝ) < n + k := by exact_mod_cast (show 0 < n + k by omega)
    have heq : 1 / (12 * ((n + k : ℕ) : ℝ) * (((n + k : ℕ) : ℝ) + 1)) =
        1 / (12 * ((n : ℝ) + k)) - 1 / (12 * ((n : ℝ) + (k + 1))) := by
      push_cast
      field_simp
      ring
    simpa only [Nat.add_assoc, Nat.cast_add, Nat.cast_one] using
      (Stirling.log_stirlingSeq_diff_le (n + k)).trans_eq heq
  have hsum := Finset.sum_le_sum hstep
  rw [Finset.sum_range_sub', Finset.sum_range_sub'] at hsum
  dsimp [f, g] at hsum
  simp only [Nat.cast_zero, add_zero] at hsum
  have hg : 0 ≤ 1 / (12 * ((n : ℝ) + m)) := by positivity
  linarith

/-- Robbins' logarithmic Stirling remainder, valid at every positive integer. -/
theorem log_factorial_stirling_error (n : ℕ) (hn : 0 < n) :
    |Real.log (Nat.factorial n : ℝ) -
      (((n : ℝ) + 1 / 2) * Real.log n - n + (1 / 2) * Real.log (2 * Real.pi))| ≤
        1 / (12 * (n : ℝ)) := by
  have hlim : Tendsto (fun m : ℕ ↦ Real.log (Stirling.stirlingSeq (n + m)))
      atTop (𝓝 (Real.log (Real.sqrt Real.pi))) := by
    simpa only [Nat.add_comm] using
      (Stirling.tendsto_stirlingSeq_sqrt_pi.log (by positivity)).comp (tendsto_add_atTop_nat n)
  have hupper := le_of_tendsto (tendsto_const_nhds.sub hlim)
    (Eventually.of_forall (log_stirlingSeq_tail n hn))
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hid : Real.log (Stirling.stirlingSeq n) - Real.log (Real.sqrt Real.pi) =
      Real.log (Nat.factorial n : ℝ) -
        (((n : ℝ) + 1 / 2) * Real.log n - n + (1 / 2) * Real.log (2 * Real.pi)) := by
    rw [Stirling.log_stirlingSeq_formula, Real.log_sqrt Real.pi_pos.le,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hn'.ne',
      Real.log_div hn'.ne' (Real.exp_pos 1).ne', Real.log_exp,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero]
    ring
  have hlower := Stirling.le_log_factorial_stirling (n := n) hn.ne'
  rw [hid] at hupper
  rw [abs_of_nonneg (by nlinarith : 0 ≤ Real.log (Nat.factorial n : ℝ) -
    (((n : ℝ) + 1 / 2) * Real.log n - n + (1 / 2) * Real.log (2 * Real.pi)))]
  exact hupper


@[simp] theorem gaussianKappa_even (m : ℕ) : gaussianKappa (2 * m) = kappaEven := by
  simp [gaussianKappa]

@[simp] theorem gaussianKappa_odd (m : ℕ) : gaussianKappa (2 * m + 1) = kappaOdd := by
  simp [gaussianKappa]

@[simp] theorem gaussianPower_even (m : ℕ) : gaussianPower (2 * m) = m ^ 2 := by
  unfold gaussianPower
  rw [show 2 * m / 2 = m by omega, show 2 * m - m = m by omega]
  ring

@[simp] theorem gaussianPower_odd (m : ℕ) : gaussianPower (2 * m + 1) = m * (m + 1) := by
  unfold gaussianPower
  rw [show (2 * m + 1) / 2 = m by omega, show 2 * m + 1 - m = m + 1 by omega]

private theorem gaussian_uniform_relative_error (r : ℕ) (hr : 4 ≤ r) :
    |(binaryGaussianSum r : ℝ) / (gaussianKappa r * (2 : ℝ) ^ gaussianPower r) - 1| ≤
      ((((r + 1 : ℕ) : ℝ) * gaussianErrorConstant + 8 / eulerProduct) *
        (1 / 2 : ℝ) ^ (r / 4)) / gaussianKappa r := by
  let m := r / 2
  have hm : 2 ≤ m := by dsimp [m]; omega
  by_cases he : r % 2 = 0
  · have hr' : r = 2 * m := by dsimp [m]; omega
    rw [hr', gaussianKappa_even, gaussianPower_even]
    have hdiv : 2 * m / 4 = m / 2 := by omega
    rw [hdiv]
    exact binaryGaussianSum_even_relative_error m hm
  · have hr' : r = 2 * m + 1 := by dsimp [m]; omega
    rw [hr', gaussianKappa_odd, gaussianPower_odd]
    have hdiv : (2 * m + 1) / 4 = m / 2 := by omega
    rw [hdiv]
    convert binaryGaussianSum_odd_relative_error m hm using 1

private def gaussianLogBoundConstant : ℝ :=
  (gaussianErrorConstant + 8 / eulerProduct) / min kappaEven kappaOdd

private theorem gaussianLogBoundConstant_pos : 0 < gaussianLogBoundConstant := by
  unfold gaussianLogBoundConstant
  positivity [gaussianErrorConstant_pos, euler_positive, kappaEven_pos, kappaOdd_pos]

private theorem gaussian_uniform_relative_bound (r : ℕ) (hr : 4 ≤ r) :
    |(binaryGaussianSum r : ℝ) / (gaussianKappa r * (2 : ℝ) ^ gaussianPower r) - 1| ≤
      gaussianLogBoundConstant * (r + 1) * (1 / 2 : ℝ) ^ (r / 4) := by
  have hκ : 0 < min kappaEven kappaOdd := lt_min kappaEven_pos kappaOdd_pos
  have hmin : min kappaEven kappaOdd ≤ gaussianKappa r := by
    unfold gaussianKappa
    split_ifs
    · exact min_le_left _ _
    · exact min_le_right _ _
  have hr' : (1 : ℝ) ≤ r + 1 := by have := Nat.cast_nonneg (α := ℝ) r; linarith
  have hb : (0 : ℝ) ≤ 8 / eulerProduct := by positivity [euler_positive]
  have hnum : ((r + 1 : ℕ) : ℝ) * gaussianErrorConstant + 8 / eulerProduct ≤
      (r + 1) * (gaussianErrorConstant + 8 / eulerProduct) := by
    push_cast
    nlinarith
  calc
    _ ≤ _ := gaussian_uniform_relative_error r hr
    _ ≤ ((((r + 1 : ℕ) : ℝ) * gaussianErrorConstant + 8 / eulerProduct) *
        (1 / 2 : ℝ) ^ (r / 4)) / min kappaEven kappaOdd :=
      div_le_div_of_nonneg_left (by positivity [gaussianErrorConstant_pos, euler_positive]) hκ hmin
    _ ≤ (((r + 1) * (gaussianErrorConstant + 8 / eulerProduct)) *
        (1 / 2 : ℝ) ^ (r / 4)) / min kappaEven kappaOdd :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hnum (by positivity)) hκ.le
    _ = _ := by unfold gaussianLogBoundConstant; ring

private theorem gaussian_relative_eventually :
    ∃ N : ℕ, 4 ≤ N ∧ ∀ r ≥ N,
      |(binaryGaussianSum r : ℝ) / (gaussianKappa r * (2 : ℝ) ^ gaussianPower r) - 1| ≤
        1 / (r : ℝ) := by
  let A := gaussianLogBoundConstant
  have hA : 0 < A := gaussianLogBoundConstant_pos
  have hlim : Tendsto (fun j : ℕ ↦ ((j : ℝ) + 1) ^ 2 * (1 / 2 : ℝ) ^ j)
      atTop (𝓝 0) := by
    have h2 := tendsto_pow_const_mul_const_pow_of_lt_one 2
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    have h1 := tendsto_pow_const_mul_const_pow_of_lt_one 1
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    have h0 := tendsto_pow_const_mul_const_pow_of_lt_one 0
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    convert (h2.add (h1.const_mul 2)).add h0 using 1
    · funext j
      ring
    · norm_num
  have hevent : ∀ᶠ j : ℕ in atTop,
      ((j : ℝ) + 1) ^ 2 * (1 / 2 : ℝ) ^ j ≤ 1 / (16 * A) :=
    Filter.Tendsto.eventually_le_const (by positivity) hlim
  obtain ⟨M, hM⟩ := eventually_atTop.mp hevent
  refine ⟨max 4 (4 * M), le_max_left _ _, ?_⟩
  intro r hr
  have hr4 : 4 ≤ r := le_trans (le_max_left _ _) hr
  have hjM : M ≤ r / 4 := by omega
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hrj : (r : ℝ) + 1 ≤ 4 * ((r / 4 : ℕ) + 1 : ℝ) := by
    exact_mod_cast (show r + 1 ≤ 4 * (r / 4 + 1) by omega)
  have hprod : ((r : ℝ) + 1) * r ≤ 16 * (((r / 4 : ℕ) : ℝ) + 1) ^ 2 := by
    nlinarith [sq_nonneg ((r : ℝ) + 1 - 4 * (((r / 4 : ℕ) : ℝ) + 1))]
  have hq : 0 ≤ (1 / 2 : ℝ) ^ (r / 4) := by positivity
  have hsmall := hM (r / 4) hjM
  have hbound : A * ((r : ℝ) + 1) * (1 / 2 : ℝ) ^ (r / 4) * r ≤ 1 := by
    calc
      _ = A * (((r : ℝ) + 1) * r) * (1 / 2 : ℝ) ^ (r / 4) := by ring
      _ ≤ A * (16 * (((r / 4 : ℕ) : ℝ) + 1) ^ 2) * (1 / 2 : ℝ) ^ (r / 4) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod hA.le) hq
      _ = (16 * A) * ((((r / 4 : ℕ) : ℝ) + 1) ^ 2 * (1 / 2 : ℝ) ^ (r / 4)) := by ring
      _ ≤ (16 * A) * (1 / (16 * A)) := mul_le_mul_of_nonneg_left hsmall (by positivity)
      _ = 1 := by field_simp
  exact (gaussian_uniform_relative_bound r hr4).trans ((le_div_iff₀ hrpos).mpr hbound)

private theorem abs_log_le_twice_sub_one {x : ℝ} (hx : (1 / 2 : ℝ) ≤ x) :
    |Real.log x| ≤ 2 * |x - 1| := by
  have hxpos : 0 < x := by linarith
  have hupper := Real.log_le_sub_one_of_pos hxpos
  have hlower := Real.one_sub_inv_le_log_of_pos hxpos
  have hi : x⁻¹ ≤ 2 := by
    rw [← one_div]
    exact (div_le_iff₀ hxpos).mpr (by linarith)
  have hid : 1 - x⁻¹ = (x - 1) * x⁻¹ := by field_simp
  rw [hid] at hlower
  have hneg := mul_le_mul_of_nonneg_right (neg_abs_le (x - 1)) (inv_nonneg.mpr hxpos.le)
  have hm := mul_le_mul_of_nonneg_left hi (abs_nonneg (x - 1))
  exact abs_le.mpr ⟨by nlinarith, by linarith [le_abs_self (x - 1), abs_nonneg (x - 1)]⟩

/-- A uniform logarithmic Gaussian error; the exponential bound gives even O(1/r). -/
theorem binaryGaussianSum_log_error : ∃ N : ℕ, 2 ≤ N ∧ ∀ r ≥ N,
    |Real.log (binaryGaussianSum r : ℝ) - (gaussianPower r : ℝ) * Real.log 2 -
      Real.log (gaussianKappa r)| ≤ 2 / (r : ℝ) := by
  obtain ⟨N, hN, hbound⟩ := gaussian_relative_eventually
  refine ⟨N, by omega, ?_⟩
  intro r hr
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hsmall : 1 / (r : ℝ) ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
    exact_mod_cast (show 2 ≤ r by omega)
  let x := (binaryGaussianSum r : ℝ) / (gaussianKappa r * (2 : ℝ) ^ gaussianPower r)
  have hx : (1 / 2 : ℝ) ≤ x := by
    have h := (abs_le.mp (hbound r hr)).1
    dsimp [x]
    linarith
  have hlog := (abs_log_le_twice_sub_one hx).trans
    (mul_le_mul_of_nonneg_left (hbound r hr) (by norm_num : (0 : ℝ) ≤ 2))
  have hG : (0 : ℝ) < binaryGaussianSum r := by exact_mod_cast binaryGaussianSum_pos r
  have hκ := gaussianKappa_pos r
  have hid : Real.log x = Real.log (binaryGaussianSum r : ℝ) -
      (gaussianPower r : ℝ) * Real.log 2 - Real.log (gaussianKappa r) := by
    dsimp [x]
    rw [Real.log_div hG.ne' (by positivity), Real.log_mul hκ.ne' (by positivity), Real.log_pow]
    ring
  rw [hid] at hlog
  simpa only [mul_one_div] using hlog

end SymmetricSubgroupAsymptotics
