import SymmetricSubgroupAsymptotics.GaussianEstimates

/-!
# Exponential Gaussian-sum asymptotics

Both residue-dependent theta constants arise from centering the subspace
dimension. The estimates retain an explicit error, uniform in the parity.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace SymmetricSubgroupAsymptotics

private def gaussianTheta (e : ℕ) (j : ℤ) : ℝ :=
  (2 : ℝ) ^ (-((j : ℝ) * ((j : ℝ) - e)))

private theorem gaussianTheta_zero (j : ℤ) : gaussianTheta 0 j = thetaEvenTerm j := by
  unfold gaussianTheta thetaEvenTerm
  congr 1
  ring

private theorem gaussianTheta_one (j : ℤ) : gaussianTheta 1 j = thetaOddTerm j := by
  simp [gaussianTheta, thetaOddTerm]

private theorem gaussianTheta_summable (e : ℕ) (he : e ≤ 1) : Summable (gaussianTheta e) := by
  interval_cases e
  · rw [show gaussianTheta 0 = thetaEvenTerm from funext gaussianTheta_zero]
    exact theta_even_summable
  · rw [show gaussianTheta 1 = thetaOddTerm from funext gaussianTheta_one]
    exact theta_odd_summable

private theorem gaussianTheta_pos (e : ℕ) (j : ℤ) : 0 < gaussianTheta e j := by
  exact Real.rpow_pos_of_pos (by norm_num) _

private theorem gaussianTheta_le_one (e : ℕ) (he : e ≤ 1) (j : ℤ) :
    gaussianTheta e j ≤ 1 := by
  have hz : (0 : ℤ) ≤ j * (j - e) := by
    have he0 : (0 : ℤ) ≤ e := by positivity
    have he1 : (e : ℤ) ≤ 1 := by exact_mod_cast he
    by_cases hj : j ≤ 0
    · exact mul_nonneg_of_nonpos_of_nonpos hj (by omega)
    · have hj1 : (1 : ℤ) ≤ j := by omega
      exact mul_nonneg (by omega) (by omega)
  have hr : (0 : ℝ) ≤ (j : ℝ) * ((j : ℝ) - e) := by exact_mod_cast hz
  unfold gaussianTheta
  calc
    _ ≤ (2 : ℝ) ^ (0 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = 1 := by norm_num

private theorem two_rpow_one_sub (n : ℕ) :
    (2 : ℝ) ^ (1 - (n : ℝ)) = 2 * (1 / 2 : ℝ) ^ n := by
  rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_one,
    Real.rpow_natCast]
  simp [div_eq_mul_inv, inv_pow]

private theorem gaussianTheta_nat_bound (e : ℕ) (he : e ≤ 1) (n : ℕ) :
    gaussianTheta e n ≤ 2 * (1 / 2 : ℝ) ^ n := by
  rw [← two_rpow_one_sub]
  unfold gaussianTheta
  push_cast
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
  have he' : (e : ℝ) ≤ 1 := by exact_mod_cast he
  have hn : (0 : ℝ) ≤ n := by positivity
  nlinarith [sq_nonneg ((n : ℝ) - 1), mul_nonneg hn (sub_nonneg.mpr he')]

private theorem gaussianTheta_neg_bound (e : ℕ) (n : ℕ) :
    gaussianTheta e (-((n : ℤ) + 1)) ≤ 2 * (1 / 2 : ℝ) ^ n := by
  rw [← two_rpow_one_sub]
  unfold gaussianTheta
  push_cast
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
  have he : (0 : ℝ) ≤ e := by positivity
  have hn : (0 : ℝ) ≤ n := by positivity
  nlinarith [sq_nonneg (n : ℝ), mul_nonneg hn he]

private theorem geometric_tail_bound (f : ℕ → ℝ)
    (hf0 : ∀ n, 0 ≤ f n) (hfb : ∀ n, f n ≤ 2 * (1 / 2 : ℝ) ^ n) (m : ℕ) :
    Summable (fun n ↦ f (n + m)) ∧
      ∑' n, f (n + m) ≤ 4 * (1 / 2 : ℝ) ^ m := by
  have hg : Summable (fun n : ℕ ↦ (2 * (1 / 2 : ℝ) ^ m) * (1 / 2 : ℝ) ^ n) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hle (n : ℕ) : f (n + m) ≤ (2 * (1 / 2 : ℝ) ^ m) * (1 / 2 : ℝ) ^ n := by
    simpa only [pow_add, mul_assoc, mul_comm, mul_left_comm] using hfb (n + m)
  have hs := hg.of_nonneg_of_le (fun n ↦ hf0 (n + m)) hle
  refine ⟨hs, ?_⟩
  have hsum := hs.tsum_le_tsum hle hg
  rw [tsum_mul_left, tsum_geometric_two] at hsum
  nlinarith

private theorem gaussianTheta_finite_split (m e : ℕ) :
    ∑ k ∈ Finset.range (2 * m + e + 1), gaussianTheta e ((k : ℤ) - m) =
      (∑ n ∈ Finset.range m, gaussianTheta e (-((n : ℤ) + 1))) +
        ∑ n ∈ Finset.range (m + e + 1), gaussianTheta e n := by
  rw [show 2 * m + e + 1 = m + (m + e + 1) by omega, Finset.sum_range_add]
  congr 1
  · rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro n hn
    have hn' := Finset.mem_range.mp hn
    congr 1
    omega
  · apply Finset.sum_congr rfl
    intro n hn
    congr 1
    omega

/-- Truncating the centered theta sum loses at most a geometric tail. -/
private theorem gaussianTheta_truncation (m e : ℕ) (he : e ≤ 1) :
    0 ≤ (∑' j : ℤ, gaussianTheta e j) -
        ∑ k ∈ Finset.range (2 * m + e + 1), gaussianTheta e ((k : ℤ) - m) ∧
      (∑' j : ℤ, gaussianTheta e j) -
        ∑ k ∈ Finset.range (2 * m + e + 1), gaussianTheta e ((k : ℤ) - m) ≤
          8 * (1 / 2 : ℝ) ^ m := by
  have hp := geometric_tail_bound (fun n ↦ gaussianTheta e n)
    (fun n ↦ (gaussianTheta_pos e n).le) (gaussianTheta_nat_bound e he) (m + e + 1)
  have hn := geometric_tail_bound (fun n ↦ gaussianTheta e (-((n : ℤ) + 1)))
    (fun n ↦ (gaussianTheta_pos e _).le) (gaussianTheta_neg_bound e) m
  have hsP : Summable (fun n : ℕ ↦ gaussianTheta e n) :=
    (gaussianTheta_summable e he).comp_injective Nat.cast_injective
  have hsN : Summable (fun n : ℕ ↦ gaussianTheta e (-((n : ℤ) + 1))) :=
    (gaussianTheta_summable e he).comp_injective (by
      intro a b h
      have h' : (a : ℤ) = b := by linarith
      exact_mod_cast h')
  rw [tsum_of_nat_of_neg_add_one hsP hsN, gaussianTheta_finite_split]
  have hP := hsP.sum_add_tsum_nat_add (m + e + 1)
  have hN := hsN.sum_add_tsum_nat_add m
  have hP0 : 0 ≤ ∑' n : ℕ, gaussianTheta e (((n + (m + e + 1) : ℕ) : ℤ)) :=
    tsum_nonneg (fun _ ↦ (gaussianTheta_pos e _).le)
  have hN0 : 0 ≤ ∑' n : ℕ, gaussianTheta e (-(((n + m : ℕ) : ℤ) + 1)) :=
    tsum_nonneg (fun _ ↦ (gaussianTheta_pos e _).le)
  have hg : (1 / 2 : ℝ) ^ (m + e + 1) ≤ (1 / 2 : ℝ) ^ m :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  constructor <;> linarith [hp.2, hn.2]

private theorem gaussianTheta_center_identity (m e k : ℕ) (hk : k ≤ 2 * m + e) :
    (2 : ℝ) ^ (k * (2 * m + e - k)) / (2 : ℝ) ^ (m * (m + e)) =
      gaussianTheta e ((k : ℤ) - m) := by
  rw [← Real.rpow_natCast (2 : ℝ) (k * (2 * m + e - k)),
    ← Real.rpow_natCast (2 : ℝ) (m * (m + e)),
    ← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
  unfold gaussianTheta
  congr 1
  rw [Nat.cast_mul, Nat.cast_sub hk]
  push_cast
  ring

private theorem half_pow_as_rpow (n : ℕ) :
    (1 / 2 : ℝ) ^ n = (2 : ℝ) ^ (-(n : ℝ)) := by
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
  simp [one_div, inv_pow]

private theorem gaussianTheta_edge (m e k : ℕ) (hm : 2 ≤ m) (he : e ≤ 1)
    (hk : k ≤ 2 * m + e) (hedge : k < m / 2 ∨ 2 * m + e - k < m / 2) :
    gaussianTheta e ((k : ℤ) - m) ≤ (1 / 2 : ℝ) ^ (m / 2) := by
  rw [half_pow_as_rpow]
  unfold gaussianTheta
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
  push_cast
  have hL : 1 ≤ m / 2 := by omega
  have hL' : (1 : ℝ) ≤ (m / 2 : ℕ) := by exact_mod_cast hL
  have he0 : (0 : ℝ) ≤ e := by positivity
  rcases hedge with hlow | hhigh
  · have hsum : k + m / 2 ≤ m := by omega
    have hsum' : (k : ℝ) + (m / 2 : ℕ) ≤ m := by exact_mod_cast hsum
    have hx : 0 ≤ (m : ℝ) - k := by linarith
    have hx1 : 0 ≤ (m : ℝ) - k - 1 := by linarith
    nlinarith [mul_nonneg hx1 hx, mul_nonneg hx he0]
  · have hsum : m + e + m / 2 ≤ k := by omega
    have hsum' : (m : ℝ) + e + (m / 2 : ℕ) ≤ k := by exact_mod_cast hsum
    have hx : 0 ≤ (k : ℝ) - m - e := by linarith
    have hx1 : 0 ≤ (k : ℝ) - m - e - 1 := by linarith
    nlinarith [mul_nonneg hx1 hx, mul_nonneg hx he0]

/-- A fixed positive coefficient in the explicit Gaussian-sum error. -/
def gaussianErrorConstant : ℝ := 2 / eulerProduct ^ 3 + 1 / eulerProduct

theorem gaussianErrorConstant_pos : 0 < gaussianErrorConstant := by
  unfold gaussianErrorConstant
  positivity [euler_positive]

private theorem gaussian_centered_term_error (m e k : ℕ) (hm : 2 ≤ m)
    (he : e ≤ 1) (hk : k ≤ 2 * m + e) :
    0 ≤ gaussianTheta e ((k : ℤ) - m) / eulerProduct -
        (binaryGaussianCoefficient (2 * m + e) k : ℝ) / (2 : ℝ) ^ (m * (m + e)) ∧
      gaussianTheta e ((k : ℤ) - m) / eulerProduct -
        (binaryGaussianCoefficient (2 * m + e) k : ℝ) / (2 : ℝ) ^ (m * (m + e)) ≤
          gaussianErrorConstant * (1 / 2 : ℝ) ^ (m / 2) := by
  let w := gaussianTheta e ((k : ℤ) - m)
  let d := eulerProduct⁻¹ - (binaryGaussianCoefficient (2 * m + e) k : ℝ) /
    (2 : ℝ) ^ (k * (2 * m + e - k))
  have hd := binaryGaussianCoefficient_normalized_error (2 * m + e) k hk
  have hw := (gaussianTheta_pos e ((k : ℤ) - m)).le
  have hw1 := gaussianTheta_le_one e he ((k : ℤ) - m)
  have hφ := euler_positive
  have hq : 0 ≤ (1 / 2 : ℝ) ^ (m / 2) := by positivity
  have hid : gaussianTheta e ((k : ℤ) - m) / eulerProduct -
      (binaryGaussianCoefficient (2 * m + e) k : ℝ) / (2 : ℝ) ^ (m * (m + e)) = w * d := by
    dsimp [w, d]
    rw [← gaussianTheta_center_identity m e k hk]
    have hpow : (2 : ℝ) ^ (k * (2 * m + e - k)) ≠ 0 := by positivity
    field_simp
  rw [hid]
  constructor
  · exact mul_nonneg hw hd.1
  · by_cases hc : m / 2 ≤ k ∧ m / 2 ≤ 2 * m + e - k
    · have hqk : (1 / 2 : ℝ) ^ k ≤ (1 / 2 : ℝ) ^ (m / 2) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hc.1
      have hqr : (1 / 2 : ℝ) ^ (2 * m + e - k) ≤ (1 / 2 : ℝ) ^ (m / 2) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hc.2
      have hd' : d ≤ (2 / eulerProduct ^ 3) * (1 / 2 : ℝ) ^ (m / 2) := by
        have hsum := div_le_div_of_nonneg_right (add_le_add hqk hqr)
          (show 0 ≤ eulerProduct ^ 3 by positivity)
        dsimp [d]
        calc
          _ ≤ _ := hd.2
          _ ≤ _ := hsum
          _ = _ := by ring
      have hwd : w * d ≤ d := mul_le_of_le_one_left hd.1 hw1
      have hextra : 0 ≤ (1 / eulerProduct) * (1 / 2 : ℝ) ^ (m / 2) := by positivity
      unfold gaussianErrorConstant
      nlinarith
    · have hedge : k < m / 2 ∨ 2 * m + e - k < m / 2 := by omega
      have hwedge := gaussianTheta_edge m e k hm he hk hedge
      have hcoef : (0 : ℝ) ≤ binaryGaussianCoefficient (2 * m + e) k := by
        exact_mod_cast (binaryGaussianCoefficient_pos hk).le
      have hd' : d ≤ eulerProduct⁻¹ := by
        dsimp [d]
        exact sub_le_self _ (div_nonneg hcoef (by positivity))
      have hwd := mul_le_mul hwedge hd' hd.1 hq
      have hextra : 0 ≤ (2 / eulerProduct ^ 3) * (1 / 2 : ℝ) ^ (m / 2) := by positivity
      unfold gaussianErrorConstant
      dsimp [w] at *
      rw [← one_div eulerProduct] at hwd
      nlinarith

private theorem gaussian_sum_error (m e : ℕ) (hm : 2 ≤ m) (he : e ≤ 1) :
    0 ≤ (∑' j : ℤ, gaussianTheta e j) / eulerProduct -
        (binaryGaussianSum (2 * m + e) : ℝ) / (2 : ℝ) ^ (m * (m + e)) ∧
      (∑' j : ℤ, gaussianTheta e j) / eulerProduct -
        (binaryGaussianSum (2 * m + e) : ℝ) / (2 : ℝ) ^ (m * (m + e)) ≤
          (((2 * m + e + 1 : ℕ) : ℝ) * gaussianErrorConstant + 8 / eulerProduct) *
            (1 / 2 : ℝ) ^ (m / 2) := by
  have hφ := euler_positive
  have hfinite : (binaryGaussianSum (2 * m + e) : ℝ) =
      ∑ k ∈ Finset.range (2 * m + e + 1), (binaryGaussianCoefficient (2 * m + e) k : ℝ) := by
    unfold binaryGaussianSum
    push_cast
    rfl
  have hlow := Finset.sum_nonneg (s := Finset.range (2 * m + e + 1))
    (fun k hk ↦ (gaussian_centered_term_error m e k hm he
      (Nat.le_of_lt_succ (Finset.mem_range.mp hk))).1)
  have hupp := Finset.sum_le_sum (s := Finset.range (2 * m + e + 1))
    (fun k hk ↦ (gaussian_centered_term_error m e k hm he
      (Nat.le_of_lt_succ (Finset.mem_range.mp hk))).2)
  simp only [Finset.sum_sub_distrib, ← Finset.sum_div, ← hfinite,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hlow hupp
  have ht := gaussianTheta_truncation m e he
  have htl := div_nonneg ht.1 hφ.le
  have htu := div_le_div_of_nonneg_right ht.2 hφ.le
  rw [sub_div] at htl htu
  have hg : (1 / 2 : ℝ) ^ m ≤ (1 / 2 : ℝ) ^ (m / 2) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.div_le_self m 2)
  have htail := mul_le_mul_of_nonneg_left hg (show 0 ≤ 8 / eulerProduct by positivity)
  constructor
  · linarith
  · have htu' : (∑' j : ℤ, gaussianTheta e j) / eulerProduct -
        (∑ k ∈ Finset.range (2 * m + e + 1), gaussianTheta e ((k : ℤ) - m)) /
          eulerProduct ≤ (8 / eulerProduct) * (1 / 2 : ℝ) ^ (m / 2) := by
      calc
        _ ≤ 8 * (1 / 2 : ℝ) ^ m / eulerProduct := htu
        _ = (8 / eulerProduct) * (1 / 2 : ℝ) ^ m := by ring
        _ ≤ _ := htail
    calc
      _ = ((∑' j : ℤ, gaussianTheta e j) / eulerProduct -
          (∑ k ∈ Finset.range (2 * m + e + 1), gaussianTheta e ((k : ℤ) - m)) /
            eulerProduct) +
          ((∑ k ∈ Finset.range (2 * m + e + 1), gaussianTheta e ((k : ℤ) - m)) /
            eulerProduct - (binaryGaussianSum (2 * m + e) : ℝ) /
              (2 : ℝ) ^ (m * (m + e))) := by ring
      _ ≤ _ := add_le_add htu' hupp
      _ = _ := by ring

/-- Even ranks: the normalized explicit Gaussian sum approaches `κ₀` with
an explicit exponential error. The bound is `O(m·2^{-m/2})`. -/
theorem binaryGaussianSum_even_error (m : ℕ) (hm : 2 ≤ m) :
    |(binaryGaussianSum (2 * m) : ℝ) / (2 : ℝ) ^ (m ^ 2) - kappaEven| ≤
      (((2 * m + 1 : ℕ) : ℝ) * gaussianErrorConstant + 8 / eulerProduct) *
        (1 / 2 : ℝ) ^ (m / 2) := by
  have h := gaussian_sum_error m 0 hm (by omega)
  have hκ : (∑' j : ℤ, gaussianTheta 0 j) / eulerProduct = kappaEven := by
    simp only [gaussianTheta_zero, kappaEven]
    ring
  rw [hκ] at h
  simp only [Nat.add_zero, ← pow_two] at h
  rw [abs_sub_comm, abs_of_nonneg h.1]
  exact h.2

/-- Odd ranks: the normalized explicit Gaussian sum approaches `κ₁` with
an explicit exponential error, uniform with the even-rank estimate. -/
theorem binaryGaussianSum_odd_error (m : ℕ) (hm : 2 ≤ m) :
    |(binaryGaussianSum (2 * m + 1) : ℝ) / (2 : ℝ) ^ (m * (m + 1)) - kappaOdd| ≤
      (((2 * m + 2 : ℕ) : ℝ) * gaussianErrorConstant + 8 / eulerProduct) *
        (1 / 2 : ℝ) ^ (m / 2) := by
  have h := gaussian_sum_error m 1 hm (by omega)
  have hκ : (∑' j : ℤ, gaussianTheta 1 j) / eulerProduct = kappaOdd := by
    simp only [gaussianTheta_one, kappaOdd]
    ring
  rw [hκ] at h
  rw [abs_sub_comm, abs_of_nonneg h.1]
  exact h.2

/-- Relative-error version of the even-rank Gaussian asymptotic. -/
theorem binaryGaussianSum_even_relative_error (m : ℕ) (hm : 2 ≤ m) :
    |(binaryGaussianSum (2 * m) : ℝ) / (kappaEven * (2 : ℝ) ^ (m ^ 2)) - 1| ≤
      ((((2 * m + 1 : ℕ) : ℝ) * gaussianErrorConstant + 8 / eulerProduct) *
        (1 / 2 : ℝ) ^ (m / 2)) / kappaEven := by
  have hk := kappaEven_pos
  have hid : (binaryGaussianSum (2 * m) : ℝ) /
      (kappaEven * (2 : ℝ) ^ (m ^ 2)) - 1 =
        ((binaryGaussianSum (2 * m) : ℝ) / (2 : ℝ) ^ (m ^ 2) - kappaEven) /
          kappaEven := by field_simp
  rw [hid, abs_div, abs_of_pos hk]
  exact div_le_div_of_nonneg_right (binaryGaussianSum_even_error m hm) hk.le

/-- Relative-error version of the odd-rank Gaussian asymptotic. -/
theorem binaryGaussianSum_odd_relative_error (m : ℕ) (hm : 2 ≤ m) :
    |(binaryGaussianSum (2 * m + 1) : ℝ) /
        (kappaOdd * (2 : ℝ) ^ (m * (m + 1))) - 1| ≤
      ((((2 * m + 2 : ℕ) : ℝ) * gaussianErrorConstant + 8 / eulerProduct) *
        (1 / 2 : ℝ) ^ (m / 2)) / kappaOdd := by
  have hk := kappaOdd_pos
  have hid : (binaryGaussianSum (2 * m + 1) : ℝ) /
      (kappaOdd * (2 : ℝ) ^ (m * (m + 1))) - 1 =
        ((binaryGaussianSum (2 * m + 1) : ℝ) / (2 : ℝ) ^ (m * (m + 1)) - kappaOdd) /
          kappaOdd := by field_simp
  rw [hid, abs_div, abs_of_pos hk]
  exact div_le_div_of_nonneg_right (binaryGaussianSum_odd_error m hm) hk.le

end SymmetricSubgroupAsymptotics
