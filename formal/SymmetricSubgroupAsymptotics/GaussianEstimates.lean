import SymmetricSubgroupAsymptotics.GaussianCount
import SymmetricSubgroupAsymptotics.Constants

/-!
# Quantitative Euler-product and Gaussian-coefficient estimates

The estimates in this file have explicit errors. Finite Euler products
approximate the positive infinite product within a geometric tail; the same
bounds control Gaussian coefficients uniformly in their two dimensions.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Filter Topology

namespace SymmetricSubgroupAsymptotics

/-- The first `m` factors of the binary Euler product. -/
def eulerPartialProduct (m : ℕ) : ℝ := ∏ i ∈ Finset.range m, eulerFactor i

theorem eulerFactor_eq_half_pow (i : ℕ) :
    eulerFactor i = 1 - (1 / 2 : ℝ) ^ (i + 1) := by
  unfold eulerFactor
  rw [show -((i : ℝ) + 1) = -((i + 1 : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
  simp [one_div, inv_pow]

theorem eulerFactor_le_one (i : ℕ) : eulerFactor i ≤ 1 := by
  rw [eulerFactor_eq_half_pow]
  exact sub_le_self _ (by positivity)

@[simp] theorem eulerPartialProduct_zero : eulerPartialProduct 0 = 1 := by
  simp [eulerPartialProduct]

@[simp] theorem eulerPartialProduct_succ (m : ℕ) :
    eulerPartialProduct (m + 1) = eulerPartialProduct m * eulerFactor m := by
  simp [eulerPartialProduct, Finset.prod_range_succ]

theorem eulerPartialProduct_pos (m : ℕ) : 0 < eulerPartialProduct m := by
  exact Finset.prod_pos (fun i _ ↦ eulerFactor_pos i)

theorem eulerPartialProduct_le_one (m : ℕ) : eulerPartialProduct m ≤ 1 := by
  exact Finset.prod_le_one (fun i _ ↦ (eulerFactor_pos i).le)
    (fun i _ ↦ eulerFactor_le_one i)

theorem eulerPartialProduct_antitone : Antitone eulerPartialProduct := by
  apply antitone_nat_of_succ_le
  intro m
  rw [eulerPartialProduct_succ]
  exact mul_le_of_le_one_right (eulerPartialProduct_pos m).le (eulerFactor_le_one m)

/-- A finite geometric bound for the loss from appending Euler factors. -/
theorem eulerPartialProduct_tail_bound (m d : ℕ) :
    eulerPartialProduct m - eulerPartialProduct (m + d) ≤
      (1 / 2 : ℝ) ^ m * (1 - (1 / 2 : ℝ) ^ d) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Nat.add_succ, eulerPartialProduct_succ, eulerFactor_eq_half_pow]
    have hp := eulerPartialProduct_le_one (m + d)
    have hg : 0 ≤ (1 / 2 : ℝ) ^ (m + d + 1) := by positivity
    have hmul := mul_le_mul_of_nonneg_right hp hg
    simp only [pow_add, pow_one, one_mul] at hmul ⊢
    nlinarith

theorem eulerPartialProduct_tendsto :
    Tendsto eulerPartialProduct atTop (𝓝 eulerProduct) :=
  euler_multipliable.hasProd.tendsto_prod_nat

theorem eulerProduct_le_partial (m : ℕ) : eulerProduct ≤ eulerPartialProduct m := by
  apply le_of_tendsto' (eulerPartialProduct_tendsto.comp (tendsto_add_atTop_nat m))
  intro d
  exact eulerPartialProduct_antitone (Nat.le_add_left m d)

/-- The finite Euler product has an explicit exponentially small absolute error. -/
theorem eulerPartialProduct_sub_bound (m : ℕ) :
    0 ≤ eulerPartialProduct m - eulerProduct ∧
      eulerPartialProduct m - eulerProduct ≤ (1 / 2 : ℝ) ^ m := by
  constructor
  · exact sub_nonneg.mpr (eulerProduct_le_partial m)
  · have ht : Tendsto (fun d ↦ eulerPartialProduct m - eulerPartialProduct (d + m))
        atTop (𝓝 (eulerPartialProduct m - eulerProduct)) :=
      tendsto_const_nhds.sub
        (eulerPartialProduct_tendsto.comp (tendsto_add_atTop_nat m))
    apply le_of_tendsto' ht
    intro d
    have h := eulerPartialProduct_tail_bound m d
    have hp : 0 ≤ (1 / 2 : ℝ) ^ m * (1 / 2 : ℝ) ^ d := by positivity
    rw [Nat.add_comm d m]
    nlinarith

/-- Reciprocal Euler products converge at the same geometric rate. -/
theorem eulerPartialProduct_inv_bound (m : ℕ) :
    0 ≤ eulerProduct⁻¹ - (eulerPartialProduct m)⁻¹ ∧
      eulerProduct⁻¹ - (eulerPartialProduct m)⁻¹ ≤
        (1 / 2 : ℝ) ^ m / eulerProduct ^ 2 := by
  have he := euler_positive
  have hp := eulerPartialProduct_pos m
  have hb := eulerPartialProduct_sub_bound m
  have heP := eulerProduct_le_partial m
  constructor
  · exact sub_nonneg.mpr (by simpa only [one_div] using one_div_le_one_div_of_le he heP)
  · have hd : eulerProduct ^ 2 ≤ eulerProduct * eulerPartialProduct m := by
      nlinarith
    calc
      eulerProduct⁻¹ - (eulerPartialProduct m)⁻¹ =
          (eulerPartialProduct m - eulerProduct) /
            (eulerProduct * eulerPartialProduct m) := by field_simp
      _ ≤ (1 / 2 : ℝ) ^ m / (eulerProduct * eulerPartialProduct m) := by
        exact div_le_div_of_nonneg_right hb.2 (by positivity)
      _ ≤ (1 / 2 : ℝ) ^ m / eulerProduct ^ 2 := by
        exact div_le_div_of_nonneg_left (by positivity) (by positivity) hd

theorem eulerFactor_eq_inv_pow (i : ℕ) :
    eulerFactor i = 1 - ((2 : ℝ) ^ (i + 1))⁻¹ := by
  rw [eulerFactor_eq_half_pow]
  simp [one_div, inv_pow]

private theorem gaussian_factor_reflected (a d i : ℕ) :
    ((2 : ℝ) ^ (a + d + i + 1) - 2 ^ a) / (2 ^ (a + i + 1) - 2 ^ a) =
      2 ^ d * eulerFactor (d + i) / eulerFactor i := by
  rw [eulerFactor_eq_inv_pow, eulerFactor_eq_inv_pow]
  have hp : (0 : ℝ) < 2 ^ i := by positivity
  have hpi : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
  have ha : (2 : ℝ) ^ a ≠ 0 := by positivity
  have hd : (2 : ℝ) ^ d ≠ 0 := by positivity
  have hi : (2 : ℝ) ^ i ≠ 0 := by positivity
  have hni : (2 : ℝ) ^ i * 2 - 1 ≠ 0 := by nlinarith
  simp only [pow_add, pow_one]
  field_simp

/-- Exact finite Euler-product form of a Gaussian coefficient. -/
theorem binaryGaussianCoefficient_euler (r k : ℕ) (hk : k ≤ r) :
    (binaryGaussianCoefficient r k : ℝ) =
      (2 : ℝ) ^ (k * (r - k)) *
        eulerPartialProduct r /
          (eulerPartialProduct k * eulerPartialProduct (r - k)) := by
  have hprod : (binaryGaussianCoefficient r k : ℝ) =
      (2 : ℝ) ^ (k * (r - k)) *
        (∏ i ∈ Finset.range k, eulerFactor (r - k + i)) / eulerPartialProduct k := by
    unfold binaryGaussianCoefficient
    push_cast
    rw [← Finset.prod_range_reflect]
    calc
      _ = ∏ i ∈ Finset.range k,
          ((2 : ℝ) ^ (r - k) * eulerFactor (r - k + i) / eulerFactor i) := by
        apply Finset.prod_congr rfl
        intro i hi
        have hi' := Finset.mem_range.mp hi
        have hr : k - 1 - i + (r - k) + i + 1 = r := by omega
        have hk' : k - 1 - i + i + 1 = k := by omega
        simpa only [hr, hk'] using gaussian_factor_reflected (k - 1 - i) (r - k) i
      _ = _ := by
        rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_const,
          Finset.card_range]
        simp only [eulerPartialProduct, ← pow_mul, Nat.mul_comm]
  have hs : eulerPartialProduct r = eulerPartialProduct (r - k) *
      ∏ i ∈ Finset.range k, eulerFactor (r - k + i) := by
    unfold eulerPartialProduct
    conv_lhs => rw [← Nat.sub_add_cancel hk]
    exact Finset.prod_range_add eulerFactor (r - k) k
  rw [hprod, hs]
  have hp := ne_of_gt (eulerPartialProduct_pos (r - k))
  field_simp

/-- Normalizing by the quadratic power leaves a quotient of Euler products. -/
theorem binaryGaussianCoefficient_normalized (r k : ℕ) (hk : k ≤ r) :
    (binaryGaussianCoefficient r k : ℝ) / (2 : ℝ) ^ (k * (r - k)) =
      eulerPartialProduct r /
        (eulerPartialProduct k * eulerPartialProduct (r - k)) := by
  rw [binaryGaussianCoefficient_euler r k hk]
  have h2 : (2 : ℝ) ^ (k * (r - k)) ≠ 0 := by positivity
  field_simp

/-- A uniform exponentially small error when both dimensions grow.
The sign is included: the normalized finite coefficient approaches `φ⁻¹`
from below. -/
theorem binaryGaussianCoefficient_normalized_error (r k : ℕ) (hk : k ≤ r) :
    0 ≤ eulerProduct⁻¹ -
        (binaryGaussianCoefficient r k : ℝ) / (2 : ℝ) ^ (k * (r - k)) ∧
      eulerProduct⁻¹ -
        (binaryGaussianCoefficient r k : ℝ) / (2 : ℝ) ^ (k * (r - k)) ≤
          ((1 / 2 : ℝ) ^ k + (1 / 2 : ℝ) ^ (r - k)) / eulerProduct ^ 3 := by
  rw [binaryGaussianCoefficient_normalized r k hk]
  have hφ := euler_positive
  have hA := eulerPartialProduct_pos r
  have hB := eulerPartialProduct_pos k
  have hC := eulerPartialProduct_pos (r - k)
  have hφA := eulerProduct_le_partial r
  have hφB := eulerProduct_le_partial k
  have hφC := eulerProduct_le_partial (r - k)
  have hAC := eulerPartialProduct_antitone (Nat.sub_le r k)
  have hB1 := eulerPartialProduct_le_one k
  have hC1 := eulerPartialProduct_le_one (r - k)
  have hφ1 : eulerProduct ≤ 1 := by simpa using eulerProduct_le_partial 0
  have hb := eulerPartialProduct_sub_bound k
  have hc := eulerPartialProduct_sub_bound (r - k)
  have hnum : 0 ≤ eulerPartialProduct k * eulerPartialProduct (r - k) -
      eulerProduct * eulerPartialProduct r := by
    have hm := mul_le_mul hφB hAC hA.le hB.le
    nlinarith
  have hnum_bound : eulerPartialProduct k * eulerPartialProduct (r - k) -
      eulerProduct * eulerPartialProduct r ≤
        (1 / 2 : ℝ) ^ k + (1 / 2 : ℝ) ^ (r - k) := by
    nlinarith [mul_nonneg hb.1 (sub_nonneg.mpr hC1),
      mul_nonneg hc.1 (sub_nonneg.mpr hφ1),
      mul_nonneg hφ.le (sub_nonneg.mpr hφA)]
  have hden : eulerProduct ^ 3 ≤
      eulerProduct * (eulerPartialProduct k * eulerPartialProduct (r - k)) := by
    have hm := mul_le_mul hφB hφC hφ.le hB.le
    nlinarith [mul_le_mul_of_nonneg_left hm hφ.le]
  have hid : eulerProduct⁻¹ -
      eulerPartialProduct r / (eulerPartialProduct k * eulerPartialProduct (r - k)) =
        (eulerPartialProduct k * eulerPartialProduct (r - k) -
          eulerProduct * eulerPartialProduct r) /
          (eulerProduct * (eulerPartialProduct k * eulerPartialProduct (r - k))) := by
    field_simp
  rw [hid]
  constructor
  · exact div_nonneg hnum (by positivity)
  · calc
      _ ≤ ((1 / 2 : ℝ) ^ k + (1 / 2 : ℝ) ^ (r - k)) /
          (eulerProduct * (eulerPartialProduct k * eulerPartialProduct (r - k))) :=
        div_le_div_of_nonneg_right hnum_bound (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) hden

end SymmetricSubgroupAsymptotics
