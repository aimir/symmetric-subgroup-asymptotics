import SymmetricSubgroupAsymptotics.GrowingQuotientHotAggregate

/-!
# Absorbing a subexponential growing menu mass

One direct original-weight hypothesis subsumes the certificate constants and
the number of action classes.  The universal pointing polynomials, Euler
constants, linear hot correction, and the finite sum over widths are all
absorbed into arbitrarily small `w*n` or `n^2` exponents.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

variable {ι : ℕ → Type*} [∀ w, Fintype (ι w)]

/-- Direct subexponential control of the original weighted certificate mass.
This is uniform simultaneously over every retained width. -/
def GrowingMenuMassBound (w₀ : ℕ)
    (D : ∀ w, ι w → ℕ → ℝ) (A : ∀ w, ι w → ℝ) : Prop :=
  ∀ γ : ℝ, 0 < γ → ∀ᶠ n : ℕ in atTop, ∀ w,
    w ∈ Finset.Ico w₀ (n + 1) →
      (∑ i, D w i (n - w) / A w i) ≤ (2 : ℝ) ^ (γ * w * n)

private theorem eventually_succ_le_two_rpow {γ : ℝ} (hγ : 0 < γ) :
    ∀ᶠ n : ℕ in atTop, ((n + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (γ * n) := by
  filter_upwards [eventually_shifted_natpow_mul_exponential_le 1 1 hγ,
    eventually_exponential_le_inv_rpow (show 0 < γ / 2 by positivity) 1,
    eventually_ge_atTop 2] with n hpoly hexp hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hexp' : (2 : ℝ) ^ (-(γ / 2) * n) ≤ 1 / (n : ℝ) := by
    simpa using hexp
  have hsmall : ((n + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-γ * n) ≤ 1 := by
    calc
      _ ≤ 2 * (2 : ℝ) ^ (-(γ / 2) * n) := by simpa using hpoly
      _ ≤ 2 * (1 / (n : ℝ)) := mul_le_mul_of_nonneg_left hexp' (by norm_num)
      _ ≤ 1 := by
        rw [mul_one_div]
        exact (div_le_iff₀ hnpos).2 (by
          simpa using (show (2 : ℝ) ≤ n by exact_mod_cast hn))
  calc
    ((n + 1 : ℕ) : ℝ) =
        (((n + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-γ * n)) *
          (2 : ℝ) ^ (γ * n) := by
      rw [mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      rw [show -γ * (n : ℝ) + γ * n = 0 by ring, Real.rpow_zero, mul_one]
    _ ≤ 1 * (2 : ℝ) ^ (γ * n) :=
      mul_le_mul_of_nonneg_right hsmall (by positivity)
    _ = _ := one_mul _

private theorem eventually_const_le_two_rpow {C γ : ℝ}
    (hC : 0 ≤ C) (hγ : 0 < γ) :
    ∀ᶠ n : ℕ in atTop, C ≤ (2 : ℝ) ^ (γ * n) := by
  filter_upwards [eventually_exponential_le_inv_rpow hγ 1,
    eventually_ge_atTop (max 1 ⌈C⌉₊)] with n hexp hn
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (show 0 < n by omega)
  have hexp' : (2 : ℝ) ^ (-γ * n) ≤ 1 / (n : ℝ) := by
    simpa using hexp
  have hCn : C ≤ (n : ℝ) :=
    (Nat.le_ceil C).trans (by exact_mod_cast (le_max_right 1 ⌈C⌉₊).trans hn)
  have hsmall : C * (2 : ℝ) ^ (-γ * n) ≤ 1 := by
    calc
      _ ≤ C * (1 / (n : ℝ)) := mul_le_mul_of_nonneg_left hexp' hC
      _ ≤ 1 := by rw [mul_one_div]; exact (div_le_one hnpos).2 hCn
  calc
    C = (C * (2 : ℝ) ^ (-γ * n)) * (2 : ℝ) ^ (γ * n) := by
      rw [mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      rw [show -γ * (n : ℝ) + γ * n = 0 by ring, Real.rpow_zero, mul_one]
    _ ≤ 1 * (2 : ℝ) ^ (γ * n) :=
      mul_le_mul_of_nonneg_right hsmall (by positivity)
    _ = _ := one_mul _

/-- The direct menu-mass hypothesis supplies the complete cold overhead at
every retained width. -/
theorem growingMenuMass_cold_overhead
    {ρ : ℝ} (w₀ : ℕ)
    (D : ∀ w, ι w → ℕ → ℝ) (A : ∀ w, ι w → ℝ)
    (hρ : 0 < ρ) (hw₀ : 5 ≤ w₀)
    (hD : ∀ w i b, 0 ≤ D w i b) (hA : ∀ w i, 0 < A w i)
    (hmass : GrowingMenuMassBound w₀ D A) :
    ∀ᶠ n : ℕ in atTop, ∀ w, w ∈ Finset.Ico w₀ (n + 1) →
      eulerProduct⁻¹ ^ 2 * (((n + 1 : ℕ) : ℝ) ^ (w + 2)) *
          (2 : ℝ) ^ ((halfDegree w : ℝ) / 4 + 1 / 4) *
          (∑ i, D w i (n - w) / A w i) ≤
        (2 : ℝ) ^ (ρ * w * n / 16) := by
  let γ : ℝ := ρ / 512
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have hφ : 0 ≤ eulerProduct⁻¹ ^ 2 := pow_nonneg (inv_nonneg.mpr euler_positive.le) 2
  filter_upwards [hmass γ hγ, eventually_succ_le_two_rpow hγ,
    eventually_const_le_two_rpow hφ hγ,
    eventually_ge_atTop (max 1 ⌈(1 : ℝ) / γ⌉₊)] with n hmassn hbase hconst hn
  intro w hw
  have hww := Finset.mem_Ico.mp hw
  have hwn : w ≤ n := by omega
  have hw5 : 5 ≤ w := hw₀.trans hww.1
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hγn : (1 : ℝ) ≤ γ * n := by
    have hnγ : (1 : ℝ) / γ ≤ n :=
      (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 1 ⌈(1 : ℝ) / γ⌉₊).trans hn)
    simpa [mul_comm] using (div_le_iff₀ hγ).mp hnγ
  have hmassw := hmassn w hw
  have hpoly : (((n + 1 : ℕ) : ℝ) ^ (w + 2)) ≤
      (2 : ℝ) ^ (2 * γ * w * n) := by
    have hp := pow_le_pow_left₀ (by positivity) hbase (w + 2)
    calc
      _ ≤ ((2 : ℝ) ^ (γ * n)) ^ (w + 2) := hp
      _ = (2 : ℝ) ^ (γ * n * (w + 2)) := by
        rw [← Real.rpow_natCast,
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        push_cast
        rfl
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
        have hw2 : (w : ℝ) + 2 ≤ 2 * (w : ℝ) := by
          exact_mod_cast (show w + 2 ≤ 2 * w by omega)
        calc
          γ * (n : ℝ) * ((w : ℝ) + 2) ≤
              γ * n * (2 * (w : ℝ)) :=
            mul_le_mul_of_nonneg_left hw2
              (mul_nonneg hγ.le (by positivity))
          _ = 2 * γ * w * n := by ring)
  have hlinear : (2 : ℝ) ^ ((halfDegree w : ℝ) / 4 + 1 / 4) ≤
      (2 : ℝ) ^ (γ * w * n) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hr : (halfDegree w : ℝ) ≤ w := by
      exact_mod_cast (show halfDegree w ≤ w by unfold halfDegree; omega)
    have hw1 : (1 : ℝ) ≤ w := by exact_mod_cast (show 1 ≤ w by omega)
    nlinarith [mul_le_mul_of_nonneg_right hγn (by positivity : (0 : ℝ) ≤ w)]
  have hconstw : eulerProduct⁻¹ ^ 2 ≤ (2 : ℝ) ^ (γ * w * n) :=
    hconst.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
      have hw1 : (1 : ℝ) ≤ w := by exact_mod_cast (show 1 ≤ w by omega)
      nlinarith [mul_nonneg hγ.le (sub_nonneg.mpr hnR)]))
  have hmass0 : 0 ≤ ∑ i, D w i (n - w) / A w i :=
    Finset.sum_nonneg fun i _ => div_nonneg (hD w i (n - w)) (hA w i).le
  calc
    _ ≤ (2 : ℝ) ^ (γ * w * n) * (2 : ℝ) ^ (2 * γ * w * n) *
        (2 : ℝ) ^ (γ * w * n) * (2 : ℝ) ^ (γ * w * n) := by
      exact mul_le_mul
        (mul_le_mul (mul_le_mul hconstw hpoly (by positivity) (by positivity))
          hlinear (by positivity) (by positivity))
        hmassw hmass0 (by positivity)
    _ = (2 : ℝ) ^ (5 * γ * w * n) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
      dsimp [γ]
      have hwn0 : 0 ≤ (w : ℝ) * n := by positivity
      nlinarith)

/-- The same direct mass hypothesis supplies the complete hot overhead after
summing all retained widths. -/
theorem growingMenuMass_hot_overhead
    {ρ : ℝ} (w₀ : ℕ)
    (D : ∀ w, ι w → ℕ → ℝ) (A : ∀ w, ι w → ℝ)
    (hρ : 0 < ρ)
    (hD : ∀ w i b, 0 ≤ D w i b) (hA : ∀ w i, 0 < A w i)
    (hmass : GrowingMenuMassBound w₀ D A) :
    ∀ᶠ n : ℕ in atTop,
      eulerProduct⁻¹ * (((n + 1 : ℕ) : ℝ) ^ n) *
          (2 : ℝ) ^ (5 * (n : ℝ) / 8 + 1 / 4) *
          (∑ w ∈ Finset.Ico w₀ (n + 1), ∑ i, D w i (n - w) / A w i) ≤
        (2 : ℝ) ^ (ρ ^ 2 * (n : ℝ) ^ 2 / 16) := by
  let γ : ℝ := ρ ^ 2 / 512
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have hφ : 0 ≤ eulerProduct⁻¹ := inv_nonneg.mpr euler_positive.le
  filter_upwards [hmass γ hγ, eventually_succ_le_two_rpow hγ,
    eventually_const_le_two_rpow hφ hγ,
    eventually_linear_add_le_quadratic hγ (by norm_num : (0 : ℝ) ≤ 5 / 8)
      (by norm_num : (0 : ℝ) ≤ 1 / 4), eventually_ge_atTop 1] with
      n hmassn hbase hconst hlinear hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hmassSum :
      (∑ w ∈ Finset.Ico w₀ (n + 1), ∑ i, D w i (n - w) / A w i) ≤
        ((n + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (γ * (n : ℝ) ^ 2) := by
    calc
      _ ≤ ∑ _w ∈ Finset.Ico w₀ (n + 1),
          (2 : ℝ) ^ (γ * (n : ℝ) ^ 2) := by
        apply Finset.sum_le_sum
        intro w hw
        have hww := Finset.mem_Ico.mp hw
        have hwn : w ≤ n := by omega
        exact (hmassn w hw).trans
          (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
            have hγn : 0 ≤ γ * (n : ℝ) := by positivity
            nlinarith [mul_nonneg hγn (show 0 ≤ (n : ℝ) - w by
              exact sub_nonneg.mpr (by exact_mod_cast hwn))]))
      _ = (Finset.Ico w₀ (n + 1)).card *
          (2 : ℝ) ^ (γ * (n : ℝ) ^ 2) := by simp
      _ ≤ ((n + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (γ * (n : ℝ) ^ 2) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have hcard : (Finset.Ico w₀ (n + 1)).card ≤ n + 1 := by
          rw [Nat.card_Ico]
          omega
        exact_mod_cast hcard
  have hpoly : (((n + 1 : ℕ) : ℝ) ^ n) ≤
      (2 : ℝ) ^ (γ * (n : ℝ) ^ 2) := by
    have hp := pow_le_pow_left₀ (by positivity) hbase n
    calc
      _ ≤ ((2 : ℝ) ^ (γ * n)) ^ n := hp
      _ = _ := by
        rw [← Real.rpow_natCast,
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        ring
  have hsucc : ((n + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (γ * (n : ℝ) ^ 2) :=
    hbase.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
      nlinarith [mul_nonneg hγ.le (mul_nonneg (show 0 ≤ (n : ℝ) by positivity)
        (sub_nonneg.mpr hnR))]))
  have hconst' : eulerProduct⁻¹ ≤ (2 : ℝ) ^ (γ * (n : ℝ) ^ 2) :=
    hconst.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
      nlinarith [mul_nonneg hγ.le (mul_nonneg (show 0 ≤ (n : ℝ) by positivity)
        (sub_nonneg.mpr hnR))]))
  have hlinear' : (2 : ℝ) ^ (5 * (n : ℝ) / 8 + 1 / 4) ≤
      (2 : ℝ) ^ (γ * (n : ℝ) ^ 2) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
      nlinarith [hlinear])
  have hmassTotal0 :
      0 ≤ ∑ w ∈ Finset.Ico w₀ (n + 1), ∑ i, D w i (n - w) / A w i := by
    exact Finset.sum_nonneg fun w _ =>
      Finset.sum_nonneg fun i _ => div_nonneg (hD w i (n - w)) (hA w i).le
  have hmassBound :
      (∑ w ∈ Finset.Ico w₀ (n + 1), ∑ i, D w i (n - w) / A w i) ≤
        (2 : ℝ) ^ (γ * (n : ℝ) ^ 2) *
          (2 : ℝ) ^ (γ * (n : ℝ) ^ 2) := by
    exact hmassSum.trans (mul_le_mul_of_nonneg_right hsucc (by positivity))
  calc
    _ ≤ (2 : ℝ) ^ (γ * (n : ℝ) ^ 2) *
        (2 : ℝ) ^ (γ * (n : ℝ) ^ 2) *
        (2 : ℝ) ^ (γ * (n : ℝ) ^ 2) *
        (((2 : ℝ) ^ (γ * (n : ℝ) ^ 2)) *
          (2 : ℝ) ^ (γ * (n : ℝ) ^ 2)) := by
      exact mul_le_mul
        (mul_le_mul (mul_le_mul hconst' hpoly (by positivity) (by positivity))
          hlinear' (by positivity) (by positivity))
        hmassBound hmassTotal0 (by positivity)
    _ = (2 : ℝ) ^ (5 * γ * (n : ℝ) ^ 2) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
      dsimp [γ]
      have hn2 : 0 ≤ (n : ℝ) ^ 2 := sq_nonneg _
      nlinarith)

end SymmetricSubgroupAsymptotics

end
