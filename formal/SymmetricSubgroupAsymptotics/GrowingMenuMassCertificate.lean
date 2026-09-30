import SymmetricSubgroupAsymptotics.GrowingMenuMassAbsorption

/-!
# Checkable certificates for a growing weighted menu mass

The growing quotient transfer asks for a subexponential bound uniform in the
removed width and the ambient degree.  In applications the available estimate
has a more concrete form: a fixed polynomial in the ambient degree times a
width exponent whose quadratic coefficient can be made arbitrarily small.

This file proves that the concrete form implies `GrowingMenuMassBound`.  It is
the numerical bridge used by the pre-E7 action menu; no action classification,
normal-axis count, or local epimorphism estimate is hidden in the bridge.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

variable {ι : ℕ → Type*} [∀ w, Fintype (ι w)]

/-- A directly checkable menu-mass estimate.  For every positive quadratic
coefficient, the complete original weighted mass is bounded by a fixed
polynomial in the ambient degree times `2^(epsilon*w^2)`.  The constants may
depend on `epsilon`, but not on the width, complement, or ambient degree. -/
def PolynomialSubquadraticMenuMassBound (w₀ : ℕ)
    (D : ∀ w, ι w → ℕ → ℝ) (A : ∀ w, ι w → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ B : ℝ, ∃ p : ℕ, 0 ≤ B ∧
      ∀ n w, w ∈ Finset.Ico w₀ (n + 1) →
        (∑ i, D w i (n - w) / A w i) ≤
          B * (((n + 1 : ℕ) : ℝ) ^ p) *
            (2 : ℝ) ^ (ε * (w : ℝ) ^ 2)

private theorem eventually_const_le_two_rpow
    {C γ : ℝ} (hC : 0 ≤ C) (hγ : 0 < γ) :
    ∀ᶠ n : ℕ in atTop, C ≤ (2 : ℝ) ^ (γ * n) := by
  filter_upwards [eventually_exponential_le_inv_rpow hγ 1,
    eventually_ge_atTop (max 1 ⌈C⌉₊)] with n hexp hn
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (show 0 < n by omega)
  have hexp' : (2 : ℝ) ^ (-γ * n) ≤ 1 / (n : ℝ) := by
    simpa using hexp
  have hCn : C ≤ (n : ℝ) :=
    (Nat.le_ceil C).trans
      (by exact_mod_cast (le_max_right 1 ⌈C⌉₊).trans hn)
  have hsmall : C * (2 : ℝ) ^ (-γ * n) ≤ 1 := by
    calc
      C * (2 : ℝ) ^ (-γ * n) ≤ C * (1 / (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hexp' hC
      _ ≤ 1 := by
        rw [mul_one_div]
        exact (div_le_one hnpos).2 hCn
  calc
    C = (C * (2 : ℝ) ^ (-γ * n)) * (2 : ℝ) ^ (γ * n) := by
      rw [mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      rw [show -γ * (n : ℝ) + γ * n = 0 by ring,
        Real.rpow_zero, mul_one]
    _ ≤ 1 * (2 : ℝ) ^ (γ * n) :=
      mul_le_mul_of_nonneg_right hsmall (by positivity)
    _ = _ := one_mul _

private theorem eventually_succ_pow_le_two_rpow
    (p : ℕ) {γ : ℝ} (hγ : 0 < γ) :
    ∀ᶠ n : ℕ in atTop,
      (((n + 1 : ℕ) : ℝ) ^ p) ≤ (2 : ℝ) ^ (γ * n) := by
  have hhalf : 0 < γ / 2 := by positivity
  filter_upwards [eventually_shifted_natpow_mul_exponential_le 1 p hγ,
    eventually_const_le_two_rpow
      (C := (((2 : ℕ) : ℝ) ^ p)) (by positivity) hhalf] with n hpoly hconst
  have hsmall : (((n + 1 : ℕ) : ℝ) ^ p) *
      (2 : ℝ) ^ (-γ * n) ≤ 1 := by
    calc
      (((n + 1 : ℕ) : ℝ) ^ p) * (2 : ℝ) ^ (-γ * n) ≤
          (((2 : ℕ) : ℝ) ^ p) * (2 : ℝ) ^ (-(γ / 2) * n) := by
        simpa only [Nat.cast_ofNat] using hpoly
      _ ≤ (2 : ℝ) ^ ((γ / 2) * n) *
          (2 : ℝ) ^ (-(γ / 2) * n) :=
        mul_le_mul_of_nonneg_right hconst (by positivity)
      _ = 1 := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        rw [show (γ / 2) * (n : ℝ) + -(γ / 2) * n = 0 by ring,
          Real.rpow_zero]
  calc
    (((n + 1 : ℕ) : ℝ) ^ p) =
        ((((n + 1 : ℕ) : ℝ) ^ p) * (2 : ℝ) ^ (-γ * n)) *
          (2 : ℝ) ^ (γ * n) := by
      rw [mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      rw [show -γ * (n : ℝ) + γ * n = 0 by ring,
        Real.rpow_zero, mul_one]
    _ ≤ 1 * (2 : ℝ) ^ (γ * n) :=
      mul_le_mul_of_nonneg_right hsmall (by positivity)
    _ = _ := one_mul _

/-- A polynomial times an arbitrarily small quadratic width exponent is
uniformly subexponential on every triangle `w₀ <= w <= n`.  This is the exact
`GrowingMenuMassBound` consumed by both the hot and cold quotient estimates. -/
theorem growingMenuMassBound_of_polynomialSubquadratic
    {w₀ : ℕ} (hw₀ : 1 ≤ w₀)
    (D : ∀ w, ι w → ℕ → ℝ) (A : ∀ w, ι w → ℝ)
    (h : PolynomialSubquadraticMenuMassBound w₀ D A) :
    GrowingMenuMassBound w₀ D A := by
  intro γ hγ
  let ε : ℝ := γ / 3
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨B, p, hB, hbound⟩ := h ε hε
  filter_upwards [eventually_const_le_two_rpow hB hε,
    eventually_succ_pow_le_two_rpow p hε] with n hconst hpoly
  intro w hw
  have hwn : w ≤ n := by
    have := (Finset.mem_Ico.mp hw).2
    omega
  have hw1 : 1 ≤ w := hw₀.trans (Finset.mem_Ico.mp hw).1
  have hwR : (1 : ℝ) ≤ w := by exact_mod_cast hw1
  have hwnR : (w : ℝ) ≤ n := by exact_mod_cast hwn
  calc
    (∑ i, D w i (n - w) / A w i) ≤
        B * (((n + 1 : ℕ) : ℝ) ^ p) *
          (2 : ℝ) ^ (ε * (w : ℝ) ^ 2) := hbound n w hw
    _ ≤ (2 : ℝ) ^ (ε * n) * (2 : ℝ) ^ (ε * n) *
        (2 : ℝ) ^ (ε * (w : ℝ) ^ 2) := by
      exact mul_le_mul
        (mul_le_mul hconst hpoly (by positivity) (by positivity))
        (le_rfl) (by positivity) (by positivity)
    _ = (2 : ℝ) ^
        (ε * n + ε * n + ε * (w : ℝ) ^ 2) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    _ ≤ (2 : ℝ) ^ (γ * w * n) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
        dsimp [ε]
        have hn0 : (0 : ℝ) ≤ n := by positivity
        have hw0 : (0 : ℝ) ≤ w := by positivity
        nlinarith [mul_nonneg (sub_nonneg.mpr hwR) hn0,
          mul_nonneg hw0 (sub_nonneg.mpr (sub_nonneg.mpr hwnR))])

end SymmetricSubgroupAsymptotics

end
