import SymmetricSubgroupAsymptotics.BinaryMixtureAbsorption

/-! Multiplicative normalization of the finite-alphabet small-support
estimate. The coefficient shift is the literal power (2N)^C. Any fixed
positive constant and any fixed polynomial degree are absorbed uniformly
in the original support C, so an extra support-size sum can use degree
k+1. No profile count, action divisor, or group-theoretic input occurs here.
-/
set_option autoImplicit false
open Filter

namespace SymmetricSubgroupAsymptotics.BinaryMixtureNumerics

/-- Every fixed positive polynomial prefactor has a uniform logarithmic
exponent. The exponent constant is independent of the degree variable n. -/
theorem polynomial_prefactor_le_rpow_log (A : ℝ) (hA : 0 < A) (k : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, 1 ≤ n →
      A * ((n : ℝ)+1)^k ≤ (2 : ℝ)^(K * Real.log ((n : ℝ)+2)) := by
  let M : ℝ := max (Real.log A) 0
  let K : ℝ := (M / Real.log 2 + (k : ℝ)) / Real.log 2
  have hM : 0 ≤ M := le_max_right _ _
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro n hn
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have hnp : 0 < (n : ℝ)+1 := by positivity
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
    (show (2 : ℝ) ≤ (n : ℝ)+2 by linarith)
  have hMbound : M ≤ (M / Real.log 2) * Real.log ((n : ℝ)+2) := by
    calc
      _ = (M * Real.log 2) / Real.log 2 := by field_simp [hlog2.ne']
      _ ≤ (M * Real.log ((n : ℝ)+2)) / Real.log 2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlog hM) hlog2.le
      _ = _ := by ring
  have hpolylog := mul_le_mul_of_nonneg_left
    (Real.log_le_log hnp (show (n : ℝ)+1 ≤ (n : ℝ)+2 by linarith))
    (show 0 ≤ (k : ℝ) by positivity)
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply (Real.log_le_iff_le_exp (mul_pos hA (pow_pos hnp k))).mp
  rw [Real.log_mul hA.ne' (pow_ne_zero k hnp.ne'), Real.log_pow]
  calc
    _ ≤ M + (k : ℝ) * Real.log ((n : ℝ)+2) :=
      add_le_add (le_max_left _ _) hpolylog
    _ ≤ (M / Real.log 2) * Real.log ((n : ℝ)+2) +
        (k : ℝ) * Real.log ((n : ℝ)+2) := add_le_add hMbound le_rfl
    _ = _ := by
      dsimp [K]
      field_simp [hlog2.ne']
      <;> ring

/-- Conversion of a literal natural power into its exact base-two
logarithmic exponent, valid for every positive original base. -/
theorem natpow_eq_two_rpow_log (x : ℝ) (hx : 0 < x) (C : ℕ) :
    x^C = (2 : ℝ)^((C : ℝ) * Real.log x / Real.log 2) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  have he : Real.log 2 * ((C : ℝ) * Real.log x / Real.log 2) =
      (C : ℝ) * Real.log x := by field_simp [hlog2.ne']
  rw [he, Real.exp_nat_mul, Real.exp_log hx]

/-- The explicit normalized small-support bound, including the original
critical-coefficient power and any fixed polynomial prefactor, is uniformly
exponentially small. Taking k=5 absorbs the extra factor N+1 needed for a
support-size sum when the fixed-support estimate has degree four. -/
theorem eventually_small_support_prefactor_bound (A : ℝ) (hA : 0 < A) (k : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ C : ℕ, (C : ℝ) ≤ Real.sqrt (n : ℝ)/4 →
      A * ((n : ℝ)+1)^k * (2*(n : ℝ))^C *
        (2 : ℝ)^(-(n : ℝ)/2+1/2+(211/192)*(C : ℝ)^2+(14/3)*C+49/3) ≤
          (2 : ℝ)^(-(n : ℝ)/4) := by
  obtain ⟨K, hK, hpoly⟩ := polynomial_prefactor_le_rpow_log A hA k
  filter_upwards [eventually_small_support_bound K hK,
    eventually_ge_atTop 1] with n hn hn1
  intro C hC
  have hnreal : 1 ≤ (n : ℝ) := by exact_mod_cast hn1
  have hnpos : 0 < 2*(n : ℝ) := by linarith
  let E : ℝ := -(n : ℝ)/2+1/2+(211/192)*(C : ℝ)^2+(14/3)*C+49/3
  have hshift := natpow_eq_two_rpow_log (2*(n : ℝ)) hnpos C
  have hmain := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hpoly n hn1)
      (pow_nonneg hnpos.le C)) (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) E)
  calc
    _ ≤ (2 : ℝ)^(K*Real.log ((n : ℝ)+2)) * (2*(n : ℝ))^C * (2 : ℝ)^E := hmain
    _ = (2 : ℝ)^(E + (C : ℝ)*Real.log (2*(n : ℝ))/Real.log 2 +
        K*Real.log ((n : ℝ)+2)) := by
      rw [hshift, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    _ ≤ _ := by
      simpa only [E] using hn (C : ℝ) (Nat.cast_nonneg C) hC

end SymmetricSubgroupAsymptotics.BinaryMixtureNumerics
