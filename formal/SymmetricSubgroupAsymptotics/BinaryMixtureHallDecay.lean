import SymmetricSubgroupAsymptotics.BinaryMixtureSmallSupportDecay

/-! Uniform normalized decay in the small-carrier Hall regime. These
scalar estimates retain the original coefficient shift 2a+4T, the complete
Hall prefactor, and the parity loss in the Gaussian lower bound. All
thresholds depend only on fixed constants, not on the original profile.
The actual model count and its original normalizer weights are installed
by separate counting theorems.
-/
set_option autoImplicit false
noncomputable section
open Filter

namespace SymmetricSubgroupAsymptotics.BinaryMixtureNumerics

def hallQuadratic (R a u : ℕ) : ℝ :=
  ((a : ℝ)+u+7)^2/3 + ((a : ℝ)^2+((R : ℝ)+a+u)^2)/4

def hallPolynomial (R c a u : ℕ) : ℝ :=
  ((R : ℝ)+1) * ((c : ℝ)+1) * ((a : ℝ)+1) * ((R : ℝ)+u+a+1)

/-- Every literal Hall prefactor variable is bounded by the complete
half-degree in the small-carrier regime. -/
theorem hallPolynomial_le (n R c a u T : ℕ)
    (hn : n = R+2*a+4*T) (hc : c ≤ R) (hu : u ≤ 7*T) (hTa : 140*T ≤ a) :
    hallPolynomial R c a u ≤ ((n : ℝ)+1)^4 := by
  have hR : (R : ℝ)+1 ≤ (n : ℝ)+1 := by exact_mod_cast (show R+1 ≤ n+1 by omega)
  have hc' : (c : ℝ)+1 ≤ (n : ℝ)+1 := by exact_mod_cast (show c+1 ≤ n+1 by omega)
  have ha : (a : ℝ)+1 ≤ (n : ℝ)+1 := by exact_mod_cast (show a+1 ≤ n+1 by omega)
  have hlast : (R : ℝ)+u+a+1 ≤ (n : ℝ)+1 := by
    exact_mod_cast (show R+u+a+1 ≤ n+1 by omega)
  have hprod := mul_le_mul
    (mul_le_mul (mul_le_mul hR hc' (by positivity) (by positivity))
      ha (by positivity) (by positivity)) hlast (by positivity) (by positivity)
  calc
    _ ≤ (((n : ℝ)+1)*((n : ℝ)+1))*((n : ℝ)+1)*((n : ℝ)+1) := hprod
    _ = _ := by ring

/-- The scalar fixed-profile Hall bound is uniformly exponentially small
after its full critical-coefficient power. The constant A may contain all
fixed Euler and finite-alphabet weight factors. -/
theorem eventually_normalized_hall_bound (A : ℝ) (hA : 0 < A) :
    ∀ᶠ n : ℕ in atTop, ∀ R c a u T : ℕ,
      n = R+2*a+4*T → c ≤ R → 1 ≤ a → u ≤ 7*T → 140*T ≤ a →
      A * hallPolynomial R c a u * (2*(n : ℝ))^(2*a+4*T) *
        (2 : ℝ)^(hallQuadratic R a u - (n : ℝ)^2/4) ≤
          (2 : ℝ)^(-(n : ℝ)/50) := by
  obtain ⟨K, hK, hpoly⟩ := polynomial_prefactor_le_rpow_log A hA 4
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hconstant : 0 ≤ 28/Real.log 2 + K := by positivity
  filter_upwards [eventually_small_regime_exponent_le
      (28/Real.log 2 + K) hconstant, eventually_ge_atTop 1] with n hdecay hn1
  intro R c a u T hn hc ha hu hTa
  have hnreal : 1 ≤ (n : ℝ) := by exact_mod_cast hn1
  have hne : (n : ℝ) = (R : ℝ)+2*a+4*T := by exact_mod_cast hn
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hu' : (u : ℝ) ≤ 7*T := by exact_mod_cast hu
  have hTa' : (T : ℝ) ≤ (a : ℝ)/140 := by
    have h : 140*(T : ℝ) ≤ a := by exact_mod_cast hTa
    linarith
  have hHall := hall_exponent_with_critical_shift_le (R : ℝ) a u T
    (by positivity) ha' (by positivity) (by positivity) hu' hTa'
  rw [← hne] at hHall
  have hlog0 : 0 ≤ Real.log ((n : ℝ)+2) := Real.log_nonneg (by linarith)
  have hcost : K*Real.log ((n : ℝ)+2) ≤ K*(a : ℝ)*Real.log ((n : ℝ)+2) := by
    have h := mul_le_mul_of_nonneg_right ha' (mul_nonneg hK hlog0)
    nlinarith only [h]
  have hexponent : hallQuadratic R a u - (n : ℝ)^2/4 +
      (2*(a : ℝ)+4*T)*Real.log (2*(n : ℝ))/Real.log 2 +
        K*Real.log ((n : ℝ)+2) ≤ -(n : ℝ)/50 := by
    calc
      _ ≤ (-(a : ℝ)*(n : ℝ)/25 +
          (28/Real.log 2)*(a : ℝ)*Real.log ((n : ℝ)+2)) +
            K*(a : ℝ)*Real.log ((n : ℝ)+2) := by
        exact add_le_add (by simpa only [hallQuadratic] using hHall) hcost
      _ = -(a : ℝ)*(n : ℝ)/25 +
          (28/Real.log 2+K)*(a : ℝ)*Real.log ((n : ℝ)+2) := by ring
      _ ≤ _ := hdecay a ha'
  have hpolynomial : A * hallPolynomial R c a u ≤
      (2 : ℝ)^(K*Real.log ((n : ℝ)+2)) :=
    (mul_le_mul_of_nonneg_left (hallPolynomial_le n R c a u T hn hc hu hTa) hA.le).trans
      (hpoly n hn1)
  have hnpos : 0 < 2*(n : ℝ) := by linarith
  have hshift : (2*(n : ℝ))^(2*a+4*T) =
      (2 : ℝ)^((2*(a : ℝ)+4*T)*Real.log (2*(n : ℝ))/Real.log 2) := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
      natpow_eq_two_rpow_log (2*(n : ℝ)) hnpos (2*a+4*T)
  calc
    _ ≤ (2 : ℝ)^(K*Real.log ((n : ℝ)+2)) * (2*(n : ℝ))^(2*a+4*T) *
        (2 : ℝ)^(hallQuadratic R a u - (n : ℝ)^2/4) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hpolynomial (pow_nonneg hnpos.le _)) (by positivity)
    _ = (2 : ℝ)^(hallQuadratic R a u - (n : ℝ)^2/4 +
        (2*(a : ℝ)+4*T)*Real.log (2*(n : ℝ))/Real.log 2 +
          K*Real.log ((n : ℝ)+2)) := by
      rw [hshift, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent

/-- Explicit normalization with the complete original thirteen-color
weight constant and the Gaussian parity loss. The parameter phi is fixed
and positive; in counting applications it is the actual Euler product. -/
theorem eventually_normalized_hall_with_gaussian_lower (φ : ℝ) (hφ : 0 < φ) :
    ∀ᶠ n : ℕ in atTop, ∀ R c a u T : ℕ,
      n = R+2*a+4*T → c ≤ R → 1 ≤ a → u ≤ 7*T → 140*T ≤ a →
      (Real.exp 13 * (2*(n : ℝ))^(2*a+4*T) *
        (2*(φ⁻¹)^5 * hallPolynomial R c a u * (2 : ℝ)^(hallQuadratic R a u))) /
          (φ * (2 : ℝ)^((n : ℝ)^2/4-1/4)) ≤ (2 : ℝ)^(-(n : ℝ)/50) := by
  let A : ℝ := Real.exp 13 * 2 * (φ⁻¹)^6 * (2 : ℝ)^(1/4 : ℝ)
  have hA : 0 < A := by dsimp [A]; positivity
  filter_upwards [eventually_normalized_hall_bound A hA] with n hn
  intro R c a u T hN hc ha hu hTa
  have hpowers : (2 : ℝ)^(hallQuadratic R a u) /
      (2 : ℝ)^((n : ℝ)^2/4-1/4) =
        (2 : ℝ)^(1/4 : ℝ) * (2 : ℝ)^(hallQuadratic R a u - (n : ℝ)^2/4) := by
    rw [← Real.rpow_sub (by norm_num : (0 : ℝ) < 2),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  calc
    _ = (Real.exp 13 * 2 * (φ⁻¹)^6) * hallPolynomial R c a u *
        (2*(n : ℝ))^(2*a+4*T) *
          ((2 : ℝ)^(hallQuadratic R a u) / (2 : ℝ)^((n : ℝ)^2/4-1/4)) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = A * hallPolynomial R c a u * (2*(n : ℝ))^(2*a+4*T) *
        (2 : ℝ)^(hallQuadratic R a u - (n : ℝ)^2/4) := by
      rw [hpowers]
      dsimp [A]
      ring
    _ ≤ _ := hn R c a u T hN hc ha hu hTa

end SymmetricSubgroupAsymptotics.BinaryMixtureNumerics
