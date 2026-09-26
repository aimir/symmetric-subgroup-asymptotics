import SymmetricSubgroupAsymptotics.BinaryMixtureSmallSupportDecay
import SymmetricSubgroupAsymptotics.BinaryCarrierReserveEnvelope

/-! Normalized decay in the large-carrier regime. The exact coefficient
shift and the Gaussian parity loss remain in the displayed expressions.
A fixed polynomial factor may include the final finite bin sum. The last
theorem uses the proved actual terminal reserve, uniformly over all finite
critical index types; it assumes no model count or final numerical bound.
-/
set_option autoImplicit false
open Filter

namespace SymmetricSubgroupAsymptotics.BinaryMixtureNumerics

/-- Uniform absorption of the carrier envelope, the whole coefficient
shift, and any fixed positive polynomial prefactor. -/
theorem eventually_normalized_carrier_bound (A : ℝ) (hA : 0 < A)
    (k : ℕ) (K : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ n : ℕ in atTop, ∀ R a T : ℕ,
      n = R+2*a+4*T → a < 140*T →
      Real.sqrt (n : ℝ)/4 < (2*a+4*T : ℕ) →
      A * ((n : ℝ)+1)^k * (2*(n : ℝ))^(2*a+4*T) *
        (2 : ℝ)^(-(29/656)*(T : ℝ)*(n : ℝ)+K*(n : ℝ)*Real.log ((n : ℝ)+2)) ≤
          (2 : ℝ)^(-(29/1490432)*(n : ℝ)) := by
  obtain ⟨J, hJ, hpoly⟩ := polynomial_prefactor_le_rpow_log A hA k
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hconstant : 0 ≤ K+2/Real.log 2+J := by positivity
  filter_upwards [eventually_large_regime_exponent_le
      (K+2/Real.log 2+J) hconstant, eventually_ge_atTop 1] with n hdecay hn1
  intro R a T hn ha hsupp
  have hnreal : 1 ≤ (n : ℝ) := by exact_mod_cast hn1
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have hlarge : (a : ℝ)/140 < T := by
    have h : (a : ℝ) < 140*T := by exact_mod_cast ha
    linarith
  have hsupp' : Real.sqrt (n : ℝ)/4 < 2*(a : ℝ)+4*T := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hsupp
  have hshift_le : 2*(a : ℝ)+4*T ≤ (n : ℝ) := by
    exact_mod_cast (show 2*a+4*T ≤ n by omega)
  have hshiftcost := critical_shift_log_cost_le (n : ℝ) (2*(a : ℝ)+4*T)
    (n : ℝ) hnreal (by positivity) hshift_le
  have hlog0 : 0 ≤ Real.log ((n : ℝ)+2) := Real.log_nonneg (by linarith)
  have hpolycost : J*Real.log ((n : ℝ)+2) ≤ J*(n : ℝ)*Real.log ((n : ℝ)+2) := by
    have h := mul_le_mul_of_nonneg_right hnreal (mul_nonneg hJ hlog0)
    nlinarith only [h]
  have hexponent : -(29/656)*(T : ℝ)*(n : ℝ)+K*(n : ℝ)*Real.log ((n : ℝ)+2) +
      (2*(a : ℝ)+4*T)*Real.log (2*(n : ℝ))/Real.log 2 +
        J*Real.log ((n : ℝ)+2) ≤ -(29/1490432)*(n : ℝ) := by
    calc
      _ ≤ (-(29/656)*(T : ℝ)*(n : ℝ)+K*(n : ℝ)*Real.log ((n : ℝ)+2) +
          (2/Real.log 2)*(n : ℝ)*Real.log ((n : ℝ)+2)) +
            J*(n : ℝ)*Real.log ((n : ℝ)+2) :=
        add_le_add (add_le_add le_rfl hshiftcost) hpolycost
      _ = -(29/656)*(T : ℝ)*(n : ℝ) +
          (K+2/Real.log 2+J)*(n : ℝ)*Real.log ((n : ℝ)+2) := by ring
      _ ≤ _ := hdecay a T hlarge hsupp'
  have hnpos : 0 < 2*(n : ℝ) := by linarith
  have hshift : (2*(n : ℝ))^(2*a+4*T) =
      (2 : ℝ)^((2*(a : ℝ)+4*T)*Real.log (2*(n : ℝ))/Real.log 2) := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
      natpow_eq_two_rpow_log (2*(n : ℝ)) hnpos (2*a+4*T)
  calc
    _ ≤ (2 : ℝ)^(J*Real.log ((n : ℝ)+2)) * (2*(n : ℝ))^(2*a+4*T) *
        (2 : ℝ)^(-(29/656)*(T : ℝ)*(n : ℝ)+K*(n : ℝ)*Real.log ((n : ℝ)+2)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hpoly n hn1) (pow_nonneg hnpos.le _)) (by positivity)
    _ = (2 : ℝ)^(-(29/656)*(T : ℝ)*(n : ℝ)+K*(n : ℝ)*Real.log ((n : ℝ)+2) +
        (2*(a : ℝ)+4*T)*Real.log (2*(n : ℝ))/Real.log 2 +
          J*Real.log ((n : ℝ)+2)) := by
      rw [hshift, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent

/-- The original thirteen-color weight bound and the exact Gaussian lower
bound are normalized without replacing any original action divisor. -/
theorem eventually_normalized_carrier_with_gaussian_lower (φ : ℝ) (hφ : 0 < φ)
    (k : ℕ) (K : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ n : ℕ in atTop, ∀ R a T : ℕ,
      n = R+2*a+4*T → a < 140*T →
      Real.sqrt (n : ℝ)/4 < (2*a+4*T : ℕ) →
      (Real.exp 13 * ((n : ℝ)+1)^k * (2*(n : ℝ))^(2*a+4*T) *
        (2 : ℝ)^((n : ℝ)^2/4-(29/656)*(T : ℝ)*(n : ℝ)+
          K*(n : ℝ)*Real.log ((n : ℝ)+2))) /
        (φ*(2 : ℝ)^((n : ℝ)^2/4-1/4)) ≤ (2 : ℝ)^(-(29/1490432)*(n : ℝ)) := by
  let A : ℝ := Real.exp 13 * φ⁻¹ * (2 : ℝ)^(1/4 : ℝ)
  have hA : 0 < A := by dsimp [A]; positivity
  filter_upwards [eventually_normalized_carrier_bound A hA k K hK] with n hn
  intro R a T hN ha hsupp
  have hpowers :
      (2 : ℝ)^((n : ℝ)^2/4-(29/656)*(T : ℝ)*(n : ℝ)+K*(n : ℝ)*Real.log ((n : ℝ)+2)) /
        (2 : ℝ)^((n : ℝ)^2/4-1/4) =
      (2 : ℝ)^(1/4 : ℝ) *
        (2 : ℝ)^(-(29/656)*(T : ℝ)*(n : ℝ)+K*(n : ℝ)*Real.log ((n : ℝ)+2)) := by
    rw [← Real.rpow_sub (by norm_num : (0 : ℝ) < 2),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  calc
    _ = (Real.exp 13 * φ⁻¹) * ((n : ℝ)+1)^k * (2*(n : ℝ))^(2*a+4*T) *
        ((2 : ℝ)^((n : ℝ)^2/4-(29/656)*(T : ℝ)*(n : ℝ)+K*(n : ℝ)*Real.log ((n : ℝ)+2)) /
          (2 : ℝ)^((n : ℝ)^2/4-1/4)) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = A * ((n : ℝ)+1)^k * (2*(n : ℝ))^(2*a+4*T) *
        (2 : ℝ)^(-(29/656)*(T : ℝ)*(n : ℝ)+K*(n : ℝ)*Real.log ((n : ℝ)+2)) := by
      rw [hpowers]
      dsimp [A]
      ring
    _ ≤ _ := hn R a T hN ha hsupp

/-- The proved actual reserve supplies its own fixed logarithmic envelope.
The critical rank is enlarged only for the C4 comparison; the coefficient
shift remains 2a+4T from the original profile. The cutoff is uniform over
the finite critical index type and all its factors. -/
theorem eventually_terminalProductReserve_decay (φ : ℝ) (hφ : 0 < φ) (b k : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ {ι : Type} [Fintype ι]
      (a₀ a L T : ℕ) (s : ι → Bool),
      n = criticalProductRank a₀ s+2*a+4*T → L ≤ T → a < 140*T →
      Real.sqrt (n : ℝ)/4 < (2*a+4*T : ℕ) →
      (Real.exp 13 * ((n : ℝ)+1)^k * (2*(n : ℝ))^(2*a+4*T) *
        BinaryCarrierWord.terminalProductReserve (a₀+2*a) s b L (T : ℝ)) /
        (φ*(2 : ℝ)^((n : ℝ)^2/4-1/4)) ≤ (2 : ℝ)^(-(29/1490432)*(n : ℝ)) := by
  filter_upwards [eventually_normalized_carrier_with_gaussian_lower φ hφ k
      (BinaryCarrierReserveEnvelope.constant b) (BinaryCarrierReserveEnvelope.constant_nonneg b),
    eventually_ge_atTop 1] with n hn hn1
  intro ι _ a₀ a L T s hN hL ha hsupp
  have hnreal : 1 ≤ (n : ℝ) := by exact_mod_cast hn1
  have hrank : criticalProductRank (a₀+2*a) s = criticalProductRank a₀ s + 2*a := by
    unfold criticalProductRank
    omega
  have htotal : (criticalProductRank (a₀+2*a) s : ℝ)+4*T = (n : ℝ) := by
    rw [hrank]
    exact_mod_cast hN.symm
  have henv := BinaryCarrierReserveEnvelope.terminalProductReserve_le b (a₀+2*a) s L (T : ℝ)
    (by positivity) (by exact_mod_cast hL) (by simpa only [htotal] using hnreal)
  rw [htotal] at henv
  calc
    _ ≤ (Real.exp 13 * ((n : ℝ)+1)^k * (2*(n : ℝ))^(2*a+4*T) *
        (2 : ℝ)^((n : ℝ)^2/4-(29/656)*(T : ℝ)*(n : ℝ)+
          BinaryCarrierReserveEnvelope.constant b*(n : ℝ)*Real.log ((n : ℝ)+2))) /
        (φ*(2 : ℝ)^((n : ℝ)^2/4-1/4)) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left henv (by positivity)) (by positivity)
    _ ≤ _ := hn (criticalProductRank a₀ s) a T hN ha hsupp

end SymmetricSubgroupAsymptotics.BinaryMixtureNumerics
