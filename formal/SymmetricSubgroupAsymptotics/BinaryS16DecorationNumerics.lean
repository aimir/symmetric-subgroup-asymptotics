import SymmetricSubgroupAsymptotics.BinaryCarrierParameterSmallSupport
import SymmetricSubgroupAsymptotics.BinaryCarrierHallProfiles
import SymmetricSubgroupAsymptotics.BinaryCarrierReserveProfiles

/-!
# Numerical absorption of the direct S16 decoration

The direct S16 encoder charges `(2N+2)^(20*C_old)`.  Its retained target
support `C` satisfies `C_old ≤ 4*C`.  This file keeps the strong pointwise
mixture envelopes until that charge has been paid.  In the small-support
strip the charge is subexponential; in the Hall and carrier regimes it is
absorbed respectively by the `a*N` and `T*N` reserves.
-/

set_option autoImplicit false
noncomputable section
open Filter

namespace SymmetricSubgroupAsymptotics.BinaryS16DecorationNumerics

open BinaryMixtureNumerics

private theorem log_decoration_base_le (n : ℕ) (hn : 1 ≤ n) :
    Real.log ((2*n+2 : ℕ) : ℝ) ≤ 2 * Real.log ((n : ℝ)+2) := by
  have hnpos : (0 : ℝ) < n+1 := by positivity
  have hlog2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
    (show (2 : ℝ) ≤ (n : ℝ)+2 by linarith)
  have hlogn := Real.log_le_log hnpos
    (show (n : ℝ)+1 ≤ (n : ℝ)+2 by linarith)
  have heq : (((2*n+2 : ℕ) : ℝ)) = 2*((n : ℝ)+1) := by push_cast; ring
  rw [heq, Real.log_mul (by norm_num) hnpos.ne']
  linarith

private theorem decoration_le_rpow_support
    (n Cold C : ℕ) (hn : 1 ≤ n) (hret : Cold ≤ 4*C) :
    (((2*n+2)^(20*Cold) : ℕ) : ℝ) ≤
      (2 : ℝ)^((160 / Real.log 2) * (C : ℝ) * Real.log ((n : ℝ)+2)) := by
  have hbase : (0 : ℝ) < ((2*n+2 : ℕ) : ℝ) := by positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog := log_decoration_base_le n hn
  have hCold : (Cold : ℝ) ≤ 4*C := by exact_mod_cast hret
  rw [Nat.cast_pow, natpow_eq_two_rpow_log _ hbase]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have hlog0 : 0 ≤ Real.log (((2*n+2 : ℕ) : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (show 1≤2*n+2 by omega))
  have h₁ := mul_le_mul_of_nonneg_right hCold
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 20) hlog0)
  have h₂ := mul_le_mul_of_nonneg_left hlog
    (show (0 : ℝ) ≤ 80*C by positivity)
  calc
    (((20*Cold : ℕ) : ℝ) * Real.log (((2*n+2 : ℕ) : ℝ))) / Real.log 2
        = (20*(Cold : ℝ) * Real.log (((2*n+2 : ℕ) : ℝ))) / Real.log 2 := by
            norm_num
    _ ≤ (80*(C : ℝ) * Real.log (((2*n+2 : ℕ) : ℝ))) / Real.log 2 :=
      div_le_div_of_nonneg_right (by nlinarith only [h₁]) hlog2.le
    _ ≤ (160*(C : ℝ)*Real.log ((n : ℝ)+2))/Real.log 2 :=
      div_le_div_of_nonneg_right (by nlinarith only [h₂]) hlog2.le
    _ = _ := by ring

/-- The S16 decoration is subexponential when the retained support is at
most `sqrt N / 4`. -/
theorem eventually_small_support_decoration :
    ∀ᶠ n : ℕ in atTop, ∀ Cold C : ℕ,
      Cold ≤ 4*C → (C : ℝ) ≤ Real.sqrt (n : ℝ)/4 →
      (((2*n+2)^(20*Cold) : ℕ) : ℝ) * (2 : ℝ)^(-(n : ℝ)/4) ≤
        (2 : ℝ)^(-(n : ℝ)/8) := by
  have hD : 0 ≤ (40 / Real.log 2 : ℝ) := by positivity
  filter_upwards [eventually_log_error_le_sqrt (40 / Real.log 2) hD
      (by norm_num : (0 : ℝ) < 1/8), eventually_ge_atTop 1] with n hlog hn
  intro Cold C hret hcut
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hsqrt0 := Real.sqrt_nonneg (n : ℝ)
  have hsq := Real.sq_sqrt hn0
  have hdec := decoration_le_rpow_support n Cold C hn hret
  have hx0 : 0 ≤ (40/Real.log 2)*Real.log ((n : ℝ)+2) :=
    mul_nonneg hD (Real.log_nonneg (by linarith))
  have hcost : (160 / Real.log 2) * (C : ℝ) * Real.log ((n : ℝ)+2) ≤
      (n : ℝ)/8 := by
    calc
      _ = (4*(C : ℝ))*((40/Real.log 2)*Real.log ((n : ℝ)+2)) := by ring
      _ ≤ Real.sqrt (n : ℝ) *
          ((40/Real.log 2)*Real.log ((n : ℝ)+2)) := by
        exact mul_le_mul_of_nonneg_right (by linarith) hx0
      _ ≤ Real.sqrt (n : ℝ) * ((1/8)*Real.sqrt (n : ℝ)) := by
        gcongr
      _ = (n : ℝ)/8 := by nlinarith only [hsq]
  calc
    _ ≤ (2 : ℝ)^((160 / Real.log 2) * (C : ℝ) * Real.log ((n : ℝ)+2)) *
        (2 : ℝ)^(-(n : ℝ)/4) :=
      mul_le_mul_of_nonneg_right hdec (by positivity)
    _ = (2 : ℝ)^((160 / Real.log 2) * (C : ℝ) *
          Real.log ((n : ℝ)+2) - (n : ℝ)/4) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

/-- Hall absorption with one additional fixed logarithmic cost per unit of
the cyclic-four parameter. -/
private theorem eventually_hall_with_support_log (D : ℝ) (hD : 0 ≤ D) :
    ∀ᶠ n : ℕ in atTop, ∀ R c a u T : ℕ,
      n = R+2*a+4*T → c ≤ R → 1 ≤ a → u ≤ 7*T → 140*T ≤ a →
      (Real.exp 13 * 2 * (eulerProduct⁻¹)^6 * (2 : ℝ)^(1/4 : ℝ)) *
        hallPolynomial R c a u * (2*(n : ℝ))^(2*a+4*T) *
        (2 : ℝ)^(hallQuadratic R a u-(n : ℝ)^2/4) *
        (2 : ℝ)^(D*(a : ℝ)*Real.log ((n : ℝ)+2)) ≤
          (2 : ℝ)^(-(n : ℝ)/50) := by
  let A : ℝ := Real.exp 13 * 2 * (eulerProduct⁻¹)^6 * (2 : ℝ)^(1/4 : ℝ)
  have hA : 0 < A := by dsimp [A]; positivity [euler_positive]
  obtain ⟨K,hK,hpoly⟩ := polynomial_prefactor_le_rpow_log A hA 4
  have hconstant : 0 ≤ 28/Real.log 2 + K + D := by positivity
  filter_upwards [eventually_small_regime_exponent_le
      (28/Real.log 2+K+D) hconstant, eventually_ge_atTop 1] with n hdecay hn
  intro R c a u T hN hc ha hu hTa
  have hnreal : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hne : (n : ℝ) = (R : ℝ)+2*a+4*T := by exact_mod_cast hN
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hu' : (u : ℝ) ≤ 7*T := by exact_mod_cast hu
  have hTa' : (T : ℝ) ≤ (a : ℝ)/140 := by
    have h : 140*(T : ℝ) ≤ a := by exact_mod_cast hTa
    linarith
  have hHall := hall_exponent_with_critical_shift_le (R : ℝ) a u T
    (by positivity) ha' (by positivity) (by positivity) hu' hTa'
  rw [← hne] at hHall
  have hlog0 : 0 ≤ Real.log ((n : ℝ)+2) := Real.log_nonneg (by linarith)
  have hKcost : K*Real.log ((n : ℝ)+2) ≤
      K*(a : ℝ)*Real.log ((n : ℝ)+2) := by
    have h := mul_le_mul_of_nonneg_right ha' (mul_nonneg hK hlog0)
    nlinarith only [h]
  have hexponent : hallQuadratic R a u-(n : ℝ)^2/4 +
      (2*(a : ℝ)+4*T)*Real.log (2*(n : ℝ))/Real.log 2 +
      K*Real.log ((n : ℝ)+2) + D*(a : ℝ)*Real.log ((n : ℝ)+2) ≤
        -(n : ℝ)/50 := by
    calc
      _ ≤ (-a*(n : ℝ)/25+(28/Real.log 2)*a*Real.log ((n : ℝ)+2)) +
          K*a*Real.log ((n : ℝ)+2) + D*a*Real.log ((n : ℝ)+2) := by
        exact add_le_add (add_le_add hHall hKcost) le_rfl
      _ = -a*(n : ℝ)/25 +
          (28/Real.log 2+K+D)*a*Real.log ((n : ℝ)+2) := by ring
      _ ≤ _ := hdecay a ha'
  have hpoly : A*hallPolynomial R c a u ≤
      (2 : ℝ)^(K*Real.log ((n : ℝ)+2)) :=
    (mul_le_mul_of_nonneg_left (hallPolynomial_le n R c a u T hN hc hu hTa)
      hA.le).trans (hpoly n hn)
  have hnpos : 0 < 2*(n : ℝ) := by positivity
  have hshift := natpow_eq_two_rpow_log (2*(n : ℝ)) hnpos (2*a+4*T)
  change A * hallPolynomial R c a u * (2*(n : ℝ))^(2*a+4*T) *
      (2 : ℝ)^(hallQuadratic R a u-(n : ℝ)^2/4) *
      (2 : ℝ)^(D*(a : ℝ)*Real.log ((n : ℝ)+2)) ≤ _
  calc
    _ ≤ (2 : ℝ)^(K*Real.log ((n : ℝ)+2)) * (2*(n : ℝ))^(2*a+4*T) *
        (2 : ℝ)^(hallQuadratic R a u-(n : ℝ)^2/4) *
        (2 : ℝ)^(D*(a : ℝ)*Real.log ((n : ℝ)+2)) := by
      gcongr <;> positivity
    _ = (2 : ℝ)^(hallQuadratic R a u-(n : ℝ)^2/4 +
        (2*(a : ℝ)+4*T)*Real.log (2*(n : ℝ))/Real.log 2 +
        K*Real.log ((n : ℝ)+2) + D*(a : ℝ)*Real.log ((n : ℝ)+2)) := by
      rw [hshift, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      push_cast
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent

/-- Pointwise Hall-bin estimate after paying the full retained S16
decoration. -/
theorem eventually_hall_bin_decoration :
    ∀ᶠ n : ℕ in atTop, ∀ R a T Cold : ℕ,
      n=R+2*a+4*T → 1≤a → 140*T≤a → Cold≤4*(2*a+4*T) →
      (((2*n+2)^(20*Cold) : ℕ) : ℝ) *
        ((Nat.card (BinaryCarrierParameterProfiles.PhysicalFamily R a T
          (Fin (2*(R+2*a+4*T)))) : ℝ) / exactBenchmark (2*(R+2*a+4*T))) ≤
        (2 : ℝ)^(-(n : ℝ)/50) := by
  let D : ℝ := 480 / Real.log 2
  have hD : 0 ≤ D := by dsimp [D]; positivity
  filter_upwards [eventually_hall_with_support_log D hD,
      eventually_ge_atTop 1] with n hn hn1
  intro R a T Cold hN ha hTa hret
  have hsupport : 2*a+4*T ≤ 3*a := by omega
  have hdec := decoration_le_rpow_support n Cold (3*a) hn1
    (by omega : Cold≤4*(3*a))
  have hdec' : (((2*n+2)^(20*Cold) : ℕ) : ℝ) ≤
      (2 : ℝ)^(D*(a : ℝ)*Real.log ((n : ℝ)+2)) := by
    convert hdec using 1 <;> push_cast <;> dsimp [D] <;> ring
  have hphysical := BinaryCarrierParameterProfiles.card_div_benchmark_le_weightedSum R a T
  have hweighted := BinaryCarrierHallProfiles.weightedSum_div_le R a T
  have hraw := hphysical.trans hweighted
  rw [← hN] at hraw
  have hmul := mul_le_mul hdec' hraw
    (by exact div_nonneg (Nat.cast_nonneg _) (exactBenchmark_pos _).le)
    (by positivity)
  rw [← hN]
  apply hmul.trans
  have h := hn R R a (7*T) T hN le_rfl ha le_rfl hTa
  have hpowers :
      (2 : ℝ)^(hallQuadratic R a (7*T)) /
          (2 : ℝ)^((n : ℝ)^2/4-1/4) =
        (2 : ℝ)^(1/4 : ℝ) *
          (2 : ℝ)^(hallQuadratic R a (7*T)-(n : ℝ)^2/4) := by
    rw [← Real.rpow_sub (by norm_num : (0 : ℝ) < 2),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  calc
    _ = (Real.exp 13 * 2 * (eulerProduct⁻¹)^6) *
        hallPolynomial R R a (7*T) * (2*(n : ℝ))^(2*a+4*T) *
        ((2 : ℝ)^(hallQuadratic R a (7*T)) /
          (2 : ℝ)^((n : ℝ)^2/4-1/4)) *
        (2 : ℝ)^(D*(a : ℝ)*Real.log ((n : ℝ)+2)) := by
      simp only [BinaryCarrierHallProfiles.modelUpper, div_eq_mul_inv, mul_inv_rev]
      ring
    _ = (Real.exp 13 * 2 * (eulerProduct⁻¹)^6 * (2 : ℝ)^(1/4 : ℝ)) *
        hallPolynomial R R a (7*T) * (2*(n : ℝ))^(2*a+4*T) *
        (2 : ℝ)^(hallQuadratic R a (7*T)-(n : ℝ)^2/4) *
        (2 : ℝ)^(D*(a : ℝ)*Real.log ((n : ℝ)+2)) := by
      rw [hpowers]
      ring
    _ ≤ _ := h

/-- Pointwise large-carrier bin estimate after paying the full retained S16
decoration. -/
theorem eventually_reserve_bin_decoration :
    ∀ᶠ n : ℕ in atTop, ∀ R a T Cold : ℕ,
      R+2*a+4*T=n → a<140*T →
      Real.sqrt (n : ℝ)/4 < (2*a+4*T : ℕ) → Cold≤4*(2*a+4*T) →
      (((2*n+2)^(20*Cold) : ℕ) : ℝ) *
        ((Nat.card (BinaryCarrierParameterProfiles.PhysicalFamily R a T (Fin (2*n))) : ℝ) /
          exactBenchmark (2*n)) ≤
        (2 : ℝ)^(-(29/1490432)*(n : ℝ)) := by
  let D : ℝ := 160 / Real.log 2
  let K := BinaryCarrierReserveEnvelope.constant 12
  have hKD : 0 ≤ K+D := add_nonneg
    (BinaryCarrierReserveEnvelope.constant_nonneg 12) (by dsimp [D]; positivity)
  filter_upwards [eventually_normalized_carrier_with_gaussian_lower
      eulerProduct euler_positive 0 (K+D) hKD,
      eventually_ge_atTop 1] with n hn hn1
  intro R a T Cold hN ha hcut hret
  have hsupport : 2*a+4*T≤n := by omega
  have hdec := decoration_le_rpow_support n Cold n hn1
    (hret.trans (Nat.mul_le_mul_left 4 hsupport))
  have hdec' : (((2*n+2)^(20*Cold) : ℕ) : ℝ) ≤
      (2 : ℝ)^(D*(n : ℝ)*Real.log ((n : ℝ)+2)) := by
    simpa only [D] using hdec
  have hraw := BinaryCarrierReserveProfiles.card_div_benchmark_le_envelope
    R a T (by omega : 1≤R+2*a+4*T)
  rw [hN] at hraw
  have hmul := mul_le_mul hdec' hraw
    (by exact div_nonneg (Nat.cast_nonneg _) (exactBenchmark_pos _).le)
    (by positivity)
  apply hmul.trans
  have h := hn R a T hN.symm ha hcut
  simp only [pow_zero, mul_one] at h
  calc
    _ = Real.exp 13 * (2*(n : ℝ))^(2*a+4*T) *
        (2 : ℝ)^((n : ℝ)^2/4-(29/656)*(T : ℝ)*(n : ℝ)+
          (K+D)*(n : ℝ)*Real.log ((n : ℝ)+2)) /
          (eulerProduct*(2 : ℝ)^((n : ℝ)^2/4-1/4)) := by
      simp only [BinaryCarrierReserveProfiles.envelope]
      rw [show (2 : ℝ)^(D*(n : ℝ)*Real.log ((n : ℝ)+2)) *
          (Real.exp 13 * (2*(n : ℝ))^(2*a+4*T) *
            (2 : ℝ)^((n : ℝ)^2/4-(29/656)*(T : ℝ)*(n : ℝ)+
              BinaryCarrierReserveEnvelope.constant 12*(n : ℝ)*Real.log ((n : ℝ)+2)) /
              (eulerProduct*(2 : ℝ)^((n : ℝ)^2/4-1/4))) =
          Real.exp 13 * (2*(n : ℝ))^(2*a+4*T) *
            ((2 : ℝ)^(D*(n : ℝ)*Real.log ((n : ℝ)+2)) *
              (2 : ℝ)^((n : ℝ)^2/4-(29/656)*(T : ℝ)*(n : ℝ)+
                BinaryCarrierReserveEnvelope.constant 12*(n : ℝ)*Real.log ((n : ℝ)+2))) /
              (eulerProduct*(2 : ℝ)^((n : ℝ)^2/4-1/4)) by ring]
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      dsimp [K]
      ring
    _ ≤ _ := h

end SymmetricSubgroupAsymptotics.BinaryS16DecorationNumerics
