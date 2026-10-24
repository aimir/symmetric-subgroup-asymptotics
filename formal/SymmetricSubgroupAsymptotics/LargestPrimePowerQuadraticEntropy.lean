import SymmetricSubgroupAsymptotics.LargestPrimePowerEntropy
import SymmetricSubgroupAsymptotics.TraceyQuadraticLcmEntropy

/-! If every actual primary factor is at mostM, the actual degree divides
lcm(1,...,M). The new quadratic entropy then bounds any coprime rate by a
fixed logarithmic fraction. No prime support or action is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.LargestPrimePowerQuadraticEntropy

theorem degree_dvd_lcmUpto (t M : ℕ) (ht : t ≠ 0) (hM : 1 ≤ M)
    (hmax : ∀ p ∈ t.primeFactors, p^t.factorization p ≤ M) :
    t ∣ Nat.lcmUpto M := by
  have hh := TraceyElementarySharperLogBudget.otherPart_dvd_lcmUpto 1 t M ht hM
    (fun p hp _ => hmax p hp)
  simpa only [one_pow,Nat.div_one] using hh

theorem log_le_third_square (t M : ℕ) (ht : t ≠ 0) (hM : 1 ≤ M)
    (hmax : ∀ p ∈ t.primeFactors, p^t.factorization p ≤ M) :
    Real.logb 2 (t : ℝ) ≤ (M : ℝ)^2/3 := by
  have hle := Nat.le_of_dvd (Nat.lcmUpto_pos M) (degree_dvd_lcmUpto t M ht hM hmax)
  have htR : (0 : ℝ) < t := by exact_mod_cast Nat.pos_of_ne_zero ht
  have hleR : (t : ℝ) ≤ (Nat.lcmUpto M : ℝ) := by exact_mod_cast hle
  exact (Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) htR hleR).trans
    (TraceyQuadraticLcmEntropy.log_lcmUpto_le_third_square M)

theorem reciprocal_rate_le_three_fifths (t M : ℕ) (ht : 2 ≤ t) (hM : 1 ≤ M)
    (hmax : ∀ p ∈ t.primeFactors, p^t.factorization p ≤ M) :
    (t : ℝ)/(M : ℝ) ≤ (3/5)*(t : ℝ)/Real.sqrt (Real.logb 2 (t : ℝ)) := by
  have ht0 : t ≠ 0 := by omega
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hL : 0 < Real.logb 2 (t : ℝ) := Real.logb_pos (by norm_num)
    (by exact_mod_cast (show 1 < t by omega))
  have hroot : 0 < Real.sqrt (Real.logb 2 (t : ℝ)) := Real.sqrt_pos.mpr hL
  have hh := log_le_third_square t M ht0 hM hmax
  have hrootBound : Real.sqrt (Real.logb 2 (t : ℝ)) ≤ (3/5)*(M : ℝ) := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity : (0 : ℝ) ≤ (3/5)*(M : ℝ))).mp
    rw [Real.sq_sqrt hL.le,mul_pow]
    nlinarith only [hh,sq_nonneg (M : ℝ)]
  apply (div_le_div_iff₀ hMpos hroot).mpr
  have hm := mul_le_mul_of_nonneg_left hrootBound (show (0 : ℝ) ≤ t by positivity)
  convert hm using 1 <;> ring

end SymmetricSubgroupAsymptotics.LargestPrimePowerQuadraticEntropy
