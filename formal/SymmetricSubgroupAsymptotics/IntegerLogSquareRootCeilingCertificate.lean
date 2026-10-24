import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Convert
import Lean.Elab.Tactic.Omega

/-! Integer-power certificates for logarithmic square-root ceilings.
The scale D is arbitrary: no exponent depending quadratically on the
claimed ceiling is needed. These are universal arithmetic implications,
not supplied estimates for groups, actions or published inputs. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.IntegerLogSquareRootCeilingCertificate

theorem log_lower (n D b : ℕ) (hn : 0 < n) (hD : 0 < D) (hpow : 2^b ≤ n^D) :
    (b : ℝ)/(D : ℝ) ≤ Real.logb 2 (n : ℝ) := by
  have hpowR : (2 : ℝ)^b ≤ (n : ℝ)^D := by exact_mod_cast hpow
  have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by positivity : (0 : ℝ) < (2 : ℝ)^b) hpowR
  simp only [Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),mul_one] at hh
  apply (div_le_iff₀ (by exact_mod_cast hD : (0 : ℝ) < D)).mpr
  simpa only [mul_comm] using hh

theorem log_upper (n D u : ℕ) (hn : 0 < n) (hD : 0 < D) (hpow : n^D ≤ 2^u) :
    Real.logb 2 (n : ℝ) ≤ (u : ℝ)/(D : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpowR : (n : ℝ)^D ≤ (2 : ℝ)^u := by exact_mod_cast hpow
  have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (pow_pos hnR D) hpowR
  simp only [Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),mul_one] at hh
  apply (le_div_iff₀ (by exact_mod_cast hD : (0 : ℝ) < D)).mpr
  simpa only [mul_comm] using hh

theorem ceil_le_of_square (n D b H : ℕ) (hn : 0 < n) (hD : 0 < D) (hb : 0 < b)
    (hpow : 2^b ≤ n^D) (hsquare : D*n^2 ≤ b*H^2) :
    ⌈(n : ℝ)/Real.sqrt (Real.logb 2 (n : ℝ))⌉₊ ≤ H := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hlo := log_lower n D b hn hD hpow
  have hL : 0 < Real.logb 2 (n : ℝ) := (div_pos hbR hDR).trans_le hlo
  have hS : 0 < Real.sqrt (Real.logb 2 (n : ℝ)) := Real.sqrt_pos.mpr hL
  have hsqR : (D : ℝ)*(n : ℝ)^2 ≤ (b : ℝ)*(H : ℝ)^2 := by exact_mod_cast hsquare
  have hfirst : (n : ℝ)^2 ≤ ((b : ℝ)/(D : ℝ))*(H : ℝ)^2 := by
    have hh : (n : ℝ)^2 ≤ (b : ℝ)*(H : ℝ)^2/(D : ℝ) :=
      (le_div_iff₀ hDR).mpr (by nlinarith only [hsqR])
    convert hh using 1 <;> ring
  have hsecond := mul_le_mul_of_nonneg_right hlo (sq_nonneg (H : ℝ))
  have hroot : (n : ℝ)^2 ≤ (H : ℝ)^2*Real.logb 2 (n : ℝ) := by
    simpa only [mul_comm] using hfirst.trans hsecond
  apply Nat.ceil_le.mpr
  apply (div_le_iff₀ hS).mpr
  apply (sq_le_sq₀ hnR.le (mul_nonneg (Nat.cast_nonneg H) hS.le)).mp
  simpa only [mul_pow,Real.sq_sqrt hL.le] using hroot

theorem le_ceil_of_square (n D u K : ℕ) (hn : 2 ≤ n) (hD : 0 < D) (hK : 1 ≤ K)
    (hpow : n^D ≤ 2^u) (hsquare : (K-1)^2*u < D*n^2) :
    K ≤ ⌈(n : ℝ)/Real.sqrt (Real.logb 2 (n : ℝ))⌉₊ := by
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hupper := log_upper n D u hn0 hD hpow
  have hL : 0 < Real.logb 2 (n : ℝ) := Real.logb_pos (by norm_num : (1 : ℝ) < 2)
    (by exact_mod_cast (show 1 < n by omega) : (1 : ℝ) < n)
  have hS : 0 < Real.sqrt (Real.logb 2 (n : ℝ)) := Real.sqrt_pos.mpr hL
  have hsqR : ((K-1 : ℕ) : ℝ)^2*(u : ℝ) < (D : ℝ)*(n : ℝ)^2 := by exact_mod_cast hsquare
  have hfirst : ((K-1 : ℕ) : ℝ)^2*((u : ℝ)/(D : ℝ)) < (n : ℝ)^2 := by
    have hh : ((K-1 : ℕ) : ℝ)^2*(u : ℝ)/(D : ℝ) < (n : ℝ)^2 :=
      (div_lt_iff₀ hDR).mpr (by nlinarith only [hsqR])
    convert hh using 1 <;> ring
  have hsecond := mul_le_mul_of_nonneg_left hupper (sq_nonneg ((K-1 : ℕ) : ℝ))
  have hroot : ((K-1 : ℕ) : ℝ)^2*Real.logb 2 (n : ℝ) < (n : ℝ)^2 := hsecond.trans_lt hfirst
  have hlt : ((K-1 : ℕ) : ℝ) < (n : ℝ)/Real.sqrt (Real.logb 2 (n : ℝ)) := by
    apply (lt_div_iff₀ hS).mpr
    apply (sq_lt_sq₀ (mul_nonneg (Nat.cast_nonneg _) hS.le) hnR.le).mp
    simpa only [mul_pow,Real.sq_sqrt hL.le] using hroot
  have hh := Nat.add_one_le_ceil_iff.mpr hlt
  simpa only [Nat.sub_add_cancel hK] using hh

end SymmetricSubgroupAsymptotics.IntegerLogSquareRootCeilingCertificate
