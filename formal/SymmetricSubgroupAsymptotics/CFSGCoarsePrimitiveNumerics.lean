import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

/-! Elementary degree estimates for the actual full-socle bounds.
No primitive classification or simple-group theorem is assumed here. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGCoarsePrimitiveNumerics

theorem logb_nat_le_nat (n : ℕ) : Real.logb 2 n ≤ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    by_cases hn : n = 0
    · subst n; norm_num
    have hp : (0 : ℝ) < n := by exact_mod_cast (Nat.pos_of_ne_zero hn)
    have hineq : (n : ℝ) + 1 ≤ 2 * n := by
      have hnat : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      exact_mod_cast (show n + 1 ≤ 2 * n by omega)
    have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by positivity : (0 : ℝ) < n + 1) hineq
    rw [Real.logb_mul (by norm_num) hp.ne', Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] at hh
    push_cast
    linarith

theorem factorial_logb_le_square (k : ℕ) : Real.logb 2 k.factorial ≤ (k : ℝ)^2 := by
  have hn : k ≤ 2 ^ k := (Nat.lt_two_pow_self (n := k)).le
  have hp : k.factorial ≤ 2 ^ (k * k) :=
    k.factorial_le_pow.trans (by simpa only [pow_mul] using Nat.pow_le_pow_left hn k)
  have hc : (k.factorial : ℝ) ≤ (2 : ℝ) ^ (k * k) := by exact_mod_cast hp
  have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by exact_mod_cast k.factorial_pos) hc
  simpa only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),
    mul_one, Nat.cast_mul, pow_two] using hh

theorem outer_logb_le_twice {ell out : ℕ} (hell : 5 ≤ ell) (houtpos : 0 < out)
    (hout : (out : ℝ) ≤ 3 * Real.logb 2 ell) :
    Real.logb 2 out ≤ 2 * Real.logb 2 ell := by
  have he : (5 : ℝ) ≤ ell := by exact_mod_cast hell
  have hnum : (out : ℝ) ≤ (ell : ℝ)^2 := by nlinarith [logb_nat_le_nat ell]
  have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by exact_mod_cast houtpos) hnum
  simpa only [Real.logb_pow, Nat.cast_ofNat] using hh

theorem socle_coarse_bound {ell out k n : ℕ} {a c : ℝ} (hc : 0 ≤ c)
    (hell : 5 ≤ ell) (houtpos : 0 < out) (hdegree : ell ^ k ≤ n)
    (hout : (out : ℝ) ≤ 3 * Real.logb 2 ell)
    (ha : a ≤ c * k + k * Real.logb 2 out + Real.logb 2 k.factorial) :
    a ≤ (Real.logb 2 n)^2 + (c + 2) * Real.logb 2 n := by
  have he : (2 : ℝ) ≤ ell := by exact_mod_cast (show 2 ≤ ell by omega)
  have ht : 1 ≤ Real.logb 2 ell := by
    have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by norm_num : (0 : ℝ) < 2) he
    simpa only [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using h
  have hp : (ell : ℝ) ^ k ≤ n := by exact_mod_cast hdegree
  have hkt : (k : ℝ) * Real.logb 2 ell ≤ Real.logb 2 n := by
    have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (pow_pos (by linarith : (0 : ℝ) < ell) k) hp
    simpa only [Real.logb_pow] using h
  have hk : (k : ℝ) ≤ Real.logb 2 n := by nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hsq : (k : ℝ)^2 ≤ (Real.logb 2 n)^2 := by nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have ho := mul_le_mul_of_nonneg_left (outer_logb_le_twice hell houtpos hout) (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  have hcm := mul_le_mul_of_nonneg_left hk hc
  nlinarith [factorial_logb_le_square k]

end SymmetricSubgroupAsymptotics.CFSGCoarsePrimitiveNumerics
