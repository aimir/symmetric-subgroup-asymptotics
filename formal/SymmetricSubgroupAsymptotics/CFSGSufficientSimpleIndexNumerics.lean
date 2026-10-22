import SymmetricSubgroupAsymptotics.PrimitiveOuterOrderNumerics
import SymmetricSubgroupAsymptotics.CFSGCoarsePrimitiveNumerics
import SymmetricSubgroupAsymptotics.GrowingComparatorPadding
import Mathlib.Data.Nat.Factorization.Basic

/-! Exact sufficient primitive numerics with coefficient six. The original
compression margins, ternary weights and relative-head targets are unchanged.
Only the large-degree cutoff moves to64. No simple-group assertion is an
assumption of this file. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSufficientSimpleIndexNumerics

theorem twoPow_le_sixthPower {ell q : ℕ} (hell : 0 < ell)
    (hq : (q : ℝ) ≤ 6 * Real.logb 2 ell) : 2 ^ q ≤ ell ^ 6 := by
  have hq' : (q : ℝ) ≤ Real.logb 2 ((ell : ℝ) ^ 6) := by
    simpa only [Real.logb_pow] using hq
  have hp := (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2)
    (pow_pos (by exact_mod_cast hell) 6)).mp hq'
  rw [Real.rpow_natCast] at hp
  exact_mod_cast hp

theorem square_bound {ell q : ℕ} (hell : 27 ≤ ell)
    (hq : (q : ℝ) ≤ 6 * Real.logb 2 ell) : 4 * q ≤ ell ^ 2 := by
  have hl := CFSGCoarsePrimitiveNumerics.logb_nat_le_nat ell
  have he : (27 : ℝ) ≤ ell := by exact_mod_cast hell
  have hp : 0 ≤ (ell : ℝ) * ((ell : ℝ) - 24) :=
    mul_nonneg (by linarith) (by linarith)
  have hreal : (4 : ℝ) * q ≤ (ell : ℝ) ^ 2 := by
    nlinarith
  exact_mod_cast hreal

private theorem nine_succ_le_two_pow (k : ℕ) (hk : 6 ≤ k) :
    9 * (k + 1) ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
      calc
        9 * (k + 1 + 1) ≤ 2 * (9 * (k + 1)) := by omega
        _ ≤ 2 * 2 ^ k := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (k + 1) := by rw [pow_succ]; ring

theorem twoThirds_tail {r q : ℕ} (hr : 64 ≤ r)
    (hq : (q : ℝ) ≤ 6 * Real.logb 2 r) : 3 * q ≤ 2 * r := by
  let k := Nat.log 2 r
  have hr0 : r ≠ 0 := by omega
  have hk : 6 ≤ k :=
    (Nat.le_log_iff_pow_le (by decide : 1 < 2) hr0).mpr (by norm_num; omega)
  have hlo : 2 ^ k ≤ r := Nat.pow_log_le_self 2 hr0
  have hhi : r < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by decide : 1 < 2) r
  have hp : (r : ℝ) < (2 : ℝ) ^ (k + 1) := by exact_mod_cast hhi
  have hl := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
    (by exact_mod_cast (show 0 < r by omega)) hp
  simp only [Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at hl
  have hqR : (3 : ℝ) * q < 18 * ((k + 1 : ℕ) : ℝ) := by nlinarith
  have hqN : 3 * q < 18 * (k + 1) := by exact_mod_cast hqR
  have hdyadic : 18 * (k + 1) ≤ 2 * 2 ^ k := by
    have h := Nat.mul_le_mul_left 2 (nine_succ_le_two_pow k hk)
    nlinarith
  omega

private theorem rounding_receipt :
    ∀ r : Fin 64, 30 ≤ r.val → r.val ^ 6 < 2 ^ evenWidth r.val := by
  decide +kernel

theorem rounding_gap_thirtyToSixtyThree {r q : ℕ}
    (hr : 30 ≤ r) (h63 : r ≤ 63)
    (hq : (q : ℝ) ≤ 6 * Real.logb 2 r) :
    max 2 q + 1 ≤ evenWidth r := by
  have hp := (twoPow_le_sixthPower (by omega) hq).trans_lt
    (rounding_receipt ⟨r, by omega⟩ hr)
  change (2 : ℕ) ^ q < 2 ^ evenWidth r at hp
  have hlt : q < evenWidth r := by
    by_contra h
    have hpow := pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ))
      (show evenWidth r ≤ q by omega)
    exact (not_lt_of_ge hpow) hp
  have he := width_le_evenWidth_add_one r
  omega

theorem rounding_gap_of_le_twentyFour {r q : ℕ}
    (hr : 27 ≤ r) (hq : q ≤ 24) : max 2 q + 1 ≤ evenWidth r := by
  have he := width_le_evenWidth_add_one r
  omega

private theorem ternary_receipt : ∀ q : Fin 33, q.val.factorization 3 ≤ 3 := by
  decide +kernel

theorem ternaryValuation_le_three {r q : ℕ}
    (hr : 27 ≤ r) (h44 : r ≤ 44)
    (hq : (q : ℝ) ≤ 6 * Real.logb 2 r) : q.factorization 3 ≤ 3 := by
  have hp : 2 ^ q < 2 ^ 33 := calc
    2 ^ q ≤ r ^ 6 := twoPow_le_sixthPower (by omega) hq
    _ ≤ 44 ^ 6 := Nat.pow_le_pow_left h44 6
    _ < 2 ^ 33 := by decide
  have hq33 : q < 33 := by
    by_contra h
    have hpow := pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (show 33 ≤ q by omega)
    omega
  exact ternary_receipt ⟨q, hq33⟩

theorem threeTenths_weight {r q w : ℕ}
    (hr : 27 ≤ r) (h44 : r ≤ 44)
    (hq : (q : ℝ) ≤ 6 * Real.logb 2 r) (hw : w ≤ q.factorization 3) :
    10 * w ≤ 3 * r := by
  have hv := ternaryValuation_le_three hr h44 hq
  omega

theorem strict_relative_head {r q w : ℕ}
    (hr : 27 ≤ r) (h33 : r ≤ 33)
    (hq : (q : ℝ) ≤ 6 * Real.logb 2 r) (hw : w ≤ q.factorization 3) :
    20 * w < 3 * r := by
  have hv := ternaryValuation_le_three hr (by omega) hq
  omega

end SymmetricSubgroupAsymptotics.CFSGSufficientSimpleIndexNumerics
