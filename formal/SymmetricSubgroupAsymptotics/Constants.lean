import SymmetricSubgroupAsymptotics.Statements

/-!
# Convergence and positivity of the elementary constants

The Euler product is the exponential of a convergent sum of logarithms.
Both theta series are dominated, on each half of the integers, by a
geometric series. Consequently every residue constant and elementary
benchmark in the approved statement is strictly positive.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace SymmetricSubgroupAsymptotics

private theorem two_rpow_neg_nat (n : ℕ) :
    (2 : ℝ) ^ (-(n : ℝ)) = (1 / 2 : ℝ) ^ n := by
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
  simp [one_div, inv_pow]

private theorem geometric_summable : Summable (fun n : ℕ ↦ (1 / 2 : ℝ) ^ n) :=
  summable_geometric_of_lt_one (by norm_num) (by norm_num)

private theorem euler_tail_summable :
    Summable (fun k : ℕ ↦ (2 : ℝ) ^ (-((k : ℝ) + 1))) := by
  have h := geometric_summable.mul_left (1 / 2 : ℝ)
  refine h.congr fun k ↦ ?_
  rw [show -((k : ℝ) + 1) = -(k : ℝ) + (-1) by ring,
    Real.rpow_add (by norm_num : (0 : ℝ) < 2), two_rpow_neg_nat]
  norm_num
  ring

theorem eulerFactor_pos (k : ℕ) : 0 < eulerFactor k := by
  unfold eulerFactor
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h := Real.rpow_lt_one_of_one_lt_of_neg (x := (2 : ℝ))
    (by norm_num) (show -((k : ℝ) + 1) < 0 by linarith)
  linarith

theorem euler_log_summable : Summable (fun k : ℕ ↦ Real.log (eulerFactor k)) := by
  simpa only [eulerFactor, sub_eq_add_neg] using
    Real.summable_log_one_add_of_summable euler_tail_summable.neg

theorem euler_multipliable : Multipliable eulerFactor :=
  Real.multipliable_of_summable_log eulerFactor_pos euler_log_summable

theorem euler_positive : 0 < eulerProduct := by
  unfold eulerProduct
  rw [← Real.rexp_tsum_eq_tprod eulerFactor_pos euler_log_summable]
  exact Real.exp_pos _

private theorem two_rpow_one_sub_nat (n : ℕ) :
    (2 : ℝ) ^ (1 - (n : ℝ)) = 2 * (1 / 2 : ℝ) ^ n := by
  rw [sub_eq_add_neg, Real.rpow_add (by norm_num : (0 : ℝ) < 2),
    Real.rpow_one, two_rpow_neg_nat]

theorem thetaEvenTerm_pos (j : ℤ) : 0 < thetaEvenTerm j := by
  exact Real.rpow_pos_of_pos (by norm_num) _

theorem thetaOddTerm_pos (j : ℤ) : 0 < thetaOddTerm j := by
  exact Real.rpow_pos_of_pos (by norm_num) _

private theorem theta_even_nat_summable : Summable (fun n : ℕ ↦ thetaEvenTerm n) := by
  refine (geometric_summable.mul_left 2).of_nonneg_of_le
    (fun n ↦ (thetaEvenTerm_pos n).le) fun n ↦ ?_
  rw [← two_rpow_one_sub_nat]
  unfold thetaEvenTerm
  push_cast
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
  nlinarith [sq_nonneg ((n : ℝ) - 1)]

theorem theta_even_summable : Summable thetaEvenTerm := by
  apply theta_even_nat_summable.of_nat_of_neg
  simpa only [thetaEvenTerm, Int.cast_neg, even_two, Even.neg_pow] using
    theta_even_nat_summable

private theorem theta_odd_nat_summable : Summable (fun n : ℕ ↦ thetaOddTerm n) := by
  refine (geometric_summable.mul_left 2).of_nonneg_of_le
    (fun n ↦ (thetaOddTerm_pos n).le) fun n ↦ ?_
  rw [← two_rpow_one_sub_nat]
  unfold thetaOddTerm
  push_cast
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
  nlinarith [sq_nonneg ((n : ℝ) - 1)]

theorem theta_odd_summable : Summable thetaOddTerm := by
  apply theta_odd_nat_summable.of_nat_of_neg
  refine geometric_summable.of_nonneg_of_le
    (fun n ↦ (thetaOddTerm_pos (-(n : ℤ))).le) fun n ↦ ?_
  rw [← two_rpow_neg_nat]
  unfold thetaOddTerm
  push_cast
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
  nlinarith [sq_nonneg (n : ℝ)]

theorem kappaEven_pos : 0 < kappaEven := by
  unfold kappaEven
  exact mul_pos (inv_pos.mpr euler_positive)
    (theta_even_summable.tsum_pos (fun j ↦ (thetaEvenTerm_pos j).le) 0
      (thetaEvenTerm_pos 0))

theorem kappaOdd_pos : 0 < kappaOdd := by
  unfold kappaOdd
  exact mul_pos (inv_pos.mpr euler_positive)
    (theta_odd_summable.tsum_pos (fun j ↦ (thetaOddTerm_pos j).le) 0
      (thetaOddTerm_pos 0))

theorem residue_positive (j : ℕ) : 0 < residueConstant j := by
  unfold residueConstant
  split <;> positivity [kappaEven_pos, kappaOdd_pos]

theorem elementary_positive (n : ℕ) : 0 < elementaryBenchmark n := by
  unfold elementaryBenchmark
  split_ifs with hn
  · norm_num
  · have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hc := residue_positive n
    positivity

end SymmetricSubgroupAsymptotics
