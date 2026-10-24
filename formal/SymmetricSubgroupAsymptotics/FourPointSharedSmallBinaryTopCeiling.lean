import SymmetricSubgroupAsymptotics.IntegerLogSquareRootCeilingCertificate
import SymmetricSubgroupAsymptotics.TraceyAffineInducedModuleInput
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FieldSimp

/-! A single small-exponent scalar family for the ACTUAL shared head:
t=3*2^a, 1<=a<=5. Two fixed integer power certificates provide uniform
logarithm brackets; only five small square comparisons remain. These
are arithmetic states, not group or action representatives. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FourPointSharedSmallBinaryTopCeiling
open IntegerLogSquareRootCeilingCertificate

def topCut (a : ℕ) : ℕ :=
  match a with
  | 1 => 4
  | 2 => 7
  | 3 => 12
  | 4 => 21
  | _ => 38

def headCut (a : ℕ) : ℕ := 5*2^(a-1)+3

private theorem lower_power (a : ℕ) : 2^(101+64*a) ≤ (3*2^a)^64 := by
  have hbase : 2^101 ≤ (3 : ℕ)^64 := by decide +kernel
  have hp : (2^a : ℕ)^64 = 2^(64*a) := by rw [← pow_mul,Nat.mul_comm a 64]
  rw [mul_pow,hp,pow_add]
  exact Nat.mul_le_mul_right _ hbase

private theorem upper_power (a : ℕ) : (12*2^a)^64 ≤ 2^(230+64*a) := by
  have hbase : (12 : ℕ)^64 ≤ 2^230 := by decide +kernel
  have hp : (2^a : ℕ)^64 = 2^(64*a) := by rw [← pow_mul,Nat.mul_comm a 64]
  rw [mul_pow,hp,pow_add]
  exact Nat.mul_le_mul_right _ hbase

private theorem top_square (a : ℕ) (ha1 : 1 ≤ a) (ha5 : a ≤ 5) :
    64*(3*2^a)^2 ≤ (101+64*a)*(topCut a)^2 := by
  interval_cases a <;> decide +kernel

private theorem target_square (a : ℕ) (ha1 : 1 ≤ a) (ha5 : a ≤ 5) :
    (headCut a+topCut a-1)^2*(230+64*a) < 64*(12*2^a)^2 := by
  interval_cases a <;> decide +kernel

private theorem real_cost_eq (a : ℕ) (ha : 1 ≤ a) :
    (5/6 : ℝ)*(3*2^a : ℕ)+(3*2^a : ℕ)/(2 : ℝ)^a = (headCut a : ℝ) := by
  have hp : (2 : ℝ)^a = 2*(2 : ℝ)^(a-1) := by
    calc
      (2 : ℝ)^a = (2 : ℝ)^(a-1+1) :=
        congrArg (fun j : ℕ => (2 : ℝ)^j) (Nat.sub_add_cancel ha).symm
      _ = _ := by rw [pow_succ]; ring
  have hunit : (3 : ℝ)*(2 : ℝ)^a/(2 : ℝ)^a = 3 := by field_simp
  push_cast
  rw [hunit]
  simp only [headCut,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  rw [hp]
  ring

theorem aggregate_small (a g : ℕ) (ha1 : 1 ≤ a) (ha5 : a ≤ 5)
    (hcost : (g : ℝ) ≤ (5/6 : ℝ)*(3*2^a : ℕ)+(3*2^a : ℕ)/(2 : ℝ)^a+
      (traceyPermutationGeneratorCeiling (3*2^a) : ℝ)) :
    g ≤ traceyPermutationGeneratorCeiling (12*2^a) := by
  have htop : traceyPermutationGeneratorCeiling (3*2^a) ≤ topCut a := by
    exact ceil_le_of_square (3*2^a) 64 (101+64*a) (topCut a)
      (by positivity) (by decide) (by omega) (lower_power a) (top_square a ha1 ha5)
  have hg : g ≤ headCut a+topCut a := by
    have htopR : (traceyPermutationGeneratorCeiling (3*2^a) : ℝ) ≤ topCut a := by exact_mod_cast htop
    have hcostR : (g : ℝ) ≤ (headCut a : ℝ)+(topCut a : ℝ) := by
      rw [← real_cost_eq a ha1]
      exact hcost.trans (add_le_add le_rfl htopR)
    exact_mod_cast hcostR
  have htarget : headCut a+topCut a ≤ traceyPermutationGeneratorCeiling (12*2^a) := by
    exact le_ceil_of_square (12*2^a) 64 (230+64*a) (headCut a+topCut a)
      (by
        have hh : 0 < 2^a := by positivity
        have hm := Nat.mul_le_mul_left 12 (show 1 ≤ 2^a by omega)
        omega) (by decide)
      (by dsimp only [headCut]; omega) (upper_power a) (target_square a ha1 ha5)
  exact hg.trans htarget

end SymmetricSubgroupAsymptotics.FourPointSharedSmallBinaryTopCeiling
