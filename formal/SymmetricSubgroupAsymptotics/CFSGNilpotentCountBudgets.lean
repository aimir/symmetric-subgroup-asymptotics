import SymmetricSubgroupAsymptotics.CFSGOrdinaryBoundedBinaryCount
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! Elementary logarithmic budgets for the genuine bounded nilpotent
counts. The exponent constants depend only on the fixed orbit cutoff. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGNilpotentCountBudgets
open MarkedC4

def degreeLog (b : ℕ) : ℝ := Real.logb 2 ((b : ℝ) + 2)

theorem one_le_degreeLog (b : ℕ) : 1 ≤ degreeLog b := by
  apply (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2)
    (by positivity : (0 : ℝ) < (b : ℝ) + 2)).mpr
  simp only [Real.rpow_one]
  exact le_add_of_nonneg_left (Nat.cast_nonneg b)

theorem degreeLog_mono {a b : ℕ} (h : a ≤ b) : degreeLog a ≤ degreeLog b := by
  apply Real.logb_le_logb_of_le (by norm_num) (by positivity)
  exact_mod_cast Nat.add_le_add_right h 2

theorem power_le_budget (a k b : ℕ) (ha : a ≤ b + 2) :
    (a ^ k : ℝ) ≤ (2 : ℝ) ^ ((k : ℝ) * degreeLog b) := by
  have he : (2 : ℝ) ^ degreeLog b = (b : ℝ) + 2 :=
    Real.rpow_logb (by norm_num) (by norm_num) (by positivity)
  have haR : (a : ℝ) ≤ (b : ℝ) + 2 := by exact_mod_cast ha
  calc
    _ ≤ ((b : ℝ) + 2) ^ k := pow_le_pow_left₀ (Nat.cast_nonneg a) haR k
    _ = ((2 : ℝ) ^ degreeLog b) ^ k := congrArg (fun t : ℝ => t ^ k) he.symm
    _ = _ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring

theorem factorial_le_budget (b : ℕ) :
    (b.factorial : ℝ) ≤ (2 : ℝ) ^ ((b : ℝ) * degreeLog b) := by
  have h : (b.factorial : ℝ) ≤ (b : ℝ) ^ b := by exact_mod_cast b.factorial_le_pow
  exact h.trans (power_le_budget b b b (by omega))

theorem constant_power_le_budget (c b : ℕ) :
    ((c : ℝ) ^ b) ≤ (2 : ℝ) ^ ((c : ℝ) * b * degreeLog b) := by
  have hn : c ≤ 2 ^ c := (Nat.lt_two_pow_self (n := c)).le
  have hc : (c : ℝ) ≤ (2 : ℝ) ^ c := by exact_mod_cast hn
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg c) hc b
  have hpow' : (c : ℝ) ^ b ≤ (2 : ℝ) ^ ((c : ℝ) * b) := by
    calc
      _ ≤ ((2 : ℝ) ^ c) ^ b := hpow
      _ = (2 : ℝ) ^ (c * b) := (pow_mul 2 c b).symm
      _ = (2 : ℝ) ^ ((c * b : ℕ) : ℝ) := (Real.rpow_natCast 2 (c * b)).symm
      _ = _ := by rw [Nat.cast_mul]
  apply hpow'.trans
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  exact le_mul_of_one_le_right (by positivity) (one_le_degreeLog b)

theorem mul_pow2_bounds {x y a b : ℝ} (hxa : x ≤ (2 : ℝ) ^ a)
    (hyb : y ≤ (2 : ℝ) ^ b) (hy : 0 ≤ y) :
    x * y ≤ (2 : ℝ) ^ (a + b) := by
  exact (mul_le_mul hxa hyb hy (Real.rpow_pos_of_pos (by norm_num) a).le).trans_eq
    (Real.rpow_add (by norm_num) a b).symm

theorem zero_family_card_le_one (P : Subgroup (PermutationGroup 0) → Prop) :
    (Nat.card {G // P G} : ℝ) ≤ 1 := by
  exact_mod_cast ((Finite.card_le_one_iff_subsingleton (α := {G // P G})).mpr
    (inferInstance : Subsingleton {G // P G}))

theorem binary_card_le (C b : ℕ) :
    (Nat.card (BoundedNilpotentTargetConvolution.BinaryFamily C b) : ℝ) ≤
      (2 : ℝ) ^ ((b : ℝ) ^ 2 / 16 +
        CFSGOrdinaryBoundedBinaryCount.coefficient C * b * degreeLog b) := by
  by_cases hb : b = 0
  · subst b
    simpa only [Nat.cast_zero, zero_pow (by decide : 2 ≠ 0), zero_div,
      mul_zero, zero_mul, add_zero, Real.rpow_zero] using
      zero_family_card_le_one (fun G => IsPGroup 2 G ∧ OrbitCutoffFamilies.OrbitCutoff C G)
  · exact CFSGOrdinaryBoundedBinaryCount.bounded_binary_card_le C b (by omega)

end SymmetricSubgroupAsymptotics.CFSGNilpotentCountBudgets
