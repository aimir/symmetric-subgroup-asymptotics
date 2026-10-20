import SymmetricSubgroupAsymptotics.LargeOrbitGeneratorConsequencesWeighted

/-! A literal integer power-of-two cutoff for the proved orbit weight. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.LargeOrbitGeneratorConsequences

theorem exists_orbitWeight_cutoff (rate : ℝ) (hrate : 0 < rate) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ n : ℕ, C ≤ n →
      128 * orbitWeight n ≤ rate * n := by
  obtain ⟨k, hk⟩ := exists_nat_ge (max (1 : ℝ) ((128 / rate) ^ 2))
  have hk1 : (1 : ℝ) ≤ k := (le_max_left _ _).trans hk
  have hksq : (128 / rate) ^ 2 ≤ (k : ℝ) := (le_max_right _ _).trans hk
  have hkN : 1 ≤ k := by exact_mod_cast hk1
  let C := 2 ^ k
  have hC : 2 ≤ C := by
    have h := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hkN
    simpa only [pow_one, C] using h
  refine ⟨C, hC, ?_⟩
  intro n hn
  have hCn : (C : ℝ) ≤ n := by exact_mod_cast hn
  have hCpos : (0 : ℝ) < C := by exact_mod_cast (show 0 < C by omega)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlogC : Real.logb 2 (C : ℝ) = k := by
    dsimp [C]
    rw [Nat.cast_pow, Real.logb_pow]
    simp only [Nat.cast_ofNat,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one]
  have hklog : (k : ℝ) ≤ Real.logb 2 n := by
    rw [← hlogC]
    exact (Real.logb_le_logb (by norm_num) hCpos hnpos).mpr hCn
  have hlogpos : 0 < Real.logb 2 n := by linarith
  have hsqrt : 0 < Real.sqrt (Real.logb 2 n) := Real.sqrt_pos.mpr hlogpos
  have hroot : 128 / rate ≤ Real.sqrt (Real.logb 2 n) :=
    Real.le_sqrt_of_sq_le (hksq.trans hklog)
  have hRate : 128 ≤ rate * Real.sqrt (Real.logb 2 n) := by
    simpa only [mul_comm] using (div_le_iff₀ hrate).mp hroot
  unfold orbitWeight
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hsqrt).mpr
  nlinarith [mul_le_mul_of_nonneg_right hRate (Nat.cast_nonneg n)]

end SymmetricSubgroupAsymptotics.LargeOrbitGeneratorConsequences
