import SymmetricSubgroupAsymptotics.MarkedC4HistoryMenuError

/-! The finite physical word alphabet and original point labels are paid
once. Their scalar cost has a negligible exponent; no subgroup count or
marked moment is a premise. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.MarkedC4.SkeletonMenuError

def letters (C : ℕ) : ℝ := (max C 1 : ℕ)*(2 : ℝ)^C.factorial

def cost (C b : ℕ) : ℝ :=
  (b.factorial : ℝ)*((b : ℝ)+1)*(max C 1 : ℕ)^b*((2 : ℝ)^C.factorial)^b

def coefficient (C : ℕ) : ℝ := 2+Real.logb 2 (letters C)

theorem letters_one_le (C : ℕ) : 1 ≤ letters C := by
  have hc : (1 : ℝ) ≤ (max C 1 : ℕ) := by exact_mod_cast le_max_right C 1
  have hp : (1 : ℝ) ≤ (2 : ℝ)^C.factorial := one_le_pow₀ (by norm_num)
  exact (by norm_num : (1 : ℝ) = 1*1).trans_le (mul_le_mul hc hp (by norm_num) (by positivity))

theorem coefficient_nonneg (C : ℕ) : 0 ≤ coefficient C := by
  have hl := Real.logb_nonneg (by norm_num : (1 : ℝ)<2) (letters_one_le C)
  unfold coefficient
  linarith

theorem cost_le_power (C b r : ℕ) (hb : 1 ≤ b) :
    cost C b ≤ ((b : ℝ)+r+2)^(coefficient C*b) := by
  let s : ℝ := (b : ℝ)+r+2
  let a : ℝ := Real.logb 2 (letters C)
  have hs2 : 2 ≤ s := by
    dsimp [s]
    linarith [Nat.cast_nonneg (α := ℝ) b,Nat.cast_nonneg (α := ℝ) r]
  have hs : 1 ≤ s := by linarith
  have hs0 : 0<s := by linarith
  have ha : 0 ≤ a := Real.logb_nonneg (by norm_num) (letters_one_le C)
  have hfac : (b.factorial : ℝ) ≤ s^b := by
    calc
      _ ≤ (b : ℝ)^b := by exact_mod_cast Nat.factorial_le_pow b
      _ ≤ s^b := pow_le_pow_left₀ (Nat.cast_nonneg _) (by
        dsimp [s]
        linarith [Nat.cast_nonneg (α := ℝ) r]) _
  have hb1 : (b : ℝ)+1 ≤ s^b := by
    calc
      _ ≤ s := by dsimp [s]; linarith [Nat.cast_nonneg (α := ℝ) r]
      _ = s^1 := (pow_one s).symm
      _ ≤ s^b := pow_le_pow_right₀ hs hb
  have hl : letters C ≤ s^a := by
    calc
      _ = (2 : ℝ)^a := (Real.rpow_logb (by norm_num) (by norm_num)
        (show 0<letters C from lt_of_lt_of_le (by norm_num) (letters_one_le C))).symm
      _ ≤ s^a := Real.rpow_le_rpow (by norm_num) hs2 ha
  have hlpow : (letters C)^b ≤ s^(a*b) := by
    calc
      _ ≤ (s^a)^b := pow_le_pow_left₀ ((by norm_num : (0 : ℝ) ≤ 1).trans (letters_one_le C)) hl _
      _ = s^(a*b) := by rw [← Real.rpow_natCast,← Real.rpow_mul hs0.le]
  have hcost : cost C b = (b.factorial : ℝ)*((b : ℝ)+1)*(letters C)^b := by
    unfold cost letters
    rw [mul_pow]
    ring
  have hletters0 : 0 ≤ letters C := (by norm_num : (0 : ℝ) ≤ 1).trans (letters_one_le C)
  rw [hcost]
  calc
    _ ≤ s^b*s^b*s^(a*b) := mul_le_mul
      (mul_le_mul hfac hb1 (by positivity) (by positivity)) hlpow (pow_nonneg hletters0 _) (by positivity)
    _ = s^(coefficient C*b) := by
      simp only [← Real.rpow_natCast]
      rw [← Real.rpow_add hs0,← Real.rpow_add hs0]
      congr 1
      dsimp [coefficient,a]
      ring

theorem cost_le_error (C b r : ℕ) (hb : 1 ≤ b) :
    cost C b ≤ (2 : ℝ)^boundedWordError (coefficient C) b r := by
  apply (cost_le_power C b r hb).trans
  have hd : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hl : 0 ≤ Real.log ((b : ℝ)+r+2) := Real.log_nonneg (by
    linarith [Nat.cast_nonneg (α := ℝ) b,Nat.cast_nonneg (α := ℝ) r])
  apply (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ)<2) (by positivity)).mp
  rw [Real.logb,Real.log_rpow (by positivity)]
  apply (div_le_iff₀ hd).mpr
  unfold boundedWordError
  field_simp
  nlinarith [Nat.cast_nonneg (α := ℝ) b]

theorem negligible (C : ℕ) :
    UniformQuadraticNegligible (boundedWordError (coefficient C)) :=
  boundedWordError_negligible (coefficient_nonneg C)

end SymmetricSubgroupAsymptotics.MarkedC4.SkeletonMenuError
end
