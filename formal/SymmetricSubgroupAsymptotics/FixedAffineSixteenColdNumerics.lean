import SymmetricSubgroupAsymptotics.WidthThirtyTwoBinaryRankTailResidual

/-! Fixed menu coefficients and exact rational margins for the two actual
affine16 exceptional translation cells. No action or subgroup enumeration
is part of these numerical bounds. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
namespace FixedAffineSixteenColdNumerics

theorem two_rpow_twelveThousandFiveHundred_le_menuMass (b : ℕ) :
    (2 : ℝ)^((12500 : ℕ) : ℝ) ≤
      (2 : ℝ)^(16*(64 : ℝ)*Real.log ((64+b+2 : ℕ) : ℝ)^2) := by
  have heq : Real.exp (25 : ℝ)=Real.exp 1^25 := by
    rw [←Real.exp_nat_mul]
    congr 1
    norm_num
  have he : Real.exp (25 : ℝ)<(66 : ℝ)^7 := by
    rw [heq]
    exact (pow_lt_pow_left₀ Real.exp_one_lt_three (Real.exp_pos _).le
      (by decide : 25≠0)).trans (by norm_num)
  have hl := Real.log_lt_log (Real.exp_pos (25 : ℝ)) he
  simp only [Real.log_exp,Real.log_pow,Nat.cast_ofNat] at hl
  have ha : (66 : ℝ)≤((64+b+2 : ℕ) : ℝ) := by
    exact_mod_cast (show 66≤64+b+2 by omega)
  have hm := Real.log_le_log (by norm_num : (0 : ℝ)<66) ha
  have hlog : (25/7 : ℝ)≤Real.log ((64+b+2 : ℕ) : ℝ) := by linarith
  have hs : (625/49 : ℝ)≤Real.log ((64+b+2 : ℕ) : ℝ)^2 := by nlinarith
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  norm_num only [Nat.cast_ofNat]
  nlinarith

theorem parameters_two : PreE7CharacterEntryParameters preE7CharacterRho 32 16
    (51/50) (1/100) (401/200) (121/40) 0 := by
  constructor <;> norm_num [preE7CharacterRho,halfDegree]

theorem parameters_four : PreE7CharacterEntryParameters preE7CharacterRho 64 32
    (51/25) (1/100) (801/200) (1209/200) 0 := by
  constructor <;> norm_num [preE7CharacterRho,halfDegree]

end FixedAffineSixteenColdNumerics
end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
