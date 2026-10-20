import SymmetricSubgroupAsymptotics.ScalarFourCentralSymmetricCompleteQuotientBudget
import SymmetricSubgroupAsymptotics.ScalarFourCentralSymmetricCompleteQuotientSumOfCold

/-! The complete original quotient sum has fixed constants small enough for
the width-twelve residual bridge. No literal normal axis is removed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.ScalarFourCentralTopCoordinates
open Non2UnipotentPrefixFiniteMenu
variable {Q T : Type} [Group Q] [Group T] [Finite Q] [Finite T] {c d : ℕ}
  (D : ScalarFourCentralTopCoordinates Q T c d)

theorem coldSlopeTwo_le_width_twelve : coldSlopeTwo≤(43/30 : ℝ) := by
  have hp : ((5 : ℝ)^3)<(2 : ℝ)^(7 : ℕ) := by norm_num
  have hl := Real.logb_lt_logb (by norm_num : (1 : ℝ)<2)
    (pow_pos (by norm_num) 3) hp
  simp only [Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1 : ℝ)<2),mul_one] at hl
  unfold coldSlopeTwo
  norm_num at hl ⊢
  linarith

theorem symmetric_complete_quotient_envelope_two
    (e : T ≃* Equiv.Perm (Fin 3))
    (hc : c≤2) (hd : d≤2) (hcubic : orderOf D.cubic=3)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (b : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)), completeQuotientWeight (R := Q) J) ≤
      (2 : ℝ)^(512 : ℕ)*(2 : ℝ)^((43/30 : ℝ)*(b : ℝ))*(subgroupCount b : ℝ)+
        BinaryKernelRankTailNumerics.raw ((2 : ℝ)^(256 : ℕ)) 22 b := by
  have hsum := D.symmetric_complete_quotient_summed_count_two e hc hd hcubic hZmud lit 16
    (D.symmetric_order_le_sixteen e (hc.trans (by omega)) (hd.trans (by omega))) b
  have hn : (Nat.card {N : Subgroup Q // N.Normal} : ℝ)≤(2 : ℝ)^(256 : ℕ) := by
    exact_mod_cast D.symmetric_normal_count_le e (hc.trans (by omega)) (hd.trans (by omega))
  have ha : (2 : ℝ)^(coldSlopeTwo*b)≤(2 : ℝ)^((43/30 : ℝ)*(b : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ)≤2)
      (mul_le_mul_of_nonneg_right coldSlopeTwo_le_width_twelve (by positivity))
  have hz : (2 : ℝ)^((51/50 : ℝ)*(b : ℝ))≤(2 : ℝ)^((43/30 : ℝ)*(b : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ)≤2)
      (mul_le_mul_of_nonneg_right (by norm_num : (51/50 : ℝ)≤43/30) (by positivity))
  have hAa : symmetricColdCoefficient T 16*(2 : ℝ)^(coldSlopeTwo*b)≤
      (2 : ℝ)^(128 : ℕ)*(2 : ℝ)^((43/30 : ℝ)*(b : ℝ)) :=
    mul_le_mul (symmetricColdCoefficient_sixteen_le e) ha (by positivity) (by positivity)
  have hcold : (Nat.card {N : Subgroup Q // N.Normal} : ℝ)*
      ((subgroupCount b : ℝ)*(symmetricColdCoefficient T 16*(2 : ℝ)^(coldSlopeTwo*b)+
        (2 : ℝ)^((51/50 : ℝ)*(b : ℝ)))) ≤
      (2 : ℝ)^(512 : ℕ)*(2 : ℝ)^((43/30 : ℝ)*(b : ℝ))*(subgroupCount b : ℝ) := by
    calc
      _ ≤ (2 : ℝ)^(256 : ℕ)*((subgroupCount b : ℝ)*
          ((2 : ℝ)^(128 : ℕ)*(2 : ℝ)^((43/30 : ℝ)*(b : ℝ))+
            (2 : ℝ)^((43/30 : ℝ)*(b : ℝ)))) :=
        mul_le_mul hn (mul_le_mul_of_nonneg_left (add_le_add hAa hz) (by positivity))
          (by unfold symmetricColdCoefficient; positivity) (by positivity)
      _ = ((2 : ℝ)^(256 : ℕ)*((2 : ℝ)^(128 : ℕ)+1))*
          ((2 : ℝ)^((43/30 : ℝ)*(b : ℝ))*(subgroupCount b : ℝ)) := by ring
      _ ≤ _ := by
        have hnum : (2 : ℝ)^(256 : ℕ)*((2 : ℝ)^(128 : ℕ)+1)≤(2 : ℝ)^(512 : ℕ) := by
          calc
            _ ≤ (2 : ℝ)^(256 : ℕ)*((2 : ℝ)^(128 : ℕ)+(2 : ℝ)^(128 : ℕ)) :=
              mul_le_mul_of_nonneg_left
                (add_le_add_right (one_le_pow₀ (by norm_num : (1 : ℝ)≤2)) _) (by positivity)
            _ = (2 : ℝ)^(256 : ℕ)*(2 : ℝ)^(129 : ℕ) := by
              congr 1
              rw [pow_succ' (2 : ℝ) 128]
              ring
            _ = (2 : ℝ)^(385 : ℕ) := by rw [← pow_add]
            _ ≤ (2 : ℝ)^(512 : ℕ) :=
              pow_le_pow_right₀ (by norm_num : (1 : ℝ)≤2) (by omega)
        calc
          _ ≤ (2 : ℝ)^(512 : ℕ)*
              ((2 : ℝ)^((43/30 : ℝ)*(b : ℝ))*(subgroupCount b : ℝ)) :=
            mul_le_mul_of_nonneg_right hnum (by positivity)
          _ = _ := (mul_assoc _ _ _).symm
  have hhot : (Nat.card {N : Subgroup Q // N.Normal} : ℝ)*
      BinaryKernelRankTailNumerics.raw 1 (16+6) b≤
      BinaryKernelRankTailNumerics.raw ((2 : ℝ)^(256 : ℕ)) 22 b := by
    have hh := mul_le_mul_of_nonneg_right hn
      (show 0≤BinaryKernelRankTailNumerics.raw 1 22 b by
        unfold BinaryKernelRankTailNumerics.raw; positivity)
    simpa only [BinaryKernelRankTailNumerics.raw,one_mul,mul_assoc] using hh
  exact hsum.trans (by rw [mul_add,add_comm]; exact add_le_add hcold hhot)

end SymmetricSubgroupAsymptotics.ScalarFourCentralTopCoordinates
