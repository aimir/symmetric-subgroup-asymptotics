import SymmetricSubgroupAsymptotics.ScalarFourCentralCompleteQuotientBudget

/-! The complete original quotient sum has fixed constants small enough for
the width-sixteen residual bridge. No literal normal axis is removed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.ScalarFourCentralTopCoordinates
open Non2UnipotentPrefixFiniteMenu
variable {Q : Type} [Group Q] [Finite Q] {c d : ℕ}
  (D : ScalarFourCentralTopCoordinates Q CyclicThree c d)

theorem complete_quotient_envelope
    (hc : c≤3) (hd : d≤3) (hcubic : D.cubic=Multiplicative.ofAdd (1 : ZMod 3))
    (f : CyclicThree →* Equiv.Perm (Fin 3)) (hf : Function.Injective f)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (b : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)), completeQuotientWeight (R := Q) J) ≤
      (2 : ℝ)^(512 : ℕ)*(2 : ℝ)^((381/192 : ℝ)*(b : ℝ))*(subgroupCount b : ℝ)+
        BinaryKernelRankTailNumerics.raw ((2 : ℝ)^(256 : ℕ)) 19 b := by
  have hsum := D.complete_quotient_summed_count hc hd hcubic f hf hZmud lit 16
    (D.order_le_sixteen hc hd) b
  have hn : (Nat.card {N : Subgroup Q // N.Normal} : ℝ)≤(2 : ℝ)^(256 : ℕ) := by
    exact_mod_cast D.normal_count_le hc hd
  have ha : (2 : ℝ)^(coldSlope*b)≤(2 : ℝ)^((381/192 : ℝ)*(b : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ)≤2)
      (mul_le_mul_of_nonneg_right coldSlope_le_common (by positivity))
  have hz : (2 : ℝ)^((3/2 : ℝ)*(b : ℝ))≤(2 : ℝ)^((381/192 : ℝ)*(b : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ)≤2)
      (mul_le_mul_of_nonneg_right (by norm_num : (3/2 : ℝ)≤381/192) (by positivity))
  have hAa : cubicColdCoefficient 16*(2 : ℝ)^(coldSlope*b)≤
      (2 : ℝ)^(64 : ℕ)*(2 : ℝ)^((381/192 : ℝ)*(b : ℝ)) :=
    mul_le_mul cubicColdCoefficient_sixteen_le ha (by positivity) (by positivity)
  have hcold : (Nat.card {N : Subgroup Q // N.Normal} : ℝ)*
      ((subgroupCount b : ℝ)*(cubicColdCoefficient 16*(2 : ℝ)^(coldSlope*b)+
        (2 : ℝ)^((3/2 : ℝ)*(b : ℝ)))) ≤
      (2 : ℝ)^(512 : ℕ)*(2 : ℝ)^((381/192 : ℝ)*(b : ℝ))*(subgroupCount b : ℝ) := by
    calc
      _ ≤ (2 : ℝ)^(256 : ℕ)*((subgroupCount b : ℝ)*
          ((2 : ℝ)^(64 : ℕ)*(2 : ℝ)^((381/192 : ℝ)*(b : ℝ))+
            (2 : ℝ)^((381/192 : ℝ)*(b : ℝ)))) :=
        mul_le_mul hn (mul_le_mul_of_nonneg_left (add_le_add hAa hz) (by positivity))
          (by unfold cubicColdCoefficient; positivity) (by positivity)
      _ = ((2 : ℝ)^(256 : ℕ)*((2 : ℝ)^(64 : ℕ)+1))*
          ((2 : ℝ)^((381/192 : ℝ)*(b : ℝ))*(subgroupCount b : ℝ)) := by ring
      _ ≤ _ := by
        have hnum : (2 : ℝ)^(256 : ℕ)*((2 : ℝ)^(64 : ℕ)+1)≤(2 : ℝ)^(512 : ℕ) := by
          calc
            _ ≤ (2 : ℝ)^(256 : ℕ)*((2 : ℝ)^(64 : ℕ)+(2 : ℝ)^(64 : ℕ)) :=
              mul_le_mul_of_nonneg_left
                (add_le_add_right (one_le_pow₀ (by norm_num : (1 : ℝ)≤2)) _) (by positivity)
            _ = (2 : ℝ)^(256 : ℕ)*(2 : ℝ)^(65 : ℕ) := by
              congr 1
              rw [pow_succ' (2 : ℝ) 64]
              ring
            _ = (2 : ℝ)^(321 : ℕ) := by rw [← pow_add]
            _ ≤ (2 : ℝ)^(512 : ℕ) :=
              pow_le_pow_right₀ (by norm_num : (1 : ℝ)≤2) (by omega)
        calc
          _ ≤ (2 : ℝ)^(512 : ℕ)*
              ((2 : ℝ)^((381/192 : ℝ)*(b : ℝ))*(subgroupCount b : ℝ)) :=
            mul_le_mul_of_nonneg_right hnum (by positivity)
          _ = _ := (mul_assoc _ _ _).symm
  have hhot : (Nat.card {N : Subgroup Q // N.Normal} : ℝ)*
      BinaryKernelRankTailNumerics.raw 1 (16+3) b≤
      BinaryKernelRankTailNumerics.raw ((2 : ℝ)^(256 : ℕ)) 19 b := by
    have hh := mul_le_mul_of_nonneg_right hn
      (show 0≤BinaryKernelRankTailNumerics.raw 1 19 b by
        unfold BinaryKernelRankTailNumerics.raw; positivity)
    simpa only [BinaryKernelRankTailNumerics.raw,one_mul,mul_assoc] using hh
  exact hsum.trans (by rw [mul_add,add_comm]; exact add_le_add hcold hhot)

end SymmetricSubgroupAsymptotics.ScalarFourCentralTopCoordinates
