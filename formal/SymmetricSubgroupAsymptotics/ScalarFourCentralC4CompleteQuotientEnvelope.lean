import SymmetricSubgroupAsymptotics.ScalarFourCentralC4CompleteQuotientBudget
import SymmetricSubgroupAsymptotics.ScalarFourCentralCompleteQuotientBudget

/-! The complete original quotient sum has fixed constants small enough for
the width-sixteen residual bridge. No literal normal axis is removed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.ScalarFourCentralC4TopCoordinates
open Non2UnipotentPrefixFiniteMenu
variable {Q T : Type} [Group Q] [Group T] [Finite Q] [Finite T] {c d : ℕ}
  (D : ScalarFourCentralC4TopCoordinates Q T c d)

include D

theorem complete_quotient_envelope_of_menu
    (f : T →* Equiv.Perm (Fin 3)) (hf : Function.Injective f)
    (hc : c≤3) (hd : d≤3)
    (hmenu : ∀ (N : Subgroup Q) [N.Normal],
      (∃ c' d' : ℕ, c'≤c ∧ d'≤d ∧
        Nonempty (ScalarFourCentralC4TopCoordinates (Q ⧸ N) T c' d')) ∨
      (IsPGroup 2 (Q ⧸ N) ∧ Nat.card (Q ⧸ N)≤2^7))
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (b : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)), completeQuotientWeight (R := Q) J) ≤
      (2 : ℝ)^(512 : ℕ)*(2 : ℝ)^((381/192 : ℝ)*(b : ℝ))*(subgroupCount b : ℝ)+
        BinaryKernelRankTailNumerics.raw ((2 : ℝ)^(256 : ℕ)) 7 b+
        MarkedC4KernelRankTailNumerics.raw ((2 : ℝ)^(256 : ℕ)) 22 b := by
  have hsum := complete_quotient_sum_of_menu f hf hc hd hmenu hZmud lit 16
    (D.order_le_sixteen f hf hc hd) b
  have hn : (Nat.card {N : Subgroup Q // N.Normal} : ℝ)≤(2 : ℝ)^(256 : ℕ) := by
    exact_mod_cast D.normal_count_le f hf hc hd
  have ha : (2 : ℝ)^(coldSlope*b)≤(2 : ℝ)^((381/192 : ℝ)*(b : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ)≤2)
      (mul_le_mul_of_nonneg_right (show coldSlope≤(381/192 : ℝ) from ScalarFourCentralTopCoordinates.coldSlope_le_common) (by positivity))
  have hz : (2 : ℝ)^((357/200 : ℝ)*(b : ℝ))≤(2 : ℝ)^((381/192 : ℝ)*(b : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ)≤2)
      (mul_le_mul_of_nonneg_right (by norm_num : (357/200 : ℝ)≤381/192) (by positivity))
  have hAa : menuColdCoefficient T 16*(2 : ℝ)^(coldSlope*b)≤
      (2 : ℝ)^(128 : ℕ)*(2 : ℝ)^((381/192 : ℝ)*(b : ℝ)) :=
    mul_le_mul (menuColdCoefficient_sixteen_le f hf) ha (by positivity) (by positivity)
  have hcold : (Nat.card {N : Subgroup Q // N.Normal} : ℝ)*
      ((subgroupCount b : ℝ)*(menuColdCoefficient T 16*(2 : ℝ)^(coldSlope*b)+
        (2 : ℝ)^((357/200 : ℝ)*(b : ℝ)))) ≤
      (2 : ℝ)^(512 : ℕ)*(2 : ℝ)^((381/192 : ℝ)*(b : ℝ))*(subgroupCount b : ℝ) := by
    calc
      _ ≤ (2 : ℝ)^(256 : ℕ)*((subgroupCount b : ℝ)*
          ((2 : ℝ)^(128 : ℕ)*(2 : ℝ)^((381/192 : ℝ)*(b : ℝ))+
            (2 : ℝ)^((381/192 : ℝ)*(b : ℝ)))) :=
        mul_le_mul hn (mul_le_mul_of_nonneg_left (add_le_add hAa hz) (by positivity))
          (by unfold menuColdCoefficient; positivity) (by positivity)
      _ = ((2 : ℝ)^(256 : ℕ)*((2 : ℝ)^(128 : ℕ)+1))*
          ((2 : ℝ)^((381/192 : ℝ)*(b : ℝ))*(subgroupCount b : ℝ)) := by ring
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
              ((2 : ℝ)^((381/192 : ℝ)*(b : ℝ))*(subgroupCount b : ℝ)) :=
            mul_le_mul_of_nonneg_right hnum (by positivity)
          _ = _ := (mul_assoc _ _ _).symm
  have hmarked : (Nat.card {N : Subgroup Q // N.Normal} : ℝ)*
      MarkedC4KernelRankTailNumerics.raw 1 (16+Nat.card T) b≤
      MarkedC4KernelRankTailNumerics.raw ((2 : ℝ)^(256 : ℕ)) 22 b := by
    have hpow : (b.factorial : ℝ)^(16+Nat.card T)≤(b.factorial : ℝ)^22 := by
      have ht := embedded_top_card_le f hf
      have hnfac : (1 : ℝ)≤(b.factorial : ℝ) := by
        exact_mod_cast (Nat.succ_le_iff.mpr (Nat.factorial_pos b) : 1≤b.factorial)
      exact pow_le_pow_right₀ hnfac (by omega)
    have hr : MarkedC4KernelRankTailNumerics.raw 1 (16+Nat.card T) b≤
        MarkedC4KernelRankTailNumerics.raw 1 22 b := by
      unfold MarkedC4KernelRankTailNumerics.raw
      simp only [one_mul]
      exact mul_le_mul_of_nonneg_right hpow (by unfold markedC4Moment; positivity)
    have hh := mul_le_mul hn hr (by unfold MarkedC4KernelRankTailNumerics.raw markedC4Moment; positivity) (by positivity)
    simpa only [MarkedC4KernelRankTailNumerics.raw,one_mul,mul_assoc] using hh
  have hbinary : (Nat.card {N : Subgroup Q // N.Normal} : ℝ)*
      BinaryKernelRankTailNumerics.raw 1 7 b≤
      BinaryKernelRankTailNumerics.raw ((2 : ℝ)^(256 : ℕ)) 7 b := by
    have hh := mul_le_mul_of_nonneg_right hn
      (show 0≤BinaryKernelRankTailNumerics.raw 1 7 b by
        unfold BinaryKernelRankTailNumerics.raw; positivity)
    simpa only [BinaryKernelRankTailNumerics.raw,one_mul,mul_assoc] using hh
  apply hsum.trans
  rw [mul_add,mul_add]
  have hh := add_le_add (add_le_add hmarked hbinary) hcold
  simpa only [add_assoc,add_comm,add_left_comm] using hh

end SymmetricSubgroupAsymptotics.ScalarFourCentralC4TopCoordinates
