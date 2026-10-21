import SymmetricSubgroupAsymptotics.SemisimpleCompressionWithMargin

/-! The existing outer-factor allowance has room for an additional fixed
factor2^24 at widths at least six. This is used for the actual automorphism
coefficient of the residual order-eight quotient, not for a normal-menu
multiplicity. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
namespace SemisimpleOuterSmallMultiplierAllowance

variable {w : ℕ} {U : Subgroup (Equiv.Perm (Fin w))}
    {E : Subgroup U} [E.Normal] (C : SemisimpleNormalChart E)

def coefficient (b : ℕ) : ℝ := C.outerFactor (Real.logb 2 (Nat.factorial b))

theorem coefficient_nonneg (b : ℕ) : 0 ≤ coefficient C b :=
  C.outerFactor_nonneg (Real.logb_nonneg (by norm_num)
    (by exact_mod_cast Nat.factorial_pos b))

theorem outer_le_coefficient (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))) :
    C.outerFactor (Real.logb 2 (Nat.card J)) ≤ coefficient C b := by
  have hlog : Real.logb 2 (Nat.card J) ≤ Real.logb 2 (Nat.factorial b) := by
    apply Real.logb_le_logb_of_le (by norm_num)
      (by exact_mod_cast Nat.card_pos)
    have hcard := Nat.card_le_card_of_injective
      (Subtype.val : J → Equiv.Perm (Fin b)) Subtype.val_injective
    rw [Nat.card_perm,Nat.card_fin] at hcard
    exact_mod_cast hcard
  unfold coefficient SemisimpleNormalChart.outerFactor
  apply Finset.prod_le_prod
  · intro k _
    exact add_nonneg zero_le_one (C.factorWeight_nonneg
      (Real.logb_nonneg (by norm_num) (by exact_mod_cast Nat.card_pos)) k)
  · intro k _
    simpa only [add_comm] using add_le_add_left (C.factorWeight_mono hlog k) 1

private theorem logb_sq_le_four_log_sq (x : ℝ) :
    (Real.logb 2 x)^2 ≤ 4*(Real.log x)^2 := by
  have hlog : (1/2 : ℝ) < Real.log 2 :=
    lt_trans (by norm_num) Real.log_two_gt_d9
  have hlogsq : (1/4 : ℝ) ≤ (Real.log 2)^2 := by nlinarith
  have hden : 0 < (Real.log 2)^2 := sq_pos_of_pos (lt_trans (by norm_num) hlog)
  unfold Real.logb
  rw [div_pow]
  apply (div_le_iff₀ hden).2
  nlinarith [sq_nonneg (Real.log x)]

theorem multiplier_coefficient_bound (hw : 6 ≤ w)
    (hOuter : SemisimpleOuterFactorPermutationBound) {a : ℝ}
    (ha24 : a ≤ (2 : ℝ)^(24 : ℝ)) (b : ℕ) :
    a * coefficient C b ≤
      (2 : ℝ)^(16*(w : ℝ)*Real.log ((w+b+2 : ℕ) : ℝ)^2) := by
  let x : ℝ := ((w+b+2 : ℕ) : ℝ)
  have hsource := hOuter w U E C b
  have hs := logb_sq_le_four_log_sq x
  have hC : coefficient C b ≤ (2 : ℝ)^(12*(w : ℝ)*(Real.log x)^2) := by
    apply hsource.trans
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hw0 : (0 : ℝ) ≤ w := by positivity
    have hm := mul_le_mul_of_nonneg_left hs
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hw0)
    nlinarith
  have hx4 : (4 : ℝ) ≤ x := by dsimp [x]; exact_mod_cast (show 4 ≤ w+b+2 by omega)
  have hlog4 : (1 : ℝ) < Real.log 4 := by
    have hlog := Real.log_two_gt_d9
    have he : Real.log 4 = 2*Real.log 2 := by
      rw [show (4 : ℝ) = 2^(2 : ℕ) by norm_num,Real.log_pow]
      norm_num
    linarith
  have hl : (1 : ℝ) ≤ Real.log x := hlog4.le.trans
    (Real.log_le_log (by norm_num) hx4)
  have hlsq : (1 : ℝ) ≤ (Real.log x)^2 := by nlinarith
  have hwR : (6 : ℝ) ≤ w := by exact_mod_cast hw
  have he : (24 : ℝ)+12*(w : ℝ)*(Real.log x)^2 ≤
      16*(w : ℝ)*(Real.log x)^2 := by
    nlinarith [mul_le_mul_of_nonneg_left hlsq (show (0 : ℝ) ≤ w by positivity)]
  calc
    a*coefficient C b ≤ (2 : ℝ)^(24 : ℝ)*(2 : ℝ)^(12*(w : ℝ)*(Real.log x)^2) :=
      mul_le_mul ha24 hC (coefficient_nonneg C b) (by positivity)
    _ = (2 : ℝ)^((24 : ℝ)+12*(w : ℝ)*(Real.log x)^2) :=
      (Real.rpow_add (by norm_num : (0 : ℝ) < 2) _ _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) he

end SemisimpleOuterSmallMultiplierAllowance
end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu
