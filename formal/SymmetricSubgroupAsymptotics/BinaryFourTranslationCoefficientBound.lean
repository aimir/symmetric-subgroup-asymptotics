import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveCoefficient

/-! The existing joint translation coefficient fits the unchanged generic
affine width cost at localdegree16. Its capacity uses the logarithmic
ceiling even when the strict margin uses a different refined field. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

theorem binary_four_translation_coefficient_exponent_le_widthCost
    (s w b : ℕ) (hs : 2 ≤ s) (hw : w=16*s) :
    (traceyAffineCoefficientExponent 4 s (traceyInducedGeneratorCeiling 4 s)
      (traceyPermutationGeneratorCeiling w) w 2 : ℝ) ≤ affineComponentWidthCost w+8*(w : ℝ)*Real.logb 2 (b+1) := by
  have hh := traceyAffineCoefficientExponent_log_le 4 s
    (traceyPermutationGeneratorCeiling w) w 2 Nat.prime_two hs
  norm_num only [Nat.cast_ofNat] at hh
  rw [Real.logb_self_eq_one (by norm_num : (1 : ℝ)<2)] at hh
  simp only [one_mul,Nat.cast_ofNat,mul_one] at hh
  have hA : 0 ≤ 4*(s : ℝ)^2/Real.sqrt (Real.logb 2 s) := by positivity
  have hB : 0 ≤ 4*(s : ℝ)*w/Real.sqrt (Real.logb 2 s)+
      s*(traceyPermutationGeneratorCeiling w+2)+w := by positivity
  have hlog : 0 ≤ Real.logb 2 (b+1) :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast (show 1 ≤ b+1 by omega))
  have hbound :
      (traceyAffineCoefficientExponent 4 s (traceyInducedGeneratorCeiling 4 s)
        (traceyPermutationGeneratorCeiling w) w 2 : ℝ) ≤ affineComponentCoefficientExponent 16 s w b := by
    unfold affineComponentCoefficientExponent
    norm_num only [show Nat.log 2 16=4 by decide,Nat.reduceAdd,Nat.reducePow,Nat.cast_ofNat]
    nlinarith [mul_nonneg (Nat.cast_nonneg s) hlog]
  exact hbound.trans (affineComponentCoefficientExponent_le_widthCost 16 s w b
    (by decide) hs hw)

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
