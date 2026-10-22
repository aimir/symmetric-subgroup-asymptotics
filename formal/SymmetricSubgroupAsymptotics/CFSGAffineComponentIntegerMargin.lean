import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveGenericMargin
import SymmetricSubgroupAsymptotics.CFSGAffineChiefAbelianOrderBudget

/-! An integer chief-charge margin for the original component tower.
The slightly sharper rational gamma bound makes the raw full affine order
at degree27 sufficient, avoiding another small structural classification. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics

theorem fixedTargetCompositionGamma_lt_fiftyThree_hundred :
    fixedTargetCompositionGamma < (53 : ℝ)/100 := by
  have hp : (3 : ℝ)^(100:ℕ) < (2 : ℝ)^(159:ℕ) := by norm_num
  have hl := Real.logb_lt_logb (by norm_num : (1:ℝ)<2) (by positivity : (0:ℝ)<3^(100:ℕ)) hp
  simp only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1:ℝ)<2), mul_one] at hl
  norm_num only [Nat.cast_ofNat] at hl
  unfold fixedTargetCompositionGamma
  nlinarith

namespace Non2UnipotentPrefixFiniteMenu

theorem primitiveAffine_margin_of_integer_charge (r s w c : ℕ)
    (hs : 2 ≤ s) (hw : w = r*s)
    (hbudget : 54272*c+38400 ≤ 25575*r)
    (eta : ℝ) (heta : eta ≤ fixedTargetCompositionGamma * ((s:ℝ)/2) * c) :
    preE7CharacterRho*w ≤ ((evenWidth w:ℝ)-s)/8-eta := by
  have hg := fixedTargetCompositionGamma_lt_fiftyThree_hundred.le
  have hcap : eta ≤ (53/200:ℝ)*c*s := by
    calc
      eta ≤ fixedTargetCompositionGamma * ((s:ℝ)/2) * c := heta
      _ ≤ (53/100:ℝ)*((s:ℝ)/2)*c :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hg (by positivity)) (by positivity)
      _ = _ := by ring
  have hb : (54272:ℝ)*c+38400 ≤ 25575*r := by exact_mod_cast hbudget
  have hgap : (53/200:ℝ)*c + preE7CharacterRho*r + 1/16 ≤ ((r:ℝ)-1)/8 := by
    unfold preE7CharacterRho
    linarith
  have hm := mul_le_mul_of_nonneg_right hgap (show (0:ℝ)≤(s:ℝ) by positivity)
  have hpar : (w:ℝ) ≤ evenWidth w+1 := by exact_mod_cast width_le_evenWidth_add_one w
  have hs' : (2:ℝ) ≤ s := by exact_mod_cast hs
  have hw' : (w:ℝ) = r*s := by exact_mod_cast hw
  nlinarith

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics
