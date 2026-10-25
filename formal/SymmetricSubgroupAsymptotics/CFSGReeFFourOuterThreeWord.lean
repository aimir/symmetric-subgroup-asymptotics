import SymmetricSubgroupAsymptotics.CFSGReeFFourOuterSignedConjugation
import SymmetricSubgroupAsymptotics.CFSGReeFFourRelativeWeylInvolutions
import SymmetricSubgroupAsymptotics.CFSGReeFFourRelativePositiveSubgroups
import Mathlib.Algebra.CharP.Two

/-! The literal positive outer parameter at one and its actual relative
Weyl element satisfy the order-three product relation. This is transported
from the checked original positive/negative word, not an identification
with a rank-one finite group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOuterThreeWord
open CFSGReeFFourOuterFixedRoot CFSGReeFFourFieldParameters
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourOuterUnipotentGeneration
open CFSGReeFFourOuterSignedConjugation CFSGReeFFourOuterTorusReflection
open CFSGReeFFourRelativePositiveSubgroups CFSGReeFFourRelativeWeylInvolutions

def outerInvolution (m : ℕ) : originalModelFixed m :=
  fixedOuterHom m (Multiplicative.ofAdd 1)

theorem outerInvolution_square (m : ℕ) : (outerInvolution m)^2 = 1 := by
  have hz : (Multiplicative.ofAdd (1 : Field m))^2 = 1 := by
    rw [pow_two]
    change (1 : Field m) + 1 = 0
    exact CharTwo.add_self_eq_zero 1
  calc
    (outerInvolution m)^2 = fixedOuterHom m ((Multiplicative.ofAdd (1 : Field m))^2) :=
      (map_pow (fixedOuterHom m) _ 2).symm
    _ = 1 := by rw [hz, map_one]

theorem outerWeyl_three_word (m : ℕ) :
    outerFixedWeyl m = outerInvolution m *
      (outerFixedWeyl m * outerInvolution m * (outerFixedWeyl m)⁻¹) * outerInvolution m := by
  have hc : outerFixedWeyl m * outerInvolution m * (outerFixedWeyl m)⁻¹ =
      fixedSignedOuter m true 1 := fixed_outer_conjugates_parameter m 1
  calc
    outerFixedWeyl m = fixedOuterWeyl m 1 :=
      Subtype.ext (fixedOuterWeyl_one_val m).symm
    _ = outerInvolution m * fixedSignedOuter m true 1 * outerInvolution m := by
      change fixedSignedOuter m false 1 * fixedSignedOuter m true (-(1 : Field m)⁻¹) *
        fixedSignedOuter m false 1 =
          fixedSignedOuter m false 1 * fixedSignedOuter m true 1 * fixedSignedOuter m false 1
      simp only [inv_one, CharTwo.neg_eq]
    _ = _ := by rw [hc]

private theorem product_cube {G : Type*} [Group G] (x w : G)
    (hw : w⁻¹ = w) (hword : w = x * (w*x*w⁻¹) * x) : (w*x)^3 = 1 := by
  have he : w = x*w*x*w*x := by simpa only [hw, mul_assoc] using hword
  calc
    (w*x)^3 = w*(x*w*x*w*x) := by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = w*w := congrArg (fun z => w*z) he.symm
    _ = w*w⁻¹ := congrArg (fun z => w*z) hw.symm
    _ = 1 := mul_inv_cancel w

theorem outerWeyl_product_cube (m : ℕ) :
    (outerFixedWeyl m * outerInvolution m)^3 = 1 := by
  apply product_cube
  · exact Subtype.ext (outerRelativeWeyl_inv m)
  · exact outerWeyl_three_word m

theorem outerInvolution_conjugates_product_square (m : ℕ) :
    outerInvolution m * (outerFixedWeyl m * outerInvolution m) * (outerInvolution m)⁻¹ =
      (outerFixedWeyl m * outerInvolution m)^2 := by
  have hx : (outerInvolution m)⁻¹ = outerInvolution m :=
    (eq_inv_of_mul_eq_one_left (by simpa only [pow_two] using outerInvolution_square m)).symm
  have hw : (outerFixedWeyl m)⁻¹ = outerFixedWeyl m :=
    Subtype.ext (outerRelativeWeyl_inv m)
  have hr : (outerFixedWeyl m * outerInvolution m)⁻¹ =
      (outerFixedWeyl m * outerInvolution m)^2 := by
    calc
      _ = (outerFixedWeyl m * outerInvolution m)⁻¹ * 1 := by rw [mul_one]
      _ = (outerFixedWeyl m * outerInvolution m)⁻¹ *
          (outerFixedWeyl m * outerInvolution m)^3 := by rw [outerWeyl_product_cube]
      _ = _ := by
        simp only [pow_succ, pow_zero]
        group
  calc
    _ = outerInvolution m * outerFixedWeyl m := by group
    _ = (outerFixedWeyl m * outerInvolution m)⁻¹ := by rw [mul_inv_rev, hx, hw]
    _ = _ := hr

end SymmetricSubgroupAsymptotics.CFSGReeFFourOuterThreeWord
