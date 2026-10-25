import SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleNormalizers
import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalHigherCollecting

/-! A selected literal collecting certificate for the endpoint axes.
The cubic parameter is inherited from the original simple-root relation,
not from an assumed two-dimensional representation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleShortAxisConjugation
open CFSGGTwoOriginalPositiveRootWords CFSGGTwoOriginalPositiveCollecting
open CFSGGTwoOriginalHigherCollecting CFSGGTwoCharacteristicThreeMiddleNormalizers
open CFSGGTwoCharacteristicThreeMiddleFiveCoordinates
variable (K : Type) [Field K] [CharP K 3]

private theorem positive_short_inv (a : K) :
    positiveModel K 0 (-a) = (positiveModel K 0 a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [positiveModel_add,add_neg_cancel,positiveModel_zero]

theorem short_conjugate_first (a b : K) :
    positiveModel K 0 a*positiveModel K 1 b*(positiveModel K 0 a)⁻¹ =
      middleWord K ![b,a*b,-a^2*b,a^3*b,-a^3*b^2] := by
  have h := simple_collecting K (-a) b
  have h2 : -(-a)*b = a*b := by ring
  have h3 : -(-a)^2*b = -a^2*b := by ring
  have h4 : -(-a)^3*b = a^3*b := by ring
  have h5 : (-a)^3*b^2 = -a^3*b^2 := by ring
  rw [h2,h3,h4,h5] at h
  have hc : positiveModel K 1 b*positiveModel K 0 (-a) =
      positiveModel K 0 (-a)*middleWord K ![b,a*b,-a^2*b,a^3*b,-a^3*b^2] := by
    simpa only [middleWord_factors,mul_assoc] using h
  rw [positive_short_inv] at hc
  calc
    _ = positiveModel K 0 a*(positiveModel K 1 b*(positiveModel K 0 a)⁻¹) := by group
    _ = positiveModel K 0 a*((positiveModel K 0 a)⁻¹*
        middleWord K ![b,a*b,-a^2*b,a^3*b,-a^3*b^2]) := by rw [hc]
    _ = _ := by group

theorem short_conjugate_second (a b : K) :
    positiveModel K 0 a*positiveModel K 4 b*(positiveModel K 0 a)⁻¹ =
      positiveModel K 4 b := by
  have hc : positiveModel K 4 b*positiveModel K 0 a =
      positiveModel K 0 a*positiveModel K 4 b := (pair_commute K 3 b a).eq
  exact mul_inv_eq_iff_eq_mul.mpr hc.symm

end SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleShortAxisConjugation
