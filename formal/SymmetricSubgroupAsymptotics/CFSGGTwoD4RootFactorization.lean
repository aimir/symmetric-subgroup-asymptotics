import SymmetricSubgroupAsymptotics.CFSGGTwoRootUnits
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDElementaryGroup
import Mathlib.Tactic.Module

/-! The actual quadratic short-root unit is the product of the three
outer D4 root units. Its cross term is retained over every commutative
ring, so this comparison does not invert 2 or 3. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4RootFactorization
open CFSGGTwoSerreMatrices
variable (R : Type*) [CommRing R]

private theorem outer_zero_two :
    CFSGOrthogonalDSerreMatrices.positive R 4 0 *
      CFSGOrthogonalDSerreMatrices.positive R 4 2 = 0 := by
  simp [CFSGOrthogonalDSerreMatrices.positive, sub_mul, mul_sub]

private theorem outer_zero_three :
    CFSGOrthogonalDSerreMatrices.positive R 4 0 *
      CFSGOrthogonalDSerreMatrices.positive R 4 3 = 0 := by
  simp [CFSGOrthogonalDSerreMatrices.positive, CFSGOrthogonalDSerreMatrices.previous,
    sub_mul, mul_sub]

theorem outer_two_three :
    CFSGOrthogonalDSerreMatrices.positive R 4 2 *
      CFSGOrthogonalDSerreMatrices.positive R 4 3 = positiveSecond R 0 := by
  simp [CFSGOrthogonalDSerreMatrices.positive, CFSGOrthogonalDSerreMatrices.previous,
    positiveSecond, pos, neg, sub_mul, mul_sub]
  ext x y
  simp only [Matrix.neg_apply, Matrix.single_apply]
  split_ifs <;> simp

theorem positive_outer_factor (t : R) :
    rootTransvection R false 0 t =
      CFSGOrthogonalDSerreMatrices.rootTransvection R 4 false 0 t *
        CFSGOrthogonalDSerreMatrices.rootTransvection R 4 false 2 t *
          CFSGOrthogonalDSerreMatrices.rootTransvection R 4 false 3 t := by
  apply Units.ext
  simp only [Units.val_mul, rootTransvection_val, rootMatrix, rootSecond,
    CFSGOrthogonalDSerreMatrices.rootTransvection_val,
    CFSGOrthogonalDSerreMatrices.rootMatrix, Bool.false_eq_true, if_false,
    positive_zero, outerPositive]
  simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
    smul_smul, outer_zero_two, outer_zero_three, outer_two_three, smul_zero,
    add_zero, smul_add]
  module

theorem positive_central_factor (t : R) :
    rootTransvection R false 1 t =
      CFSGOrthogonalDSerreMatrices.rootTransvection R 4 false 1 t := by
  apply Units.ext
  simp only [rootTransvection_val, rootMatrix, rootSecond,
    CFSGOrthogonalDSerreMatrices.rootTransvection_val,
    CFSGOrthogonalDSerreMatrices.rootMatrix, Bool.false_eq_true, if_false,
    positive_one, positiveSecond, if_neg (show (1 : Fin 2) ≠ 0 by decide),
    smul_zero, add_zero]

theorem negative_outer_factor (t : R) :
    rootTransvection R true 0 t =
      CFSGOrthogonalDSerreMatrices.rootTransvection R 4 true 3 t *
        CFSGOrthogonalDSerreMatrices.rootTransvection R 4 true 2 t *
          CFSGOrthogonalDSerreMatrices.rootTransvection R 4 true 0 t := by
  apply Units.ext
  have h := congrArg Matrix.transpose (congrArg (fun u : (Mat R)ˣ => (u : Mat R))
    (positive_outer_factor R t))
  simpa only [Units.val_mul, rootTransvection_val, rootMatrix, rootSecond,
    CFSGOrthogonalDSerreMatrices.rootTransvection_val,
    CFSGOrthogonalDSerreMatrices.rootMatrix, Bool.false_eq_true, if_false, if_true,
    negative, negativeSecond, CFSGOrthogonalDSerreMatrices.negative,
    Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one,
    Matrix.transpose_mul, mul_assoc] using h

theorem negative_central_factor (t : R) :
    rootTransvection R true 1 t =
      CFSGOrthogonalDSerreMatrices.rootTransvection R 4 true 1 t := by
  apply Units.ext
  simp only [rootTransvection_val, rootMatrix, rootSecond,
    CFSGOrthogonalDSerreMatrices.rootTransvection_val,
    CFSGOrthogonalDSerreMatrices.rootMatrix, if_true, negative, negativeSecond,
    CFSGOrthogonalDSerreMatrices.negative, positive_one,
    positiveSecond, if_neg (show (1 : Fin 2) ≠ 0 by decide),
    Matrix.transpose_zero, smul_zero, add_zero]

end SymmetricSubgroupAsymptotics.CFSGGTwoD4RootFactorization
