import SymmetricSubgroupAsymptotics.CFSGSymplecticOriginalPositiveRootImages
import Mathlib.Tactic.IntervalCases

/-! The literal path sign is retained: unsigned negative adjoint paths
acquire (-1)^sum(k) under transpose. The actual candidate definition
contains this sign, so its realized image is the bare transpose only
AFTER both signs cancel. No false Lie-transpose automorphism is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSignedPathImages
open CFSG.Models.Chevalley CFSGSerreDiagram CFSGSymplecticSerreMatrices
open CFSGSymplecticOriginalRootCandidates CFSGSymplecticOriginalPositiveRootImages
variable (r : ℕ)

private theorem operator_transpose (E X : Mat ℤ r) (k : ℕ) :
    CFSGIntegralSquareZeroOperators.operator ℤ E.transpose k X.transpose=
      ((-1:ℤ)^k) • (CFSGIntegralSquareZeroOperators.operator ℤ E k X).transpose := by
  by_cases hk : 3≤k
  · rw [CFSGIntegralSquareZeroOperators.operator_large ℤ _ _ _ hk,
      CFSGIntegralSquareZeroOperators.operator_large ℤ _ _ _ hk]
    simp
  · have hlt : k<3:=by omega
    interval_cases k
    · simp only [CFSGIntegralSquareZeroOperators.operator_zero,pow_zero,one_smul]
    · simp only [CFSGIntegralSquareZeroOperators.operator_one,pow_one,neg_one_smul,
        Matrix.transpose_sub,Matrix.transpose_mul]
      abel
    · simp only [CFSGIntegralSquareZeroOperators.operator_two,Matrix.transpose_neg,
        Matrix.transpose_mul]
      simp only [neg_sq,one_pow,one_smul]
      rw [mul_assoc]

theorem matrixSteps_smul (neg : Bool) (ss : List (Fin r×ℕ)) (a : ℤ) (X : Mat ℤ r) :
    matrixSteps r neg ss (a • X)=a • matrixSteps r neg ss X := by
  induction ss generalizing X with
  | nil => rfl
  | cons s ss ih =>
    simp only [matrixSteps,map_smul,ih]

theorem matrixSteps_negative (ss : List (Fin r×ℕ)) (X : Mat ℤ r) :
    matrixSteps r true ss X.transpose=
      ((-1:ℤ)^(ss.map Prod.snd).sum) • (matrixSteps r false ss X).transpose := by
  induction ss generalizing X with
  | nil => simp only [matrixSteps,List.map_nil,List.sum_nil,pow_zero,one_smul]
  | cons s ss ih =>
    change matrixSteps r true ss
      (CFSGIntegralSquareZeroOperators.operator ℤ (positive ℤ r s.1).transpose s.2 X.transpose)=_
    rw [operator_transpose,matrixSteps_smul,ih]
    simp only [List.map_cons,List.sum_cons,pow_add,smul_smul]
    rfl

theorem generator_F_image (i : Fin r) :
    integralSymplecticRepresentation r
      (latticeGenerator (CartanMatrix.C r).transpose (.F i))=negative ℤ r i := by
  apply intMatrixLinearMap_injective r
  rw [integralSymplecticRepresentation_cast]
  change rationalSymplecticRepresentation r
    (generator (CartanMatrix.C r).transpose (.F i)) =
      (Int.castRingHom ℚ).mapMatrix (negative ℤ r i)
  rw [rationalSymplecticRepresentation_F,map_negative]

theorem path_negative_image (start : Fin r) (ss : List (Fin r×ℕ)) :
    integralSymplecticRepresentation r (path r true start ss)=
      (integralSymplecticRepresentation r (path r false start ss)).transpose := by
  simp only [path,map_smul,Bool.false_eq_true,if_false,if_true,one_smul,
    CFSGSerreDividedPowerPaths.pathVector,applySteps_image,
    generator_E_image,generator_F_image,negative]
  rw [matrixSteps_negative,smul_smul,←mul_pow]
  norm_num

theorem difference_negative_image (ij : Pair r) :
    integralSymplecticRepresentation r (difference r true ij)=
      (CFSGSymplecticUniformRootMatrixArithmetic.difference ℤ r ij.val.1 ij.val.2).transpose := by
  unfold difference
  rw [path_negative_image]
  exact congrArg Matrix.transpose (difference_image r ij)

theorem long_negative_image (i : Fin r) :
    integralSymplecticRepresentation r (long r true i)=
      (CFSGSymplecticUniformRootMatrixArithmetic.long ℤ r i).transpose := by
  unfold long
  rw [path_negative_image]
  exact congrArg Matrix.transpose (long_image r i)

theorem sum_negative_image (ij : Pair r) :
    integralSymplecticRepresentation r (sumRoot r true ij)=
      (CFSGSymplecticUniformRootMatrixArithmetic.sumRoot ℤ r ij.val.1 ij.val.2).transpose := by
  unfold sumRoot
  rw [path_negative_image]
  exact congrArg Matrix.transpose (sum_image r ij)

end SymmetricSubgroupAsymptotics.CFSGSymplecticSignedPathImages
