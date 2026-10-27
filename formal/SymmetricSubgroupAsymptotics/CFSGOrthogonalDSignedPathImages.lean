import SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalPositiveRootImages
import Mathlib.Tactic.Abel

/-! Whole negative-root images for the actual original D lattice. Each
transpose reverses a bracket; the literal path sign cancels the accumulated
sign. No ordinary-transpose Lie homomorphism is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDSignedPathImages
open CFSG.Models.Chevalley CFSGSerreDiagram CFSGOrthogonalDSerreMatrices
open CFSGOrthogonalDOriginalRootCandidates CFSGOrthogonalDOriginalIntegralAction
open CFSGOrthogonalDOriginalPositiveRootImages
variable (r : ℕ) (hr : 4 ≤ r)

def matrixSteps (neg : Bool) : List (Fin r)→Mat ℤ r→Mat ℤ r
  | [],X=>X
  | i::ss,X=>matrixSteps neg ss ⁅rootMatrix ℤ r neg i,X⁆

theorem applySteps_image (neg : Bool) (ss : List (Fin r)) (x : Source r) :
    integralOrthogonalRepresentation r hr
      (CFSGSerreDividedPowerPaths.applySteps (CartanMatrix.D r) neg (steps r ss) x)=
      matrixSteps r neg ss (integralOrthogonalRepresentation r hr x) := by
  induction ss generalizing x with
  | nil => rfl
  | cons i ss ih =>
    simp only [steps,List.map_cons,CFSGSerreDividedPowerPaths.applySteps,matrixSteps]
    change integralOrthogonalRepresentation r hr
      (CFSGSerreDividedPowerPaths.applySteps (CartanMatrix.D r) neg (steps r ss)
        (integralOperator (CartanMatrix.D r) neg i 1 x)) = _
    rw [ih,first_image]

private theorem transpose_bracket (E X : Mat ℤ r) :
    ⁅E.transpose,X.transpose⁆=(-1:ℤ) • ⁅E,X⁆.transpose := by
  simp only [Ring.lie_def,Matrix.transpose_sub,Matrix.transpose_mul,neg_one_smul]
  abel

theorem matrixSteps_smul (neg : Bool) (ss : List (Fin r)) (z : ℤ) (X : Mat ℤ r) :
    matrixSteps r neg ss (z • X)=z • matrixSteps r neg ss X := by
  induction ss generalizing X with
  | nil => rfl
  | cons i ss ih => simp only [matrixSteps,lie_smul,ih]

theorem matrixSteps_negative (ss : List (Fin r)) (X : Mat ℤ r) :
    matrixSteps r true ss X.transpose=
      (-1:ℤ)^ss.length • (matrixSteps r false ss X).transpose := by
  induction ss generalizing X with
  | nil => simp only [matrixSteps,List.length_nil,pow_zero,one_smul]
  | cons i ss ih =>
    change matrixSteps r true ss ⁅(positive ℤ r i).transpose,X.transpose⁆=_
    rw [transpose_bracket,matrixSteps_smul,ih]
    simp only [List.length_cons,pow_succ',smul_smul]
    rfl

theorem path_negative_image (start : Fin r) (ss : List (Fin r)) :
    integralOrthogonalRepresentation r hr (path r true start ss)=
      (integralOrthogonalRepresentation r hr (path r false start ss)).transpose := by
  simp only [path,map_smul,Bool.false_eq_true,if_false,if_true,one_smul,
    CFSGSerreDividedPowerPaths.pathVector,applySteps_image,generator_image,
    integerGenerator,negative]
  rw [matrixSteps_negative,smul_smul,←mul_pow]
  norm_num

theorem difference_negative_image (ij : Pair r) :
    integralOrthogonalRepresentation r hr (difference r true ij)=
      (CFSGOrthogonalDUniformRootMatrixArithmetic.difference ℤ r ij.val.1 ij.val.2).transpose := by
  unfold difference
  rw [path_negative_image]
  exact congrArg Matrix.transpose (difference_image r hr ij)

theorem sum_negative_image (ij : Pair r) :
    integralOrthogonalRepresentation r hr (sumRoot r hr true ij)=
      (CFSGOrthogonalDUniformRootMatrixArithmetic.sumRoot ℤ r ij.val.1 ij.val.2).transpose := by
  unfold sumRoot
  rw [path_negative_image]
  exact congrArg Matrix.transpose (sum_image r hr ij)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDSignedPathImages
