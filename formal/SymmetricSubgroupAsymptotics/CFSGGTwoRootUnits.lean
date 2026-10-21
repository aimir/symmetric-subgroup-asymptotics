import SymmetricSubgroupAsymptotics.CFSGGTwoIntegralRealization
import SymmetricSubgroupAsymptotics.CFSGQuadraticRootExponential
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDMatrixWeylParity

/-! Genuine integral quadratic root units in the folded D4 representation.
The central D4 node gives a literal fourth-root Weyl word. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoSerreMatrices
variable (R : Type*) [CommRing R]

 theorem rootMatrix_square (neg : Bool) (i : Fin 2) :
    rootMatrix R neg i*rootMatrix R neg i=rootSecond R neg i+rootSecond R neg i := by
  cases neg
  · exact positive_square R i
  · exact negative_square R i
 theorem rootMatrix_mul_second (neg : Bool) (i : Fin 2) :
    rootMatrix R neg i*rootSecond R neg i=0 := by
  cases neg
  · exact positive_mul_second R i
  · exact negative_mul_second R i
 theorem rootSecond_mul_matrix (neg : Bool) (i : Fin 2) :
    rootSecond R neg i*rootMatrix R neg i=0 := by
  cases neg
  · exact second_mul_positive R i
  · exact second_mul_negative R i
 theorem rootSecond_square (neg : Bool) (i : Fin 2) :
    rootSecond R neg i*rootSecond R neg i=0 := by
  cases neg
  · exact positiveSecond_sq_zero R i
  · exact negativeSecond_sq_zero R i

 def rootTransvection (neg : Bool) (i : Fin 2) (t : R) : (Mat R)ˣ :=
  CFSGQuadraticRootExponential.rootUnit (rootMatrix R neg i) (rootSecond R neg i)
    (rootMatrix_square R neg i) (rootMatrix_mul_second R neg i)
    (rootSecond_mul_matrix R neg i) (rootSecond_square R neg i) t

@[simp] theorem rootTransvection_val (neg : Bool) (i : Fin 2) (t : R) :
    (rootTransvection R neg i t : Mat R)=1+t • rootMatrix R neg i+t^2 • rootSecond R neg i := rfl
@[simp] theorem rootTransvection_inv_val (neg : Bool) (i : Fin 2) (t : R) :
    (↑((rootTransvection R neg i t)⁻¹):Mat R)=1-t • rootMatrix R neg i+t^2 • rootSecond R neg i :=
  CFSGQuadraticRootExponential.rootUnit_inv_val _ _ _ _ _ _ t

 def longWeyl : (Mat R)ˣ :=
  rootTransvection R false 1 (-1)*rootTransvection R true 1 1*rootTransvection R false 1 (-1)

 theorem longWeyl_val : (longWeyl R : Mat R)=
    (1-positive R 1)*(1+negative R 1)*(1-positive R 1) := by
  simp only [longWeyl,Units.val_mul,rootTransvection_val,rootMatrix,rootSecond,
    Bool.false_eq_true,if_false,if_true,positiveSecond,if_neg (show (1:Fin 2)≠0 by decide),
    negativeSecond,Matrix.transpose_zero,smul_zero,add_zero,neg_one_smul,one_smul,
    ←sub_eq_add_neg]

 theorem longWeyl_inv_val : (↑((longWeyl R)⁻¹):Mat R)=
    (1+positive R 1)*(1-negative R 1)*(1+positive R 1) := by
  simp only [longWeyl,_root_.mul_inv_rev,Units.val_mul,rootTransvection_inv_val,rootMatrix,rootSecond,
    Bool.false_eq_true,if_false,if_true,positiveSecond,if_neg (show (1:Fin 2)≠0 by decide),
    negativeSecond,Matrix.transpose_zero,smul_zero,add_zero,neg_one_smul,one_smul,
    sub_neg_eq_add,mul_assoc]

 theorem longWeyl_four (K : Type) [Field K] : longWeyl K^4=1 := by
  apply Units.ext
  change (longWeyl K : Mat K)^4=1
  rw [longWeyl_val]
  change CFSGOrthogonalDSerreMatrices.chainWeylMatrix K 3 (1:Fin 3)^4=1
  exact CFSGOrthogonalDSerreMatrices.chainWeylMatrix_four K 3 1

end SymmetricSubgroupAsymptotics.CFSGGTwoSerreMatrices
