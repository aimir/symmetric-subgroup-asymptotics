import SymmetricSubgroupAsymptotics.CFSGGTwoRootUnits
import Mathlib.Tactic.Abel

/-! Sparse action tests for the long folded root. They prove noncentrality
on the actual matrix image without claiming a scalar natural commutant. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGGTwoSerreMatrices
variable (R : Type*) [CommRing R]

 theorem longWeyl_conjugate_positive :
    (longWeyl R : Mat R)*positive R 1*(↑((longWeyl R)⁻¹):Mat R)= -negative R 1 := by
  rw [longWeyl_val,longWeyl_inv_val]
  simp only [negative,positive_one_explicit,Matrix.transpose_sub,Matrix.transpose_single]
  simp [add_mul,mul_add,sub_mul,mul_sub,pos,neg] <;> abel

 theorem positive_root_fixes_positive :
    (1+positive R 1)*positive R 1*(1-positive R 1)=positive R 1 := by
  have he : positive R 1*positive R 1=0 := by
    simpa only [positiveSecond,if_neg (show (1:Fin 2)≠0 by decide),add_zero] using
      positive_square R 1
  simp only [add_mul,mul_sub,mul_add,sub_mul,one_mul,mul_one,he,zero_mul,add_zero]
  abel

 theorem positive_root_negative_entry :
    ((1+positive R 1)*(-negative R 1)*(1-positive R 1)) (pos 1) (pos 2)=1 := by
  simp only [negative,positive_one_explicit,Matrix.transpose_sub,Matrix.transpose_single]
  simp only [add_mul,mul_add,sub_mul,mul_sub,mul_neg,neg_mul,one_mul,mul_one]
  simp [pos,neg] <;>
    simp [Matrix.single,Matrix.mul_apply,Fintype.sum_sum_type,Fin.sum_univ_succ]

 theorem negative_entry : (-negative R 1) (pos 1) (pos 2)=0 := by
  simp [negative,CFSGOrthogonalDSerreMatrices.positive,pos,neg,Matrix.single]

end SymmetricSubgroupAsymptotics.CFSGGTwoSerreMatrices
