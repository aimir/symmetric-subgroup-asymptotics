import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalBasisMatrixPilot
import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalFourteenFamily

/-! Sparse integral matrix images for the original divided-power G2
basis family. Coefficients two and three are evaluated integrally first;
rational cancellation is used only to identify rational vector images. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoOriginalBasisMatrices
open CFSGGTwoOriginalBasisMatrixPilot CFSGGTwoOriginalPositiveSerreStrings
open CFSGGTwoSerreMatrices CFSG.Models.Chevalley
variable (R : Type*) [CommRing R]

def secondMatrix : Mat R :=
  -Matrix.single (pos 0) (pos 3) 1 - Matrix.single (pos 0) (neg 3) 1 -
    Matrix.single (pos 1) (neg 2) 1 + Matrix.single (pos 2) (neg 1) 1 +
      Matrix.single (pos 3) (neg 0) 1 + Matrix.single (neg 3) (neg 0) 1

def thirdMatrix : Mat R :=
  -Matrix.single (pos 0) (neg 2) 1 + Matrix.single (pos 2) (neg 0) 1

def highestMatrix : Mat R :=
  -Matrix.single (pos 0) (neg 1) 1 + Matrix.single (pos 1) (neg 0) 1

theorem second_bracket : ⁅positive R 0,firstMatrix R⁆=(2:R) • secondMatrix R := by
  rw [Ring.lie_def,positive_zero_explicit]
  simp only [firstMatrix,add_mul,sub_mul,mul_add,mul_sub]
  simp [pos,neg,Matrix.single_mul_single_same,Matrix.single_mul_single_of_ne,
    secondMatrix,Matrix.smul_apply]
  ext i j
  simp only [Matrix.add_apply,Matrix.neg_apply,Matrix.sub_apply,
    Matrix.smul_apply,smul_eq_mul,Matrix.single_apply]
  split_ifs <;> ring

theorem third_bracket : ⁅positive R 0,secondMatrix R⁆=(3:R) • thirdMatrix R := by
  rw [Ring.lie_def,positive_zero_explicit]
  simp only [secondMatrix,add_mul,sub_mul,mul_add,mul_sub,neg_mul,mul_neg]
  simp [pos,neg,Matrix.single_mul_single_same,Matrix.single_mul_single_of_ne,
    thirdMatrix,Matrix.smul_apply]
  ext i j
  simp only [Matrix.add_apply,Matrix.neg_apply,Matrix.sub_apply,
    Matrix.smul_apply,smul_eq_mul,Matrix.single_apply]
  split_ifs <;> ring

theorem highest_bracket : ⁅positive R 1,thirdMatrix R⁆=highestMatrix R := by
  rw [Ring.lie_def,positive_one_explicit]
  simp only [thirdMatrix,add_mul,sub_mul,mul_add,mul_sub,neg_mul,mul_neg]
  simp [pos,neg,Matrix.single_mul_single_same,Matrix.single_mul_single_of_ne,highestMatrix]
  abel

theorem transpose_lie (X Y:Mat R) : ⁅X.transpose,Y.transpose⁆= -(⁅X,Y⁆).transpose := by
  simp only [Ring.lie_def,Matrix.transpose_sub,Matrix.transpose_mul]
  abel

theorem rationalRepresentation_second :
    rationalRepresentation (stringVector false 2)=secondMatrix ℚ := by
  have he := congrArg rationalRepresentation (short_string_one false)
  rw [LieHom.map_lie,map_smul,rationalRepresentation_first] at he
  simp only [shortVector,rootVector,Bool.false_eq_true,if_false,rationalRepresentation_E] at he
  change ⁅positive ℚ 0,firstMatrix ℚ⁆=(2:ℚ) • rationalRepresentation (stringVector false 2) at he
  rw [second_bracket] at he
  exact smul_right_injective (Mat ℚ) (by norm_num : (2:ℚ)≠0) he.symm

theorem rationalRepresentation_third :
    rationalRepresentation (stringVector false 3)=thirdMatrix ℚ := by
  have he := congrArg rationalRepresentation (short_string_two false)
  rw [LieHom.map_lie,map_smul,rationalRepresentation_second] at he
  simp only [shortVector,rootVector,Bool.false_eq_true,if_false,rationalRepresentation_E] at he
  change ⁅positive ℚ 0,secondMatrix ℚ⁆=(3:ℚ) • rationalRepresentation (stringVector false 3) at he
  rw [third_bracket] at he
  exact smul_right_injective (Mat ℚ) (by norm_num : (3:ℚ)≠0) he.symm

theorem rationalRepresentation_highest : rationalRepresentation (highestVector false)=highestMatrix ℚ := by
  rw [highestVector,LieHom.map_lie,rationalRepresentation_third]
  simp only [longVector,rootVector,Bool.false_eq_true,if_false,rationalRepresentation_E]
  change ⁅positive ℚ 1,thirdMatrix ℚ⁆=highestMatrix ℚ
  exact highest_bracket ℚ

theorem rationalRepresentation_negative_first :
    rationalRepresentation (stringVector true 1)= -(firstMatrix ℚ).transpose := by
  rw [string_one,LieHom.map_lie]
  simp only [shortVector,longVector,rootVector,if_true,rationalRepresentation_F,negative]
  change ⁅(positive ℚ 0).transpose,(positive ℚ 1).transpose⁆= -(firstMatrix ℚ).transpose
  rw [transpose_lie,first_bracket]

theorem rationalRepresentation_negative_second :
    rationalRepresentation (stringVector true 2)=(secondMatrix ℚ).transpose := by
  have he := congrArg rationalRepresentation (short_string_one true)
  rw [LieHom.map_lie,map_smul,rationalRepresentation_negative_first] at he
  simp only [shortVector,rootVector,if_true,rationalRepresentation_F,negative] at he
  change ⁅(positive ℚ 0).transpose,-(firstMatrix ℚ).transpose⁆=
    (2:ℚ) • rationalRepresentation (stringVector true 2) at he
  rw [lie_neg,transpose_lie,second_bracket,Matrix.transpose_smul,neg_neg] at he
  exact smul_right_injective (Mat ℚ) (by norm_num : (2:ℚ)≠0) he.symm

theorem rationalRepresentation_negative_third :
    rationalRepresentation (stringVector true 3)= -(thirdMatrix ℚ).transpose := by
  have he := congrArg rationalRepresentation (short_string_two true)
  rw [LieHom.map_lie,map_smul,rationalRepresentation_negative_second] at he
  simp only [shortVector,rootVector,if_true,rationalRepresentation_F,negative] at he
  change ⁅(positive ℚ 0).transpose,(secondMatrix ℚ).transpose⁆=
    (3:ℚ) • rationalRepresentation (stringVector true 3) at he
  rw [transpose_lie,third_bracket,Matrix.transpose_smul] at he
  apply smul_right_injective (Mat ℚ) (by norm_num : (3:ℚ)≠0)
  exact he.symm.trans (by module)

theorem rationalRepresentation_negative_highest :
    rationalRepresentation (highestVector true)=(highestMatrix ℚ).transpose := by
  rw [highestVector,LieHom.map_lie,rationalRepresentation_negative_third]
  simp only [longVector,rootVector,if_true,rationalRepresentation_F,negative]
  change ⁅(positive ℚ 1).transpose,-(thirdMatrix ℚ).transpose⁆=(highestMatrix ℚ).transpose
  rw [lie_neg,transpose_lie,highest_bracket,neg_neg]

end SymmetricSubgroupAsymptotics.CFSGGTwoOriginalBasisMatrices
