import SymmetricSubgroupAsymptotics.CFSGGTwoSerreMatrices
import SymmetricSubgroupAsymptotics.CFSGQuadraticRootDividedPowers
import SymmetricSubgroupAsymptotics.CFSGSquareZeroAdjoint
import Mathlib.Data.Matrix.Cartan

/-! The two actual folded Serre powers. The length-four relation retains
its true quadratic fourth coefficient and proves that coefficient zero
on the other simple root matrix. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGGTwoSerreMatrices
variable (R : Type*) [CommRing R]

 theorem positiveSecond_sandwich :
    positiveSecond R 0*positive R 1*positiveSecond R 0=0 := by
  rw [positive_one_explicit]
  simp [positiveSecond,pos,neg,mul_sub,sub_mul]

 theorem inner_positive_sandwich : positive R 1*positive R 0*positive R 1=0 := by
  rw [positive_zero_explicit,positive_one_explicit]
  simp [pos,neg,add_mul,mul_add,sub_mul,mul_sub]

 theorem negativeSecond_sandwich :
    negativeSecond R 0*negative R 1*negativeSecond R 0=0 := by
  have ht := congrArg Matrix.transpose (positiveSecond_sandwich R)
  simpa only [Matrix.transpose_mul,Matrix.transpose_zero,negativeSecond,negative,mul_assoc] using ht

 theorem inner_negative_sandwich : negative R 1*negative R 0*negative R 1=0 := by
  have ht := congrArg Matrix.transpose (inner_positive_sandwich R)
  simpa only [Matrix.transpose_mul,Matrix.transpose_zero,negative,mul_assoc] using ht

private theorem quadratic_ad_four {B : Type*} [Ring B] [Algebra ℚ B]
    (e d x : B) (he : e*e=d+d) (hed : e*d=0) (hde : d*e=0)
    (hx : d*x*d=0) : ⁅e,⁅e,⁅e,⁅e,x⁆⁆⁆⁆=0 := by
  have h := CFSGQuadraticRootDividedPowers.ad_pow_eq_factorial_operator e d he hed hde 4 x
  change ⁅e,⁅e,⁅e,⁅e,x⁆⁆⁆⁆= _ at h
  rw [h,CFSGIntegralQuadraticRootOperators.operator_four,hx,smul_zero]

 theorem positive_serre (i j : Fin 2) :
    (LieAlgebra.ad ℚ (Mat ℚ) (positive ℚ i)^(-CartanMatrix.G₂ i j).toNat)
      ⁅positive ℚ i,positive ℚ j⁆=0 := by
  by_cases hij : i=j
  · subst j
    rw [lie_self,map_zero]
  · fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change ⁅positive ℚ 0,⁅positive ℚ 0,⁅positive ℚ 0,⁅positive ℚ 0,positive ℚ 1⁆⁆⁆⁆=0
      exact quadratic_ad_four _ _ _ (positive_square ℚ 0)
        (positive_mul_second ℚ 0) (second_mul_positive ℚ 0) (positiveSecond_sandwich ℚ)
    · change ⁅positive ℚ 1,⁅positive ℚ 1,positive ℚ 0⁆⁆=0
      have he : positive ℚ 1*positive ℚ 1=0 := by
        simpa only [positiveSecond,if_neg (show (1:Fin 2)≠0 by decide),add_zero] using
          positive_square ℚ 1
      rw [CFSGSquareZeroAdjoint.lie_lie _ _ he,inner_positive_sandwich]
      simp only [zero_add,neg_zero]
    · exact (hij rfl).elim

 theorem negative_serre (i j : Fin 2) :
    (LieAlgebra.ad ℚ (Mat ℚ) (negative ℚ i)^(-CartanMatrix.G₂ i j).toNat)
      ⁅negative ℚ i,negative ℚ j⁆=0 := by
  by_cases hij : i=j
  · subst j
    rw [lie_self,map_zero]
  · fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change ⁅negative ℚ 0,⁅negative ℚ 0,⁅negative ℚ 0,⁅negative ℚ 0,negative ℚ 1⁆⁆⁆⁆=0
      exact quadratic_ad_four _ _ _ (negative_square ℚ 0)
        (negative_mul_second ℚ 0) (second_mul_negative ℚ 0) (negativeSecond_sandwich ℚ)
    · change ⁅negative ℚ 1,⁅negative ℚ 1,negative ℚ 0⁆⁆=0
      have he : negative ℚ 1*negative ℚ 1=0 := by
        simpa only [negativeSecond,positiveSecond,if_neg (show (1:Fin 2)≠0 by decide),
          Matrix.transpose_zero,add_zero] using negative_square ℚ 1
      rw [CFSGSquareZeroAdjoint.lie_lie _ _ he,inner_negative_sandwich]
      simp only [zero_add,neg_zero]
    · exact (hij rfl).elim

end SymmetricSubgroupAsymptotics.CFSGGTwoSerreMatrices
