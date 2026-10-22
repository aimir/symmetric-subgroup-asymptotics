import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexMiddleAction
import Mathlib.Algebra.CharP.Reduced
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! A defining-characteristic power element in the actual U-normalizer
acts diagonally on its final hyperbolic plane in odd characteristic.
The characteristic-two anti-diagonal alternative is not discarded. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexOddMiddlePower
open CFSGOrthogonalDIndexMiddleAction
variable (K : Type) [Field K]

def middleDet (s : ℕ) : rootNormalizer K s →* K :=
  Matrix.detMonoidHom.comp (middleHom K s)

theorem middle_det_eq_one_of_pPower (s p k : ℕ) [Fact p.Prime] [CharP K p]
    (A : rootNormalizer K s) (hA : A ^ (p ^ k) = 1) :
    Matrix.det (middleHom K s A) = 1 := by
  have hp : (middleDet K s A) ^ (p ^ k) = 1 := by
    rw [← map_pow, hA, map_one]
  apply iterateFrobenius_inj K p k
  simpa only [iterateFrobenius_def, one_pow] using hp

theorem middle_lower_zero_of_pPower (s p k : ℕ) [Fact p.Prime] [CharP K p]
    (hodd : (2 : K) ≠ 0) (A : rootNormalizer K s) (hA : A ^ (p ^ k) = 1) :
    (middleHom K s A) 1 0 = 0 := by
  rcases middle_matrix_dichotomy K s A with hdiag | hanti
  · exact hdiag.2.1
  · have hd := middle_det_eq_one_of_pPower K s p k A hA
    rw [Matrix.det_fin_two, hanti.1, hanti.2.1, zero_mul, zero_sub, hanti.2.2] at hd
    have hz : (2 : K) = 0 := by linear_combination -hd
    exact False.elim (hodd hz)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexOddMiddlePower
