import SymmetricSubgroupAsymptotics.CFSGHermitianTwoByTwoCongruence
import SymmetricSubgroupAsymptotics.CFSGHermitianTwoByTwoConeGeneration
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! A genuine GL2 coordinate change normalizes two independent rank-one
image rays. The matrix is constructed from the displayed columns, and
its invertibility follows from their actual nonzero determinant. No
unitary-group membership for this auxiliary coordinate change is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGHermitianTwoByTwoRankOne
variable {K : Type*} [Field K]

theorem exists_two_column_unit (v w : Fin 2 → K)
    (hdet : v 0 * w 1 - v 1 * w 0 ≠ 0) :
    ∃ D : (Matrix (Fin 2) (Fin 2) K)ˣ, D.val *ᵥ ![1, 0] = v ∧ D.val *ᵥ ![0, 1] = w := by
  let M : Matrix (Fin 2) (Fin 2) K := !![v 0, w 0; v 1, w 1]
  have hM : M.det ≠ 0 := by
    rw [Matrix.det_fin_two]
    change v 0 * w 1 - w 0 * v 1 ≠ 0
    simpa only [mul_comm] using hdet
  obtain ⟨D, hD⟩ := (Matrix.isUnit_iff_isUnit_det M).mpr (isUnit_iff_ne_zero.mpr hM)
  refine ⟨D, ?_, ?_⟩
  · rw [hD]
    ext i
    fin_cases i <;> simp [M, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply]
  · rw [hD]
    ext i
    fin_cases i <;> simp [M, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply]

theorem exists_rankOne_axis_normalization (sigma : K ≃+* K)
    (hsigma : ∀ z, sigma (sigma z) = z) (E : parameters sigma ≃+ parameters sigma)
    (a b : K) (ha : sigma a = a) (hb : sigma b = b) (v w : Fin 2 → K)
    (hdet : v 0 * w 1 - v 1 * w 0 ≠ 0)
    (hE0 : E (axis0 sigma 1 (map_one sigma)) = rankOneParameter sigma hsigma a ha v)
    (hE1 : E (axis1 sigma 1 (map_one sigma)) = rankOneParameter sigma hsigma b hb w) :
    ∃ D : (Matrix (Fin 2) (Fin 2) K)ˣ,
      (E.trans (coefficientCongruence sigma hsigma D)) (axis0 sigma 1 (map_one sigma)) = axis0 sigma a ha ∧
      (E.trans (coefficientCongruence sigma hsigma D)) (axis1 sigma 1 (map_one sigma)) = axis1 sigma b hb := by
  obtain ⟨D, hD0, hD1⟩ := exists_two_column_unit v w hdet
  have h0 : (D⁻¹).val *ᵥ v = ![1, 0] := by
    rw [← hD0, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have h1 : (D⁻¹).val *ᵥ w = ![0, 1] := by
    rw [← hD1, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  refine ⟨D⁻¹, ?_, ?_⟩
  · change coefficientCongruence sigma hsigma D⁻¹ (E (axis0 sigma 1 (map_one sigma))) = _
    rw [hE0, coefficientCongruence_rankOne, h0, ← axis0_eq_rankOne]
  · change coefficientCongruence sigma hsigma D⁻¹ (E (axis1 sigma 1 (map_one sigma))) = _
    rw [hE1, coefficientCongruence_rankOne, h1, ← axis1_eq_rankOne]

end SymmetricSubgroupAsymptotics.CFSGHermitianTwoByTwoRankOne
