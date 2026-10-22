import SymmetricSubgroupAsymptotics.CFSGOrthogonalBRationalForm
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBElementaryGroup
import Mathlib.Algebra.Module.Torsion.Free

/-! The actual quadratic B root matrices preserve the literal Gram
matrix in odd characteristic. The quadratic coefficient is retained;
only the proved relation X²=2Y is divided by two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBIndexForm
open CFSGOrthogonalBSerreMatrices
variable {K : Type} [Field K]

private theorem second_adjoint {I : Type*} [Fintype I] [DecidableEq I]
    (h2 : (2 : K) ≠ 0) (J X Y : Matrix I I K)
    (hX : X.transpose * J = -(J * X)) (hXX : X * X = (2 : K) • Y) :
    Y.transpose * J = J * Y := by
  apply smul_right_injective (Matrix I I K) h2
  calc
    (2 : K) • (Y.transpose * J) = ((2 : K) • Y).transpose * J := by
      rw [Matrix.transpose_smul, smul_mul_assoc]
    _ = (X * X).transpose * J := by rw [hXX]
    _ = X.transpose * (X.transpose * J) := by rw [Matrix.transpose_mul, mul_assoc]
    _ = J * (X * X) := by
      rw [hX, mul_neg, ← mul_assoc, hX, neg_mul, neg_neg, mul_assoc]
    _ = (2 : K) • (J * Y) := by rw [hXX, mul_smul_comm]

theorem root_preserves (h2 : (2 : K) ≠ 0) (r : ℕ) (neg : Bool) (i : Fin r) (t : K) :
    (rootTransvection K r neg i t : Mat K r).transpose * gram K r *
      (rootTransvection K r neg i t : Mat K r) = gram K r := by
  have hX : (rootMatrix K r neg i).transpose * gram K r = -(gram K r * rootMatrix K r neg i) := by
    have h : rootMatrix K r neg i ∈ skewAdjointMatricesLieSubalgebra (gram K r) := by
      cases neg
      · exact positive_mem_orthogonal K r i
      · exact negative_mem_orthogonal K r i
    rw [mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule] at h
    change (rootMatrix K r neg i).transpose * gram K r = gram K r * (-rootMatrix K r neg i) at h
    simpa only [mul_neg] using h
  have hXX : rootMatrix K r neg i * rootMatrix K r neg i = (2 : K) • rootSecond K r neg i := by
    simpa only [two_smul] using rootMatrix_square K r neg i
  have hY := second_adjoint h2 (gram K r) _ _ hX hXX
  have he : (rootTransvection K r neg i t : Mat K r).transpose * gram K r =
      gram K r * (↑((rootTransvection K r neg i t)⁻¹) : Mat K r) := by
    rw [rootTransvection_val, rootTransvection_inv_val]
    simp only [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_smul,
      add_mul, one_mul, smul_mul_assoc, hX, hY, mul_add, mul_neg, mul_one,
      mul_smul_comm, smul_neg, sub_eq_add_neg]
  rw [he, mul_assoc, Units.inv_mul, mul_one]

def formUnits (K : Type) [Field K] (r : ℕ) : Subgroup ((Mat K r)ˣ) where
  carrier := {g | (g : Mat K r).transpose * gram K r * (g : Mat K r) = gram K r}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    change ((g : Mat K r) * (h : Mat K r)).transpose * gram K r *
      ((g : Mat K r) * (h : Mat K r)) = gram K r
    rw [Matrix.transpose_mul]
    calc
      _ = (h : Mat K r).transpose *
          ((g : Mat K r).transpose * gram K r * (g : Mat K r)) * (h : Mat K r) := by
        simp only [mul_assoc]
      _ = _ := by rw [hg, hh]
  inv_mem' := by
    intro g hg
    change (↑g⁻¹ : Mat K r).transpose * gram K r * (↑g⁻¹ : Mat K r) = gram K r
    calc
      _ = (↑g⁻¹ : Mat K r).transpose *
          ((g : Mat K r).transpose * gram K r * (g : Mat K r)) * (↑g⁻¹ : Mat K r) := by rw [hg]
      _ = gram K r := by
        have hi : (g : Mat K r) * (↑g⁻¹ : Mat K r) = 1 := Units.mul_inv g
        calc
          _ = ((g : Mat K r) * (↑g⁻¹ : Mat K r)).transpose * gram K r *
              ((g : Mat K r) * (↑g⁻¹ : Mat K r)) := by
            rw [Matrix.transpose_mul]
            simp only [mul_assoc]
          _ = _ := by rw [hi, Matrix.transpose_one, one_mul, mul_one]

theorem elementary_le_formUnits (h2 : (2 : K) ≠ 0) (r : ℕ) :
    elementaryRootGroup K r ≤ formUnits K r := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨neg, i, t, rfl⟩
  exact root_preserves h2 r neg i t

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBIndexForm
