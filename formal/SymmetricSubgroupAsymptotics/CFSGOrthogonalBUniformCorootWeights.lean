import SymmetricSubgroupAsymptotics.CFSGOrthogonalBUniformPositiveTables

/-! Literal natural Cartan weights and Jacobi support of B raising
coefficients. All matrices are those of the pinned natural B model. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBUniformCorootWeights
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBOriginalRootCandidates
open CFSGOrthogonalBFullMatrixCoordinates CFSGOrthogonalBFullBlockCoordinates
open CFSGOrthogonalBFullBlockBasis CFSGOrthogonalBUniformPositiveTables
open CFSGOrthogonalBOriginalPositiveSourceProfile
variable (r : ℕ)

def fullWeight (a : Fin r) (j : BasisIndex r) : ℚ :=
  cartan ℚ r a (entry r j).1 (entry r j).1 -
    cartan ℚ r a (entry r j).2 (entry r j).2

def weight (a : Fin r) (j : PositiveIndex r) : ℚ := fullWeight r a (fullIndex r j)

theorem cartan_mem (a : Fin r) : Block ℚ r (cartan ℚ r a) := by
  apply (block_iff_mem_orthogonal r _).mpr
  exact (skewAdjointMatricesLieSubalgebra (gram ℚ r)).lie_mem
    (positive_mem_orthogonal ℚ r a) (negative_mem_orthogonal ℚ r a)

theorem bracket_coordinate (a : Fin r) (M : Mat ℚ r) (j : BasisIndex r) :
    coordinates ℚ r ⁅cartan ℚ r a, M⁆ j = fullWeight r a j * coordinates ℚ r M j := by
  obtain ⟨d, hd⟩ := cartan_isDiagonal ℚ r a
  change sign ℚ r j * (cartan ℚ r a * M - M * cartan ℚ r a)
    (entry r j).1 (entry r j).2 =
      fullWeight r a j * (sign ℚ r j * M (entry r j).1 (entry r j).2)
  simp only [fullWeight, hd, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.sub_apply, Matrix.diagonal_apply_eq]
  ring

theorem matrix_weight (a : Fin r) (j : BasisIndex r) :
    ⁅cartan ℚ r a, matrix ℚ r j⁆ = fullWeight r a j • matrix ℚ r j := by
  classical
  rw [← reconstruction r _ (lie_mem r _ _ (cartan_mem r a) (matrix_mem ℚ r j))]
  have hc : coordinates ℚ r ⁅cartan ℚ r a, matrix ℚ r j⁆ =
      fullWeight r a j • Pi.single j 1 := by
    funext k
    rw [bracket_coordinate, coordinates_matrix]
    by_cases h : k = j
    · subst k; simp
    · simp [Pi.single_apply, h, Ne.symm h]
  rw [hc, map_smul, Fintype.linearCombination_apply_single, one_smul]

theorem positive_matrix_weight (a : Fin r) (j : PositiveIndex r) :
    ⁅cartan ℚ r a, positiveMatrix r j⁆ = weight r a j • positiveMatrix r j :=
  matrix_weight r a (fullIndex r j)

theorem raising_weight (i a : Fin r) (j k : PositiveIndex r)
    (hc : raising r i j k ≠ 0) :
    weight r a k = ((CartanMatrix.B r).transpose a i : ℚ) + weight r a j := by
  have hHE : ⁅cartan ℚ r a, positive ℚ r i⁆ =
      ((CartanMatrix.B r).transpose a i : ℚ) • positive ℚ r i := by
    simpa only [Int.cast_smul_eq_zsmul] using HE ℚ r a i
  have hw : ⁅cartan ℚ r a, ⁅positive ℚ r i, positiveMatrix r j⁆⁆ =
      (((CartanMatrix.B r).transpose a i : ℚ) + weight r a j) •
        ⁅positive ℚ r i, positiveMatrix r j⁆ := by
    rw [leibniz_lie, hHE, positive_matrix_weight, smul_lie, lie_smul, add_smul]
  have h := congrArg (fun M : Mat ℚ r => coordinates ℚ r M (fullIndex r k)) hw
  simp only [bracket_coordinate, map_smul, Pi.smul_apply, smul_eq_mul] at h
  exact mul_right_cancel₀ hc h

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBUniformCorootWeights
