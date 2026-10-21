import SymmetricSubgroupAsymptotics.CFSGSymplecticCartanWeights
import SymmetricSubgroupAsymptotics.CFSGDiagonalMatrixLie

/-! The actual integer symplectic matrices satisfy both Cartan-action
Serre relations, with the pinned C-transpose/B entry convention. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices

theorem cartan_eq_diagonal_weight (r : ℕ) (i : Fin r) :
    cartan ℤ r i = Matrix.diagonal (weight r i) := by
  obtain ⟨d, hd⟩ := cartan_isDiagonal ℤ r i
  have hw : weight r i = d := by
    funext x
    simp only [weight, hd, Matrix.diagonal_apply_eq]
  rw [hw]
  exact hd

theorem HE_integer (r : ℕ) (i j : Fin r) :
    ⁅cartan ℤ r i, positive ℤ r j⁆ = CartanMatrix.B r i j • positive ℤ r j := by
  rw [cartan_eq_diagonal_weight]
  by_cases hj : j.val + 1 < r
  · simp only [positive, dif_pos hj, lie_sub]
    rw [CFSGDiagonalMatrixLie.diagonal_lie_single,
      CFSGDiagonalMatrixLie.diagonal_lie_single]
    simp only [mul_one, one_mul]
    rw [weight_chain r i j hj, weight_chain_mirror r i j hj]
    simp only [smul_sub, Matrix.smul_single, zsmul_eq_mul, mul_one, Int.cast_id]
  · simp only [positive, dif_neg hj]
    rw [CFSGDiagonalMatrixLie.diagonal_lie_single]
    simp only [mul_one, one_mul]
    rw [weight_terminal r i j hj]
    simp only [Matrix.smul_single, zsmul_eq_mul, mul_one, Int.cast_id]

theorem HF_integer (r : ℕ) (i j : Fin r) :
    ⁅cartan ℤ r i, negative ℤ r j⁆ = -(CartanMatrix.B r i j • negative ℤ r j) := by
  have h : ⁅negative ℤ r j, cartan ℤ r i⁆ =
      CartanMatrix.B r i j • negative ℤ r j := by
    have ht := congrArg Matrix.transpose (HE_integer r i j)
    simpa only [Ring.lie_def, Matrix.transpose_sub, Matrix.transpose_mul,
      cartan_transpose, Matrix.transpose_smul, negative] using ht
  exact (lie_skew (cartan ℤ r i) (negative ℤ r j)).symm.trans (congrArg Neg.neg h)

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
