import SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
import Mathlib.LinearAlgebra.SymplecticGroup

/-! Every original simple type-C root matrix is infinitesimally
symplectic for the same standard alternating-form matrix. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
variable (R : Type*) [CommRing R]

theorem diagonal_block_infinitesimal {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I R) :
    Matrix.fromBlocks A 0 0 (-A.transpose) * Matrix.J I R +
      Matrix.J I R * (Matrix.fromBlocks A 0 0 (-A.transpose)).transpose = 0 := by
  simp only [Matrix.J, Matrix.fromBlocks_transpose, Matrix.transpose_zero,
    Matrix.transpose_neg, Matrix.transpose_transpose, Matrix.fromBlocks_multiply]
  ext x y
  cases x <;> cases y <;> simp [Matrix.fromBlocks]

theorem upper_block_infinitesimal {I : Type*} [Fintype I] [DecidableEq I]
    (P : Matrix I I R) (hP : P.transpose = P) :
    Matrix.fromBlocks 0 P 0 0 * Matrix.J I R +
      Matrix.J I R * (Matrix.fromBlocks 0 P 0 0).transpose = 0 := by
  simp only [Matrix.J, Matrix.fromBlocks_transpose, Matrix.transpose_zero, hP,
    Matrix.fromBlocks_multiply]
  ext x y
  cases x <;> cases y <;> simp [Matrix.fromBlocks]

theorem lower_block_infinitesimal {I : Type*} [Fintype I] [DecidableEq I]
    (P : Matrix I I R) (hP : P.transpose = P) :
    Matrix.fromBlocks 0 0 P 0 * Matrix.J I R +
      Matrix.J I R * (Matrix.fromBlocks 0 0 P 0).transpose = 0 := by
  simp only [Matrix.J, Matrix.fromBlocks_transpose, Matrix.transpose_zero, hP,
    Matrix.fromBlocks_multiply]
  ext x y
  cases x <;> cases y <;> simp [Matrix.fromBlocks]

theorem chain_positive_block (r : ℕ) (i : Fin r) (hi : i.val + 1 < r) :
    positive R r i = Matrix.fromBlocks (Matrix.single i (⟨i.val + 1, hi⟩ : Fin r) 1)
      0 0 (-(Matrix.single i (⟨i.val + 1, hi⟩ : Fin r) 1).transpose) := by
  rw [positive, dif_pos hi]
  ext x y
  cases x <;> cases y <;> simp [Matrix.fromBlocks, Matrix.single, and_comm]

theorem terminal_positive_block (r : ℕ) (i : Fin r) (hi : ¬i.val + 1 < r) :
    positive R r i = Matrix.fromBlocks 0 (Matrix.single i i 1) 0 0 := by
  rw [positive, dif_neg hi]
  ext x y
  cases x <;> cases y <;> simp [Matrix.fromBlocks, Matrix.single]

theorem positive_infinitesimal (r : ℕ) (i : Fin r) :
    positive R r i * Matrix.J (Fin r) R +
      Matrix.J (Fin r) R * (positive R r i).transpose = 0 := by
  by_cases hi : i.val + 1 < r
  · rw [chain_positive_block R r i hi]
    exact diagonal_block_infinitesimal R _
  · rw [terminal_positive_block R r i hi]
    exact upper_block_infinitesimal R _ (by simp)

theorem negative_infinitesimal (r : ℕ) (i : Fin r) :
    negative R r i * Matrix.J (Fin r) R +
      Matrix.J (Fin r) R * (negative R r i).transpose = 0 := by
  by_cases hi : i.val + 1 < r
  · have he : negative R r i =
        Matrix.fromBlocks (Matrix.single (⟨i.val + 1, hi⟩ : Fin r) i 1)
          0 0 (-(Matrix.single (⟨i.val + 1, hi⟩ : Fin r) i 1).transpose) := by
      rw [negative, chain_positive_block R r i hi]
      simp only [Matrix.fromBlocks_transpose, Matrix.transpose_zero,
        Matrix.transpose_neg, Matrix.transpose_single]
    rw [he]
    exact diagonal_block_infinitesimal R _
  · have he : negative R r i = Matrix.fromBlocks 0 0 (Matrix.single i i 1) 0 := by
      rw [negative, terminal_positive_block R r i hi]
      simp only [Matrix.fromBlocks_transpose, Matrix.transpose_zero, Matrix.transpose_single]
    rw [he]
    exact lower_block_infinitesimal R _ (by simp)

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
