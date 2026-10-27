import SymmetricSubgroupAsymptotics.CFSGOrthogonalBFullBlockBasis
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBOriginalPositiveSourceProfile
import Mathlib.Tactic.NormNum

/-! Exact natural B height grading. The middle coordinate has grade zero,
positive coordinates r-i, and negative coordinates -(r-i). All signed
root grades agree with the actual original-path heights. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBUniformRootGrading
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBOriginalRootCandidates
open CFSGOrthogonalBFullMatrixCoordinates CFSGOrthogonalBFullBlockCoordinates
open CFSGOrthogonalBFullBlockBasis
open CFSGOrthogonalBOriginalPositiveSourceProfile
variable (r : ℕ)

def diagonalWeight : Index r → ℚ
  | .inl (.inl i) => (r : ℚ) - i.val
  | .inl (.inr i) => -((r : ℚ) - i.val)
  | .inr _ => 0

def gradingMatrix : Mat ℚ r := Matrix.diagonal (diagonalWeight r)

def grade (j : BasisIndex r) : ℚ :=
  diagonalWeight r (entry r j).1 - diagonalWeight r (entry r j).2

theorem grading_mem : Block ℚ r (gradingMatrix r) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    by_cases h : i = j
    · subst j; simp [gradingMatrix, diagonalWeight, pos, neg]
    · simp [gradingMatrix, diagonalWeight, Matrix.diagonal_apply, h, Ne.symm h, pos, neg]
  · intro i j; simp [gradingMatrix, Matrix.diagonal_apply, pos, neg]
  · intro i j; simp [gradingMatrix, Matrix.diagonal_apply, pos, neg]
  · intro i; simp [gradingMatrix, Matrix.diagonal_apply, pos, neg]
  · intro i; simp [gradingMatrix, Matrix.diagonal_apply, pos, neg]
  · intro i; simp [gradingMatrix, Matrix.diagonal_apply, pos, neg, middle]
  · intro i; simp [gradingMatrix, Matrix.diagonal_apply, pos, neg, middle]
  · simp [gradingMatrix, diagonalWeight, middle]

theorem bracket_coordinate (M : Mat ℚ r) (j : BasisIndex r) :
    coordinates ℚ r ⁅gradingMatrix r, M⁆ j = grade r j * coordinates ℚ r M j := by
  change sign ℚ r j * (gradingMatrix r * M - M * gradingMatrix r)
    (entry r j).1 (entry r j).2 =
      grade r j * (sign ℚ r j * M (entry r j).1 (entry r j).2)
  simp only [gradingMatrix, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.sub_apply, grade]
  ring

theorem matrix_weight (j : BasisIndex r) :
    ⁅gradingMatrix r, matrix ℚ r j⁆ = grade r j • matrix ℚ r j := by
  classical
  rw [← reconstruction r _ (lie_mem r _ _ (grading_mem r) (matrix_mem ℚ r j))]
  have hc : coordinates ℚ r ⁅gradingMatrix r, matrix ℚ r j⁆ =
      grade r j • Pi.single j 1 := by
    funext k
    rw [bracket_coordinate, coordinates_matrix]
    by_cases h : k = j
    · subst k; simp
    · simp [Pi.single_apply, h, Ne.symm h]
  rw [hc, map_smul, Fintype.linearCombination_apply_single, one_smul]

theorem positive_root_grade (j : RootIndex r) :
    grade r (.inr (false, j)) = (rootHeight r j : ℚ) := by
  rcases j with ij | (i | ij)
  · have h := ij.property
    simp only [rootHeight, grade, entry, diagonalWeight, pos]
    rw [Nat.cast_sub (by omega)]
    ring
  · have hi := i.isLt
    simp only [rootHeight, grade, entry, diagonalWeight, pos, middle]
    rw [Nat.cast_sub (by omega)]
    ring
  · have hi := ij.val.1.isLt
    have hj := ij.val.2.isLt
    simp only [rootHeight, grade, entry, diagonalWeight, pos, neg, Nat.cast_add]
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    ring

theorem negative_root_grade (j : RootIndex r) :
    grade r (.inr (true, j)) = -(rootHeight r j : ℚ) := by
  rw [← positive_root_grade r j]
  rcases j with ij | (i | ij) <;>
    simp only [grade, entry, diagonalWeight, pos, neg, middle] <;> ring

theorem positive_weight (i : Fin r) :
    ⁅gradingMatrix r, positive ℚ r i⁆ = positive ℚ r i := by
  by_cases hi : i.val + 1 < r
  · let next : Fin r := ⟨i.val + 1, hi⟩
    let ij : Pair r := ⟨(i, next), by dsimp [next]; omega⟩
    have he : positive ℚ r i = matrix ℚ r (.inr (false, .inl ij)) := by
      simp only [positive, dif_pos hi, matrix, CFSGOrthogonalBUniformRootMatrixArithmetic.difference, ij, next]
    rw [he, matrix_weight, positive_root_grade]
    have hh : rootHeight r (.inl ij) = 1 := by simp [rootHeight, ij, next]
    rw [hh, Nat.cast_one, one_smul]
  · have he : positive ℚ r i = matrix ℚ r (.inr (false, .inr (.inl i))) := by
      simp only [positive, dif_neg hi, matrix, CFSGOrthogonalBUniformRootMatrixArithmetic.short]
    rw [he, matrix_weight, positive_root_grade]
    have hh : rootHeight r (.inr (.inl i)) = 1 := by
      change r - i.val = 1
      have hlt := i.isLt
      omega
    rw [hh, Nat.cast_one, one_smul]

theorem negative_weight (i : Fin r) :
    ⁅gradingMatrix r, negative ℚ r i⁆ = (-1 : ℚ) • negative ℚ r i := by
  by_cases hi : i.val + 1 < r
  · let next : Fin r := ⟨i.val + 1, hi⟩
    let ij : Pair r := ⟨(i, next), by dsimp [next]; omega⟩
    have he : negative ℚ r i = matrix ℚ r (.inr (true, .inl ij)) := by
      simp only [negative, dif_pos hi, matrix, CFSGOrthogonalBUniformRootMatrixArithmetic.difference,
        Matrix.transpose_sub, Matrix.transpose_single, ij, next]
    rw [he, matrix_weight, negative_root_grade]
    have hh : rootHeight r (.inl ij) = 1 := by simp [rootHeight, ij, next]
    rw [hh, Nat.cast_one]
  · have he : negative ℚ r i = matrix ℚ r (.inr (true, .inr (.inl i))) := by
      simp only [negative, dif_neg hi, matrix]
    rw [he, matrix_weight, negative_root_grade]
    have hh : rootHeight r (.inr (.inl i)) = 1 := by
      change r - i.val = 1
      have hlt := i.isLt
      omega
    rw [hh, Nat.cast_one]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBUniformRootGrading
