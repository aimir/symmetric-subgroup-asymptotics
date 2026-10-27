import SymmetricSubgroupAsymptotics.CFSGSymplecticUniformBlockBasis
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! Actual rational diagonal grading of the uniform primitive symplectic
family. Coefficient support follows from weights, not rank-dependent
sparse-table enumeration. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticUniformRootGrading
open CFSGSymplecticSerreMatrices CFSGSymplecticOriginalRootCandidates
open CFSGSymplecticUniformRootCoordinates CFSGSymplecticUniformBlockCoordinates
open CFSGSymplecticUniformBlockLie CFSGSymplecticUniformBlockBasis
variable (r : ℕ)

def diagonalWeight : Index r→ℚ
  | .inl i => (r:ℚ)-i.val-1/2
  | .inr i => -((r:ℚ)-i.val-1/2)

def gradingMatrix : Mat ℚ r := Matrix.diagonal (diagonalWeight r)

def grade (j : BasisIndex r) : ℚ :=
  diagonalWeight r (entry r j).1-diagonalWeight r (entry r j).2

theorem grading_mem : Block ℚ r (gradingMatrix r) := by
  refine ⟨?_,?_,?_⟩
  · intro i j
    by_cases h : i=j
    · subst j; simp [gradingMatrix,diagonalWeight]
    · simp [gradingMatrix,Matrix.diagonal_apply,h,Ne.symm h]
  · intro i j; simp [gradingMatrix,Matrix.diagonal_apply]
  · intro i j; simp [gradingMatrix,Matrix.diagonal_apply]

theorem bracket_coordinate (M : Mat ℚ r) (j : BasisIndex r) :
    coordinates ℚ r ⁅gradingMatrix r,M⁆ j=grade r j*coordinates ℚ r M j := by
  change (gradingMatrix r * M - M * gradingMatrix r)
    (entry r j).1 (entry r j).2 =
      grade r j * M (entry r j).1 (entry r j).2
  simp only [gradingMatrix,Matrix.diagonal_mul,Matrix.mul_diagonal,
    Matrix.sub_apply,grade]
  ring

theorem matrix_weight (j : BasisIndex r) :
    ⁅gradingMatrix r,matrix ℚ r j⁆=grade r j • matrix ℚ r j := by
  classical
  rw [←reconstruction ℚ r _ (lie_mem ℚ r _ _ (grading_mem r) (matrix_mem ℚ r j))]
  have hc : coordinates ℚ r ⁅gradingMatrix r,matrix ℚ r j⁆=
      grade r j • Pi.single j 1 := by
    funext k
    rw [bracket_coordinate,coordinates_matrix]
    by_cases h : k=j
    · subst k; simp
    · simp [Pi.single_apply,h,Ne.symm h]
  rw [hc,map_smul,Fintype.linearCombination_apply_single,one_smul]

theorem positive_weight (i : Fin r) :
    ⁅gradingMatrix r,positive ℚ r i⁆=positive ℚ r i := by
  by_cases hi : i.val+1<r
  · let next : Fin r:=⟨i.val+1,hi⟩
    let ij : Pair r:=⟨(i,next),by dsimp [next];omega⟩
    have he : positive ℚ r i=matrix ℚ r (.inr (false,.inl ij)) := by
      simp only [positive,dif_pos hi,matrix,ij,next]
    rw [he,matrix_weight]
    have hg : grade r (.inr (false,.inl ij))=1 := by
      simp only [grade,entry,ij,diagonalWeight,next,Fin.val_mk]
      simp only [Nat.cast_add,Nat.cast_one]
      ring
    rw [hg,one_smul]
  · have he : positive ℚ r i=matrix ℚ r (.inr (false,.inr (.inl i))) := by
      simp only [positive,dif_neg hi,matrix]
    rw [he,matrix_weight]
    have hr : (r:ℚ)=(i.val:ℚ)+1 := by
      have hn : r=i.val+1:=by omega
      exact_mod_cast hn
    have hg : grade r (.inr (false,.inr (.inl i)))=1 := by
      simp only [grade,entry,diagonalWeight]
      rw [hr]
      ring
    rw [hg,one_smul]

end SymmetricSubgroupAsymptotics.CFSGSymplecticUniformRootGrading
