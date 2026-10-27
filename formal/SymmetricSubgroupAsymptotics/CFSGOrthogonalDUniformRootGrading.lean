import SymmetricSubgroupAsymptotics.CFSGOrthogonalDUniformGramBasis
import Mathlib.Tactic.Ring

/-! Actual uniform D grading before reduction. The terminal sum root has
grade one because the last two diagonal weights are one and zero. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDUniformRootGrading
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDOriginalRootCandidates
open CFSGOrthogonalDUniformRationalFamily CFSGOrthogonalDUniformGramCoordinates
variable (r : ℕ) (hr : 4 ≤ r)

def diagonalWeight : Index r→ℚ
  | .inl i=>(r:ℚ)-1-i.val
  | .inr i=>-((r:ℚ)-1-i.val)

def gradingMatrix : Mat ℚ r:=Matrix.diagonal (diagonalWeight r)

def grade : BasisIndex r→ℚ
  | .inl _=>0
  | .inr j=>diagonalWeight r (CFSGOrthogonalDUniformRootCoordinates.entry r j).1-
      diagonalWeight r (CFSGOrthogonalDUniformRootCoordinates.entry r j).2

theorem grading_mem : Orthogonal r (gradingMatrix r) := by
  rw [Orthogonal,mem_skewAdjointMatricesLieSubalgebra,mem_skewAdjointMatricesSubmodule]
  change (gradingMatrix r).transpose*gram ℚ r=gram ℚ r*(-gradingMatrix r)
  simp only [gradingMatrix,Matrix.diagonal_transpose,Matrix.diagonal_mul,mul_neg,
    Matrix.mul_diagonal]
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [gram,diagonalWeight] <;> (try split_ifs) <;> subst_vars <;> ring

theorem bracket_coordinate (M : Mat ℚ r) (j : BasisIndex r) :
    coordinates r hr ⁅gradingMatrix r,M⁆ j=grade r j*coordinates r hr M j := by
  cases j with
  | inl i =>
    have hd : diagonal r ⁅gradingMatrix r,M⁆=0 := by
      funext a
      change (gradingMatrix r*M-M*gradingMatrix r) (.inl a) (.inl a)=0
      simp only [gradingMatrix,Matrix.diagonal_mul,Matrix.mul_diagonal,Matrix.sub_apply]
      ring
    change CFSGOrthogonalDRationalCartanCoordinates.coordinates r hr
      (diagonal r ⁅gradingMatrix r,M⁆) i=0*_
    rw [hd,map_zero]
    simp
  | inr j =>
    change (gradingMatrix r*M-M*gradingMatrix r)
      (CFSGOrthogonalDUniformRootCoordinates.entry r j).1
      (CFSGOrthogonalDUniformRootCoordinates.entry r j).2=grade r (.inr j)*
        M (CFSGOrthogonalDUniformRootCoordinates.entry r j).1
          (CFSGOrthogonalDUniformRootCoordinates.entry r j).2
    simp only [gradingMatrix,Matrix.diagonal_mul,Matrix.mul_diagonal,Matrix.sub_apply,grade]
    ring

include hr in
theorem matrix_weight (j : BasisIndex r) :
    ⁅gradingMatrix r,matrix r j⁆=grade r j • matrix r j := by
  classical
  rw [←CFSGOrthogonalDUniformGramBasis.reconstruction r hr _
    ((skewAdjointMatricesLieSubalgebra (gram ℚ r)).lie_mem (grading_mem r)
      (CFSGOrthogonalDUniformGramBasis.matrix_mem r j))]
  have hc : coordinates r hr ⁅gradingMatrix r,matrix r j⁆=grade r j • Pi.single j 1 := by
    funext k
    rw [bracket_coordinate,CFSGOrthogonalDUniformRationalFamily.coordinates_matrix]
    by_cases h : k=j
    · subst k; simp
    · simp [Pi.single_apply,h,Ne.symm h]
  rw [hc,map_smul,Fintype.linearCombination_apply_single,one_smul]

include hr in
theorem positive_weight (i : Fin r) : ⁅gradingMatrix r,positive ℚ r i⁆=positive ℚ r i := by
  by_cases hi : i.val+1 < r
  · let next : Fin r:=⟨i.val+1,hi⟩
    let ij : Pair r:=⟨(i,next),by dsimp [next]; omega⟩
    have he : positive ℚ r i=matrix r (.inr (false,.inl ij)) := by
      simp only [positive,dif_pos hi,matrix,CFSGOrthogonalDUniformRootCoordinates.matrix,
        CFSGOrthogonalDUniformRootMatrixArithmetic.difference,ij,next]
    rw [he,matrix_weight r hr]
    have hg : grade r (.inr (false,.inl ij))=1 := by
      simp only [grade,CFSGOrthogonalDUniformRootCoordinates.entry,ij,next,diagonalWeight,
        Nat.cast_add,Nat.cast_one]
      ring
    rw [hg,one_smul]
  · let prev:=previous r i
    have hil:=i.isLt
    have hp : prev.val < i.val := by dsimp [prev,previous]; omega
    let ij : Pair r:=⟨(prev,i),hp⟩
    have he : positive ℚ r i=matrix r (.inr (false,.inr ij)) := by
      simp only [positive,dif_neg hi,matrix,CFSGOrthogonalDUniformRootCoordinates.matrix,
        CFSGOrthogonalDUniformRootMatrixArithmetic.sumRoot,ij,prev]
    rw [he,matrix_weight r hr]
    have hrr : (r:ℚ)=(i.val:ℚ)+1 := by
      have hn : r=i.val+1:=by omega
      exact_mod_cast hn
    have hpp : (prev.val:ℚ)=(i.val:ℚ)-1 := by
      dsimp [prev]
      rw [Nat.cast_sub (by omega)]
      norm_num
    have hg : grade r (.inr (false,.inr ij))=1 := by
      simp only [grade,CFSGOrthogonalDUniformRootCoordinates.entry,ij,diagonalWeight]
      rw [hrr,hpp]
      ring
    rw [hg,one_smul]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDUniformRootGrading
