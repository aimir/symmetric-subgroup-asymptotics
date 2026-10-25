import SymmetricSubgroupAsymptotics.CFSGReeFFourDerivedPositiveFourProbes
import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryOrderedPrefixMatrices

/-! Selected literal row/column of the ACTUAL yxy^-1 word matrix.
Only two 26-entry products of already checked flat matrices are reduced.
The inverse middle word is handled by actual original-word cancellation,
not by a new full matrix table or a recognition assumption. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryConjugateOuterColumns
open CFSGReeFFourDerivedPositiveFourProbes CFSGReeFFourBinaryOrderedPrefixMatrices
open CFSGReeFFourBinaryOrderedRootWords CFSGReeFFourBinaryOrderedMatrixData
open CFSGFFourNormPrimeFieldWords CFSGFFourNormSparseWordMatrix
open CFSGFFourNormPrimeFieldMatrixTransport CFSGReeFFourFieldParameters
open CFSGReeFFourMiddleDerivedFiveRootWords CFSGReeFFourBinarySeedOuterMatrix

local notation "Y" => CFSGReeFFourBinarySeedMiddleMatrix.matrix

def reverseMiddleMatrix : Mat := wordMatrix (ZMod 2) fourCycleLetters.reverse

def conjugateOuterMatrix : Mat := Y*outerMatrix*reverseMiddleMatrix

theorem middle_reverse_product (m : ℕ) : Y*reverseMiddleMatrix=1 := by
  have hv : wordValue (Field m) (fourCycleLetters++fourCycleLetters.reverse)=
      wordValue (Field m) [] := by
    rw [wordValue_append,reversed_letters_value,mul_inv_cancel]
    rfl
  have hm := wordMatrix_eq_of_wordValue_eq (Field m) _ _ hv
  rw [wordMatrix_append,middle_seed_matrix] at hm
  exact hm

theorem reverse_middle_product (m : ℕ) : reverseMiddleMatrix*Y=1 := by
  have hv : wordValue (Field m) (fourCycleLetters.reverse++fourCycleLetters)=
      wordValue (Field m) [] := by
    rw [wordValue_append,reversed_letters_value,inv_mul_cancel]
    rfl
  have hm := wordMatrix_eq_of_wordValue_eq (Field m) _ _ hv
  rw [wordMatrix_append,middle_seed_matrix] at hm
  exact hm

theorem probe_one_matrix : wordMatrix (ZMod 2) (probeLetters 1)=conjugateOuterMatrix := by
  change wordMatrix (ZMod 2) (fourCycleLetters++outerLetters++fourCycleLetters.reverse)=_
  rw [wordMatrix_append,wordMatrix_append,middle_seed_matrix,outer_seed_matrix]
  rfl

private theorem middle_column_two : ∀i : Fin 26,Y i 2=if i=2 then 1 else 0 := by
  decide +kernel

private theorem middle_outer_column_two : ∀i : Fin 26,
    (Y*outerMatrix) i 2=if i∈({2,3,4,6} : Finset (Fin 26)) then 1 else 0 := by
  decide +kernel

private def rowBridge : Mat := fun i j =>
  if i=1 ∧ j∈({1,3,5,6,9,11} : Finset (Fin 26)) then 1 else 0

private theorem middle_outer_row_one : ∀j : Fin 26,
    (Y*outerMatrix) 1 j=(rowBridge*Y) 1 j := by
  decide +kernel

private theorem row_mul_transport (A B C : Mat) (i : Fin 26)
    (h : ∀k,A i k=B i k) : ∀j,(A*C) i j=(B*C) i j := by
  intro j
  simp only [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [h k]

private theorem mulVec_right_fixed (A B : Mat) (v : Fin 26 → ZMod 2)
    (h : B.mulVec v=v) : (A*B).mulVec v=A.mulVec v := by
  rw [←Matrix.mulVec_mulVec,h]

theorem conjugate_outer_column_two : ∀i : Fin 26,
    conjugateOuterMatrix i 2=if i∈({2,3,4,6} : Finset (Fin 26)) then 1 else 0 := by
  have hY : (Y).mulVec (Pi.single 2 1)=Pi.single 2 1 := by
    funext i
    simpa only [Matrix.mulVec_single_one,Matrix.col_apply,Pi.single_apply,eq_comm]
      using middle_column_two i
  have hD : reverseMiddleMatrix.mulVec (Pi.single 2 1)=Pi.single 2 1 := by
    calc
      reverseMiddleMatrix.mulVec (Pi.single 2 1)=
          reverseMiddleMatrix.mulVec ((Y).mulVec (Pi.single 2 1)) :=
        congrArg reverseMiddleMatrix.mulVec hY.symm
      _=(reverseMiddleMatrix*Y).mulVec (Pi.single 2 1) :=
        Matrix.mulVec_mulVec (Pi.single 2 1) reverseMiddleMatrix Y
      _=Pi.single 2 1 := by rw [reverse_middle_product 0,Matrix.one_mulVec]
  have he := mulVec_right_fixed (Y*outerMatrix) reverseMiddleMatrix (Pi.single 2 1) hD
  intro i
  have hi := congrFun he i
  simp only [Matrix.mulVec_single_one,Matrix.col_apply] at hi
  exact hi.trans (middle_outer_column_two i)

theorem conjugate_outer_row_one : ∀j : Fin 26,
    conjugateOuterMatrix 1 j=
      if j∈({1,3,5,6,9,11} : Finset (Fin 26)) then 1 else 0 := by
  intro j
  calc
    conjugateOuterMatrix 1 j=((Y*outerMatrix)*reverseMiddleMatrix) 1 j := rfl
    _=((rowBridge*Y)*reverseMiddleMatrix) 1 j :=
      row_mul_transport (Y*outerMatrix) (rowBridge*Y) reverseMiddleMatrix 1
        middle_outer_row_one j
    _=(rowBridge*(Y*reverseMiddleMatrix)) 1 j :=
      congrArg (fun A : Mat => A 1 j) (Matrix.mul_assoc rowBridge Y reverseMiddleMatrix)
    _=rowBridge 1 j := by rw [middle_reverse_product 0,Matrix.mul_one]
    _=_ := by simp only [rowBridge,eq_self_iff_true,true_and]

end SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryConjugateOuterColumns
