import SymmetricSubgroupAsymptotics.CFSGReeFFourDerivedPositiveFourProbes
import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryOrderedPrefixMatrices

/-! Only selected rows/columns of the already checked middle matrix
squared. These bind the literal actual y² probe and allow reuse of the
proved columns e2 and e4. There is no full table or recognition premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryMiddleSquareColumns
open CFSGReeFFourDerivedPositiveFourProbes CFSGReeFFourBinaryOrderedPrefixMatrices
open CFSGReeFFourBinaryOrderedMatrixData CFSGFFourNormSparseWordMatrix
open CFSGReeFFourMiddleDerivedFiveRootWords CFSGFFourNormPrimeFieldWords
open scoped BigOperators

def middleSquareMatrix : Mat :=
  CFSGReeFFourBinarySeedMiddleMatrix.matrix*CFSGReeFFourBinarySeedMiddleMatrix.matrix

theorem probe_two_matrix : wordMatrix (ZMod 2) (probeLetters 2)=middleSquareMatrix := by
  change wordMatrix (ZMod 2) (fourCycleLetters++fourCycleLetters)=_
  rw [wordMatrix_append,middle_seed_matrix]
  rfl

private theorem row_one : ∀k : Fin 26,
    middleSquareMatrix 1 k=if k∈({1,12} : Finset (Fin 26)) then 1 else 0 := by
  decide +kernel

private theorem row_five : ∀k : Fin 26,
    middleSquareMatrix 5 k=if k∈({3,5} : Finset (Fin 26)) then 1 else 0 := by
  decide +kernel

private theorem row_six : ∀k : Fin 26,
    middleSquareMatrix 6 k=if k∈({3,4,6} : Finset (Fin 26)) then 1 else 0 := by
  decide +kernel

private theorem row_nine : ∀k : Fin 26,
    middleSquareMatrix 9 k=if k∈({7,9} : Finset (Fin 26)) then 1 else 0 := by
  decide +kernel

private theorem row_twentyThree : ∀k : Fin 26,
    middleSquareMatrix 23 k=if k∈({21,23} : Finset (Fin 26)) then 1 else 0 := by
  decide +kernel

private theorem selected_row_apply (A : Mat) (i : Fin 26) (S : Finset (Fin 26))
    (h : ∀k,A i k=if k∈S then 1 else 0) (v : Fin 26 → ZMod 2) :
    (A.mulVec v) i=∑k∈S,v k := by
  change (∑k : Fin 26,A i k*v k)=∑k∈S,v k
  simp_rw [h]
  simp [ite_mul]

theorem middle_square_apply_one (v : Fin 26 → ZMod 2) :
    (middleSquareMatrix.mulVec v) 1=v 1+v 12 := by
  simpa [add_assoc] using selected_row_apply middleSquareMatrix 1 {1,12} row_one v

theorem middle_square_apply_five (v : Fin 26 → ZMod 2) :
    (middleSquareMatrix.mulVec v) 5=v 3+v 5 := by
  simpa [add_assoc] using selected_row_apply middleSquareMatrix 5 {3,5} row_five v

theorem middle_square_apply_six (v : Fin 26 → ZMod 2) :
    (middleSquareMatrix.mulVec v) 6=v 3+v 4+v 6 := by
  simpa [add_assoc] using selected_row_apply middleSquareMatrix 6 {3,4,6} row_six v

theorem middle_square_apply_nine (v : Fin 26 → ZMod 2) :
    (middleSquareMatrix.mulVec v) 9=v 7+v 9 := by
  simpa [add_assoc] using selected_row_apply middleSquareMatrix 9 {7,9} row_nine v

theorem middle_square_apply_twentyThree (v : Fin 26 → ZMod 2) :
    (middleSquareMatrix.mulVec v) 23=v 21+v 23 := by
  simpa [add_assoc] using selected_row_apply middleSquareMatrix 23 {21,23} row_twentyThree v

private theorem column_two : ∀i : Fin 26,
    middleSquareMatrix i 2=if i=2 then 1 else 0 := by
  decide +kernel

private theorem column_four : ∀i : Fin 26,
    middleSquareMatrix i 4=(if i=4 then 1 else 0)+(if i=6 then 1 else 0) := by
  decide +kernel

theorem middle_square_fix_two :
    middleSquareMatrix.mulVec (Pi.single 2 1)=Pi.single 2 1 := by
  funext i
  simpa only [Matrix.mulVec_single_one,Matrix.col_apply,Pi.single_apply,eq_comm]
    using column_two i

theorem middle_square_apply_four :
    middleSquareMatrix.mulVec (Pi.single 4 1)=Pi.single 4 1+Pi.single 6 1 := by
  funext i
  simpa only [Matrix.mulVec_single_one,Matrix.col_apply,Pi.add_apply,Pi.single_apply,eq_comm]
    using column_four i

end SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryMiddleSquareColumns
