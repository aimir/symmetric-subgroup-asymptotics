import SymmetricSubgroupAsymptotics.MatrixPackedColumnTransposeRowBinding
import SymmetricSubgroupAsymptotics.CFSGONFirstSquareRowZeroPilot
import SymmetricSubgroupAsymptotics.CFSGONSelectedSecondFourthRowPilot

/-! SAME original ON154/F3 matrix action from already checked source-column
caches. Future finite certificates need only packed-Nat transpose and dot
checks; no fresh native154-squared string checks or model transfer occur. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGONCachedColumnRowVectorBinding
open MatrixNaturalRowDotReflection MatrixModelSelectedPointPeriodTwo
open CFSG.Models.MatrixGroups.ON

abbrev V := Fin 154 → ZMod 3

theorem first_row_binding (rowCode : ℕ → ℕ)
    (htranspose : ∀ i j : Fin 154,
      packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) i.val=
        packedDigit 2 (rowCode i.val) j.val) :
    ∀ i j : Fin 154,rawDigit rows1 i.val j.val=packedDigit 2 (rowCode i.val) j.val :=
  MatrixPackedColumnTransposeRowBinding.row_binding_of_column_transpose 154 2 rows1
    CFSGONFirstSquareRowZeroPilot.columnCode rowCode
    CFSGONFirstSquareRowZeroPilot.source_column_binding htranspose

theorem second_row_binding (rowCode : ℕ → ℕ)
    (htranspose : ∀ i j : Fin 154,
      packedDigit 2 (CFSGONSelectedSecondFourthRowPilot.columnCode j.val) i.val=
        packedDigit 2 (rowCode i.val) j.val) :
    ∀ i j : Fin 154,rawDigit rows2 i.val j.val=packedDigit 2 (rowCode i.val) j.val :=
  MatrixPackedColumnTransposeRowBinding.row_binding_of_column_transpose 154 2 rows2
    CFSGONSelectedSecondFourthRowPilot.columnCode rowCode
    CFSGONSelectedSecondFourthRowPilot.source_column_binding htranspose

theorem first_vector_step (rowCode : ℕ → ℕ) (inputCode nextCode : ℕ)
    (htranspose : ∀ i j : Fin 154,
      packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) i.val=
        packedDigit 2 (rowCode i.val) j.val)
    (hcheck : ∀ i : Fin 154,
      packedDot 2 (rowCode i.val) inputCode 154 % 3=packedDigit 2 nextCode i.val % 3) :
    CFSG.Models.MatrixData.matrix 3 154 rows1 *ᵥ
      (fun j : Fin 154 => (packedDigit 2 inputCode j.val : ZMod 3))=
      fun i : Fin 154 => (packedDigit 2 nextCode i.val : ZMod 3) := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 3 154 2 rows1 i
    (rowCode i.val) inputCode nextCode (fun j => first_row_binding rowCode htranspose i j) (hcheck i)

theorem second_vector_step (rowCode : ℕ → ℕ) (inputCode nextCode : ℕ)
    (htranspose : ∀ i j : Fin 154,
      packedDigit 2 (CFSGONSelectedSecondFourthRowPilot.columnCode j.val) i.val=
        packedDigit 2 (rowCode i.val) j.val)
    (hcheck : ∀ i : Fin 154,
      packedDot 2 (rowCode i.val) inputCode 154 % 3=packedDigit 2 nextCode i.val % 3) :
    CFSG.Models.MatrixData.matrix 3 154 rows2 *ᵥ
      (fun j : Fin 154 => (packedDigit 2 inputCode j.val : ZMod 3))=
      fun i : Fin 154 => (packedDigit 2 nextCode i.val : ZMod 3) := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 3 154 2 rows2 i
    (rowCode i.val) inputCode nextCode (fun j => second_row_binding rowCode htranspose i j) (hcheck i)

end SymmetricSubgroupAsymptotics.CFSGONCachedColumnRowVectorBinding
