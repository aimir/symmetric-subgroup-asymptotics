import SymmetricSubgroupAsymptotics.CFSGONCachedColumnRowVectorBinding

/-! ONE154/F3 row0 pilot: ONLY packed-Nat transpose and scalar decisions.
Original source coefficients enter exclusively via old checked column
bindings. No fresh string proof, full vector period or order is claimed. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGONSelectedPrimeElevenTransposeRowZeroPilot
open MatrixNaturalRowDotReflection MatrixModelSelectedPointPeriodTwo
open CFSG.Models.MatrixGroups.ON

def firstRowCode : ℕ := 4
def secondRowCode : ℕ := 16
def inputCode : ℕ := 1
def intermediateCode : ℕ := 51507437877254353631615379677337067739678913556795101676055975492677036869636584028460024064
def outputCode : ℕ := 132534785328821890248032510400660882548513784610037928392731511730517166056954094813645377536

theorem first_transpose : ∀ j : Fin 154,
    packedDigit 2 (CFSGONFirstSquareRowZeroPilot.columnCode j.val) 0=
      packedDigit 2 firstRowCode j.val := by decide +kernel

theorem second_transpose : ∀ j : Fin 154,
    packedDigit 2 (CFSGONSelectedSecondFourthRowPilot.columnCode j.val) 0=
      packedDigit 2 secondRowCode j.val := by decide +kernel

private theorem first_row_binding (j : Fin 154) : rawDigit rows1 0 j.val=
    packedDigit 2 firstRowCode j.val :=
  (CFSGONFirstSquareRowZeroPilot.source_column_binding j 0).trans (first_transpose j)

private theorem second_row_binding (j : Fin 154) : rawDigit rows2 0 j.val=
    packedDigit 2 secondRowCode j.val :=
  (CFSGONSelectedSecondFourthRowPilot.source_column_binding j 0).trans (second_transpose j)

private theorem first_check : packedDot 2 firstRowCode intermediateCode 154 % 3=
    packedDigit 2 outputCode 0 % 3 := by decide +kernel
private theorem second_check : packedDot 2 secondRowCode inputCode 154 % 3=
    packedDigit 2 intermediateCode 0 % 3 := by decide +kernel

theorem first_selected_coordinate :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 *ᵥ
      (fun j : Fin 154 => (packedDigit 2 intermediateCode j.val : ZMod 3))) 0=
        (packedDigit 2 outputCode 0 : ZMod 3) :=
  MatrixModelSelectedRowVectorReflection.coordinate_step 3 154 2 rows1 0 firstRowCode
    intermediateCode outputCode first_row_binding first_check

theorem second_selected_coordinate :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 *ᵥ
      (fun j : Fin 154 => (packedDigit 2 inputCode j.val : ZMod 3))) 0=
        (packedDigit 2 intermediateCode 0 : ZMod 3) :=
  MatrixModelSelectedRowVectorReflection.coordinate_step 3 154 2 rows2 0 secondRowCode
    inputCode intermediateCode second_row_binding second_check

end SymmetricSubgroupAsymptotics.CFSGONSelectedPrimeElevenTransposeRowZeroPilot
