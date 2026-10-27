import SymmetricSubgroupAsymptotics.MatrixModelSelectedRowVectorReflection
import SymmetricSubgroupAsymptotics.External.CFSG.Models.MatrixGroups.HN

/-! ONEnew-size selected pilot: original HN row0 of both matrices and
only two actual scalar outputs. No all-row binding or period is claimed. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGHNSelectedPrimeElevenRowZeroPilot
open MatrixNaturalRowDotReflection MatrixModelSelectedPointPeriodTwo

def firstRowCode : ℕ := 1
def secondRowCode : ℕ := 8
def inputCode : ℕ := 1
def intermediateCode : ℕ := 81761091898769599637394330553005844598810336270941627045392749374395027158849809144704230012814331612131477155238380032
def outputCode : ℕ := 5834075128331754494327698256285654008839723458916779997173857535700887152904482263995920698410481818057027697130897408

theorem first_row_binding : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows1 0 j.val = packedDigit 3 firstRowCode j.val := by
  decide +kernel

theorem second_row_binding : ∀ j : Fin 133,
    rawDigit CFSG.Models.MatrixGroups.HN.rows2 0 j.val = packedDigit 3 secondRowCode j.val := by
  decide +kernel

private theorem second_check : packedDot 3 secondRowCode inputCode 133 % 5 =
    packedDigit 3 intermediateCode 0 % 5 := by decide +kernel
private theorem first_check : packedDot 3 firstRowCode intermediateCode 133 % 5 =
    packedDigit 3 outputCode 0 % 5 := by decide +kernel

theorem second_selected_coordinate :
    (CFSG.Models.MatrixData.matrix 5 133 CFSG.Models.MatrixGroups.HN.rows2 *ᵥ
      (fun j : Fin 133 => (packedDigit 3 inputCode j.val : ZMod 5))) 0 =
        (packedDigit 3 intermediateCode 0 : ZMod 5) :=
  MatrixModelSelectedRowVectorReflection.coordinate_step 5 133 3
    CFSG.Models.MatrixGroups.HN.rows2 0 secondRowCode inputCode intermediateCode
    second_row_binding second_check

theorem first_selected_coordinate :
    (CFSG.Models.MatrixData.matrix 5 133 CFSG.Models.MatrixGroups.HN.rows1 *ᵥ
      (fun j : Fin 133 => (packedDigit 3 intermediateCode j.val : ZMod 5))) 0 =
        (packedDigit 3 outputCode 0 : ZMod 5) :=
  MatrixModelSelectedRowVectorReflection.coordinate_step 5 133 3
    CFSG.Models.MatrixGroups.HN.rows1 0 firstRowCode intermediateCode outputCode
    first_row_binding first_check

end SymmetricSubgroupAsymptotics.CFSGHNSelectedPrimeElevenRowZeroPilot
