import SymmetricSubgroupAsymptotics.MatrixModelSelectedRowVectorReflection
import SymmetricSubgroupAsymptotics.External.CFSG.Models.MatrixGroups.Th

/-! ONEnew-size selected pilot: original Th row0 of both matrices and
only two actual scalar outputs. No all-row binding or period is claimed. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGThSelectedPrimeNineteenRowZeroPilot
open MatrixNaturalRowDotReflection MatrixModelSelectedPointPeriodTwo

def firstRowCode : ℕ := 1
def secondRowCode : ℕ := 118705464191563021950720153070198904118039684779233554314569048872841816574959061692653979929854157416174753963783344250441230323632344465244912903834
def inputCode : ℕ := 1
def intermediateCode : ℕ := 132194567976583906343477102509765253479568101945452561448264081755945636681730269686894952491457954813553557609244207610114164184985518257900608853010
def outputCode : ℕ := 72256987367372167096361907495877882064050084301285519115818100852958134969089212775555098994229796753459080656574035343356842181839857802999504606226

theorem first_row_binding : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows1 0 j.val = packedDigit 2 firstRowCode j.val := by
  decide +kernel

theorem second_row_binding : ∀ j : Fin 248,
    rawDigit CFSG.Models.MatrixGroups.Th.rows2 0 j.val = packedDigit 2 secondRowCode j.val := by
  decide +kernel

private theorem second_check : packedDot 2 secondRowCode inputCode 248 % 3 =
    packedDigit 2 intermediateCode 0 % 3 := by decide +kernel
private theorem first_check : packedDot 2 firstRowCode intermediateCode 248 % 3 =
    packedDigit 2 outputCode 0 % 3 := by decide +kernel

theorem second_selected_coordinate :
    (CFSG.Models.MatrixData.matrix 3 248 CFSG.Models.MatrixGroups.Th.rows2 *ᵥ
      (fun j : Fin 248 => (packedDigit 2 inputCode j.val : ZMod 3))) 0 =
        (packedDigit 2 intermediateCode 0 : ZMod 3) :=
  MatrixModelSelectedRowVectorReflection.coordinate_step 3 248 2
    CFSG.Models.MatrixGroups.Th.rows2 0 secondRowCode inputCode intermediateCode
    second_row_binding second_check

theorem first_selected_coordinate :
    (CFSG.Models.MatrixData.matrix 3 248 CFSG.Models.MatrixGroups.Th.rows1 *ᵥ
      (fun j : Fin 248 => (packedDigit 2 intermediateCode j.val : ZMod 3))) 0 =
        (packedDigit 2 outputCode 0 : ZMod 3) :=
  MatrixModelSelectedRowVectorReflection.coordinate_step 3 248 2
    CFSG.Models.MatrixGroups.Th.rows1 0 firstRowCode intermediateCode outputCode
    first_row_binding first_check

end SymmetricSubgroupAsymptotics.CFSGThSelectedPrimeNineteenRowZeroPilot
