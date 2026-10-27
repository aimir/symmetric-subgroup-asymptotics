import SymmetricSubgroupAsymptotics.MatrixModelSelectedRowVectorReflection
import SymmetricSubgroupAsymptotics.External.CFSG.Models.MatrixGroups.Ly

/-! ONE111/F5 row0 pilot. Ly word column order starts B,B,A: the B
coordinate uses stages0→1; the A coordinate uses stages2→3. No period. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGLySelectedPrimeSixtySevenRowZeroPilot
open MatrixNaturalRowDotReflection MatrixModelSelectedPointPeriodTwo

def firstRowCode : ℕ := 93536104789177786765035829293842113257979682750466
def secondRowCode : ℕ := 3432682698532952906075760833953120748567226233045377546430521167098176099266967286545100276293780636
def firstInputCode : ℕ := 895213546598047933517728163727707062516166735454477890124197729726327206665196370695632884765176899
def firstOutputCode : ℕ := 667108399672918236875133418376304302957298532082368627338138196142021073279600420799087505494263556
def secondInputCode : ℕ := 1
def secondOutputCode : ℕ := 5617929917005061912200133370811091725735753571859787975593099562983105343750785668469584767495063308

theorem first_row_binding : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows1 0 j.val=packedDigit 3 firstRowCode j.val := by decide +kernel

theorem second_row_binding : ∀ j : Fin 111,
    rawDigit CFSG.Models.MatrixGroups.Ly.rows2 0 j.val=packedDigit 3 secondRowCode j.val := by decide +kernel

private theorem first_check : packedDot 3 firstRowCode firstInputCode 111 % 5=
    packedDigit 3 firstOutputCode 0 % 5 := by decide +kernel
private theorem second_check : packedDot 3 secondRowCode secondInputCode 111 % 5=
    packedDigit 3 secondOutputCode 0 % 5 := by decide +kernel

theorem first_selected_coordinate :
    (CFSG.Models.MatrixData.matrix 5 111 CFSG.Models.MatrixGroups.Ly.rows1 *ᵥ
      (fun j : Fin 111 => (packedDigit 3 firstInputCode j.val : ZMod 5))) 0=
        (packedDigit 3 firstOutputCode 0 : ZMod 5) :=
  MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3
    CFSG.Models.MatrixGroups.Ly.rows1 0 firstRowCode firstInputCode firstOutputCode first_row_binding first_check

theorem second_selected_coordinate :
    (CFSG.Models.MatrixData.matrix 5 111 CFSG.Models.MatrixGroups.Ly.rows2 *ᵥ
      (fun j : Fin 111 => (packedDigit 3 secondInputCode j.val : ZMod 5))) 0=
        (packedDigit 3 secondOutputCode 0 : ZMod 5) :=
  MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3
    CFSG.Models.MatrixGroups.Ly.rows2 0 secondRowCode secondInputCode secondOutputCode second_row_binding second_check

end SymmetricSubgroupAsymptotics.CFSGLySelectedPrimeSixtySevenRowZeroPilot
