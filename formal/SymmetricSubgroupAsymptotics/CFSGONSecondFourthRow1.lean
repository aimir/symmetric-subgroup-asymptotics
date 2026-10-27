import SymmetricSubgroupAsymptotics.CFSGONSelectedSecondFourthRowPilot

/-! ONE benchmark row1 of the SAME original ON B^4 over F3.
The checked column binding is reused; no new source-column certificate,
whole-matrix order or generated-group claim is introduced. -/
set_option autoImplicit false
set_option Elab.async false
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGONSecondFourthRow1
open MatrixNaturalRowDotReflection MatrixNaturalRowPowerReflection
open CFSG.Models.MatrixGroups.ON
open CFSGONSelectedSecondFourthRowPilot (columnCode source_column_binding)

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 4
  | 1 => 40
  | 2 => 532
  | 3 => 10
  | 4 => 4
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 1 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 1 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 1 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 1 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 1 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 1 z :=
  (fourth_power_row z).trans (selected_row_return z)

end SymmetricSubgroupAsymptotics.CFSGONSecondFourthRow1
