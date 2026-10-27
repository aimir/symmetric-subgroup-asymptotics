import SymmetricSubgroupAsymptotics.MatrixNaturalRowPowerReflection
import SymmetricSubgroupAsymptotics.External.CFSG.Models.MatrixGroups.Ru

/-! ONE selected row of the literal second Ru matrix's fourth power.
No whole-matrix order or generated-group claim is made. -/
set_option autoImplicit false
set_option Elab.async false
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGRuSelectedSecondFourthRowPilot
open MatrixNaturalRowDotReflection MatrixNaturalRowPowerReflection
open CFSG.Models.MatrixGroups.Ru

def columnCode (z : ℕ) : ℕ :=
  match z with
  | 0 => 24181201
  | 1 => 42178627
  | 2 => 226564608
  | 3 => 235660812
  | 4 => 57200657
  | 5 => 167319035
  | 6 => 258976326
  | 7 => 174436173
  | 8 => 253457895
  | 9 => 148421893
  | 10 => 158400283
  | 11 => 157915943
  | 12 => 72554760
  | 13 => 249170222
  | 14 => 177831114
  | 15 => 80778771
  | 16 => 17606894
  | 17 => 63128121
  | 18 => 85935930
  | 19 => 41845913
  | 20 => 106703638
  | 21 => 153683428
  | 22 => 227845227
  | 23 => 123212474
  | 24 => 159440004
  | 25 => 151730701
  | 26 => 158227288
  | 27 => 82602401
  | _ => 0

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 1
  | 1 => 172658611
  | 2 => 151707853
  | 3 => 206988465
  | 4 => 1
  | _ => 0

def rowVector (k : ℕ) (z : Fin 28) : ZMod 2 := packedDigit 1 (stageCode k) z.val

theorem source_column_binding : ∀ (z j : Fin 28),
    rawDigit rows2 j.val z.val = packedDigit 1 (columnCode z.val) j.val := by
  decide +kernel

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 28),
    packedDot 1 (stageCode k.val) (columnCode z.val) 28 % 2 =
      packedDigit 1 (stageCode (k.val+1)) z.val % 2 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 28,
    rowVector 0 z = (1 : Matrix (Fin 28) (Fin 28) (ZMod 2)) 0 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 28) :
    rowVector (k+1) z = ∑ j : Fin 28,
      rowVector k j * CFSG.Models.MatrixData.matrix 2 28 rows2 j z := by
  exact (packed_row_step 2 28 1 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 28) :
    (CFSG.Models.MatrixData.matrix 2 28 rows2 ^ 4) 0 z = rowVector 4 z :=
  matrix_pow_row_eq 2 28 rows2 0 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 28,
    rowVector 4 z = (1 : Matrix (Fin 28) (Fin 28) (ZMod 2)) 0 z := by
  decide +kernel

theorem selected_fourth_power_row_identity (z : Fin 28) :
    (CFSG.Models.MatrixData.matrix 2 28 rows2 ^ 4) 0 z =
      (1 : Matrix (Fin 28) (Fin 28) (ZMod 2)) 0 z :=
  (fourth_power_row z).trans (selected_row_return z)

end SymmetricSubgroupAsymptotics.CFSGRuSelectedSecondFourthRowPilot
