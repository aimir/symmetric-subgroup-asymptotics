import SymmetricSubgroupAsymptotics.CFSGRuSelectedSecondFourthRowPilot

/-! ONE selected row18 of the original B^4;
no other power row or generated-group conclusion is asserted. -/
set_option autoImplicit false
set_option Elab.async false
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGRuSecondFourthRow18
open MatrixNaturalRowDotReflection MatrixNaturalRowPowerReflection
open CFSG.Models.MatrixGroups.Ru
open CFSGRuSelectedSecondFourthRowPilot (columnCode source_column_binding)

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 262144
  | 1 => 207421632
  | 2 => 251438564
  | 3 => 79446260
  | 4 => 262144
  | _ => 0

def rowVector (k : ℕ) (z : Fin 28) : ZMod 2 := packedDigit 1 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 28),
    packedDot 1 (stageCode k.val) (columnCode z.val) 28 % 2 =
      packedDigit 1 (stageCode (k.val+1)) z.val % 2 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 28,
    rowVector 0 z = (1 : Matrix (Fin 28) (Fin 28) (ZMod 2)) 18 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 28) :
    rowVector (k+1) z = ∑ j : Fin 28,
      rowVector k j * CFSG.Models.MatrixData.matrix 2 28 rows2 j z := by
  exact (packed_row_step 2 28 1 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem row_power (z : Fin 28) :
    (CFSG.Models.MatrixData.matrix 2 28 rows2 ^ 4) 18 z = rowVector 4 z :=
  matrix_pow_row_eq 2 28 rows2 18 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 28,
    rowVector 4 z = (1 : Matrix (Fin 28) (Fin 28) (ZMod 2)) 18 z := by
  decide +kernel

theorem row_identity (z : Fin 28) :
    (CFSG.Models.MatrixData.matrix 2 28 rows2 ^ 4) 18 z =
      (1 : Matrix (Fin 28) (Fin 28) (ZMod 2)) 18 z :=
  (row_power z).trans (selected_row_return z)

end SymmetricSubgroupAsymptotics.CFSGRuSecondFourthRow18
