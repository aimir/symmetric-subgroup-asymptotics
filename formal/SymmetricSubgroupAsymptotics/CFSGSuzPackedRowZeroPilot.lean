import SymmetricSubgroupAsymptotics.External.CFSG.Models.MatrixGroups.Suz
import SymmetricSubgroupAsymptotics.MatrixNaturalRowDotReflection

/-! ONE selected Suz ROW0 / COLUMN0 scalar pilot. The128 selected literal
digits and packed codes are UNTRUSTED DATA until the four binding proofs
and one scalar Nat-mod proof below pass. No full vector-return, matrix
square, parity or other-row assertion is made. Original source SHAf38e6896561efb319e20bb19b296784ef2b349b7d0d5768be37d64feee6ac3db.
No resource option is raised. -/
set_option autoImplicit false
set_option Elab.async false
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGSuzPackedRowZeroPilot
open MatrixNaturalRowDotReflection

def a : Matrix (Fin 64) (Fin 64) (ZMod 3) :=
  CFSG.Models.MatrixData.matrix 3 64 CFSG.Models.MatrixGroups.Suz.rows1

def rowDigit (j : ℕ) : ℕ :=
  match j with
  | 0 => 2
  | 1 => 0
  | 2 => 0
  | 3 => 2
  | 4 => 1
  | 5 => 0
  | 6 => 0
  | 7 => 2
  | 8 => 2
  | 9 => 0
  | 10 => 2
  | 11 => 2
  | 12 => 1
  | 13 => 1
  | 14 => 2
  | 15 => 1
  | 16 => 2
  | 17 => 1
  | 18 => 1
  | 19 => 0
  | 20 => 2
  | 21 => 1
  | 22 => 0
  | 23 => 0
  | 24 => 0
  | 25 => 1
  | 26 => 2
  | 27 => 1
  | 28 => 2
  | 29 => 1
  | 30 => 1
  | 31 => 0
  | 32 => 2
  | 33 => 0
  | 34 => 2
  | 35 => 0
  | 36 => 1
  | 37 => 1
  | 38 => 0
  | 39 => 1
  | 40 => 2
  | 41 => 1
  | 42 => 2
  | 43 => 0
  | 44 => 2
  | 45 => 2
  | 46 => 0
  | 47 => 2
  | 48 => 1
  | 49 => 0
  | 50 => 0
  | 51 => 2
  | 52 => 2
  | 53 => 2
  | 54 => 1
  | 55 => 2
  | 56 => 2
  | 57 => 1
  | 58 => 2
  | 59 => 2
  | 60 => 0
  | 61 => 2
  | 62 => 2
  | 63 => 2
  | _ => 0

def columnDigit (j : ℕ) : ℕ :=
  match j with
  | 0 => 2
  | 1 => 1
  | 2 => 2
  | 3 => 1
  | 4 => 1
  | 5 => 1
  | 6 => 0
  | 7 => 1
  | 8 => 1
  | 9 => 2
  | 10 => 0
  | 11 => 1
  | 12 => 0
  | 13 => 1
  | 14 => 1
  | 15 => 1
  | 16 => 0
  | 17 => 0
  | 18 => 1
  | 19 => 0
  | 20 => 2
  | 21 => 1
  | 22 => 0
  | 23 => 0
  | 24 => 2
  | 25 => 0
  | 26 => 1
  | 27 => 2
  | 28 => 0
  | 29 => 0
  | 30 => 2
  | 31 => 0
  | 32 => 1
  | 33 => 2
  | 34 => 2
  | 35 => 0
  | 36 => 0
  | 37 => 0
  | 38 => 0
  | 39 => 2
  | 40 => 1
  | 41 => 1
  | 42 => 0
  | 43 => 0
  | 44 => 2
  | 45 => 0
  | 46 => 1
  | 47 => 0
  | 48 => 0
  | 49 => 1
  | 50 => 1
  | 51 => 0
  | 52 => 1
  | 53 => 0
  | 54 => 1
  | 55 => 2
  | 56 => 1
  | 57 => 0
  | 58 => 2
  | 59 => 1
  | 60 => 0
  | 61 => 0
  | 62 => 0
  | 63 => 1
  | _ => 0

def rowCode : ℕ := 224175358324649771740101499125688861058

def columnCode : ℕ := 85577187065045653950764877966807221606

theorem raw_row_binding : ∀ j : Fin 64,
    rawDigit CFSG.Models.MatrixGroups.Suz.rows1 0 j.val = rowDigit j.val := by
  decide +kernel

theorem raw_column_binding : ∀ j : Fin 64,
    rawDigit CFSG.Models.MatrixGroups.Suz.rows1 j.val 0 = columnDigit j.val := by
  decide +kernel

theorem packed_row_binding : ∀ j : Fin 64,
    packedDigit 2 rowCode j.val = rowDigit j.val := by
  decide +kernel

theorem packed_column_binding : ∀ j : Fin 64,
    packedDigit 2 columnCode j.val = columnDigit j.val := by
  decide +kernel

theorem scalar_check : packedDot 2 rowCode columnCode 64 % 3 = 1 % 3 := by
  decide +kernel

theorem actual_row_zero_dot : (a *ᵥ (fun j => a j 0)) (0 : Fin 64) = 1 := by
  apply selected_packed_row_dot_mod 3 64 2 CFSG.Models.MatrixGroups.Suz.rows1
    (0 : Fin 64) (0 : Fin 64) rowCode columnCode 1
  · intro j
    exact (raw_row_binding j).trans (packed_row_binding j).symm
  · intro j
    exact (raw_column_binding j).trans (packed_column_binding j).symm
  · exact scalar_check

theorem selected_basis_two_step_coordinate :
    (a *ᵥ (a *ᵥ Pi.single (0 : Fin 64) 1)) (0 : Fin 64) = 1 := by
  rw [Matrix.mulVec_single_one]
  exact actual_row_zero_dot

end SymmetricSubgroupAsymptotics.CFSGSuzPackedRowZeroPilot
