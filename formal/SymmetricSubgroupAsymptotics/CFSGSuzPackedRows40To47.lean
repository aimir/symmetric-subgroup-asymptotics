import SymmetricSubgroupAsymptotics.CFSGSuzPackedRowZeroPilot

/-! Exactly rows40 through47.
Generated from one hash-guarded first Suz matrix and its first column only.
Literal data require the closed kernel bindings and scalar checks below.
No resource limit is raised. The checked row-zero pilot supplies the shared
column and row-zero theorem; its source bytes are guarded by the producer. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGSuzPackedRows40To47
open MatrixNaturalRowDotReflection
open CFSGSuzPackedRowZeroPilot

def row40Digit (j : ℕ) : ℕ :=
  match j with
  | 0 => 1
  | 1 => 1
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => 2
  | 6 => 0
  | 7 => 0
  | 8 => 2
  | 9 => 1
  | 10 => 0
  | 11 => 0
  | 12 => 2
  | 13 => 2
  | 14 => 1
  | 15 => 2
  | 16 => 0
  | 17 => 0
  | 18 => 1
  | 19 => 0
  | 20 => 1
  | 21 => 2
  | 22 => 1
  | 23 => 2
  | 24 => 0
  | 25 => 2
  | 26 => 2
  | 27 => 2
  | 28 => 1
  | 29 => 1
  | 30 => 0
  | 31 => 2
  | 32 => 1
  | 33 => 1
  | 34 => 0
  | 35 => 1
  | 36 => 0
  | 37 => 1
  | 38 => 1
  | 39 => 0
  | 40 => 1
  | 41 => 0
  | 42 => 1
  | 43 => 1
  | 44 => 1
  | 45 => 0
  | 46 => 1
  | 47 => 0
  | 48 => 0
  | 49 => 1
  | 50 => 1
  | 51 => 0
  | 52 => 1
  | 53 => 0
  | 54 => 2
  | 55 => 0
  | 56 => 1
  | 57 => 1
  | 58 => 1
  | 59 => 2
  | 60 => 0
  | 61 => 2
  | 62 => 1
  | 63 => 0
  | _ => 0

def row40Code : ℕ := 32675795040199104944890921240003741701

theorem raw_row_40_binding : ∀ j : Fin 64,
    rawDigit CFSG.Models.MatrixGroups.Suz.rows1 40 j.val = row40Digit j.val := by
  decide +kernel

theorem packed_row_40_binding : ∀ j : Fin 64,
    packedDigit 2 row40Code j.val = row40Digit j.val := by
  decide +kernel

theorem scalar_40_check : packedDot 2 row40Code columnCode 64 % 3 = 0 % 3 := by
  decide +kernel

theorem actual_row_40_dot :
    (a *ᵥ (fun j => a j 0)) (40 : Fin 64) = 0 := by
  apply selected_packed_row_dot_mod 3 64 2 CFSG.Models.MatrixGroups.Suz.rows1
    (40 : Fin 64) (0 : Fin 64) row40Code columnCode 0
  · intro j
    exact (raw_row_40_binding j).trans (packed_row_40_binding j).symm
  · intro j
    exact (raw_column_binding j).trans (packed_column_binding j).symm
  · exact scalar_40_check

def row41Digit (j : ℕ) : ℕ :=
  match j with
  | 0 => 1
  | 1 => 0
  | 2 => 2
  | 3 => 1
  | 4 => 2
  | 5 => 2
  | 6 => 2
  | 7 => 2
  | 8 => 0
  | 9 => 1
  | 10 => 2
  | 11 => 2
  | 12 => 0
  | 13 => 2
  | 14 => 1
  | 15 => 1
  | 16 => 0
  | 17 => 1
  | 18 => 0
  | 19 => 2
  | 20 => 1
  | 21 => 2
  | 22 => 0
  | 23 => 0
  | 24 => 1
  | 25 => 2
  | 26 => 2
  | 27 => 1
  | 28 => 0
  | 29 => 2
  | 30 => 1
  | 31 => 1
  | 32 => 1
  | 33 => 0
  | 34 => 1
  | 35 => 1
  | 36 => 2
  | 37 => 1
  | 38 => 1
  | 39 => 2
  | 40 => 0
  | 41 => 2
  | 42 => 1
  | 43 => 0
  | 44 => 2
  | 45 => 2
  | 46 => 2
  | 47 => 2
  | 48 => 2
  | 49 => 2
  | 50 => 0
  | 51 => 0
  | 52 => 0
  | 53 => 0
  | 54 => 0
  | 55 => 0
  | 56 => 0
  | 57 => 2
  | 58 => 0
  | 59 => 0
  | 60 => 1
  | 61 => 1
  | 62 => 2
  | 63 => 1
  | _ => 0

def row41Code : ℕ := 134293566794068582671784879806969326177

theorem raw_row_41_binding : ∀ j : Fin 64,
    rawDigit CFSG.Models.MatrixGroups.Suz.rows1 41 j.val = row41Digit j.val := by
  decide +kernel

theorem packed_row_41_binding : ∀ j : Fin 64,
    packedDigit 2 row41Code j.val = row41Digit j.val := by
  decide +kernel

theorem scalar_41_check : packedDot 2 row41Code columnCode 64 % 3 = 0 % 3 := by
  decide +kernel

theorem actual_row_41_dot :
    (a *ᵥ (fun j => a j 0)) (41 : Fin 64) = 0 := by
  apply selected_packed_row_dot_mod 3 64 2 CFSG.Models.MatrixGroups.Suz.rows1
    (41 : Fin 64) (0 : Fin 64) row41Code columnCode 0
  · intro j
    exact (raw_row_41_binding j).trans (packed_row_41_binding j).symm
  · intro j
    exact (raw_column_binding j).trans (packed_column_binding j).symm
  · exact scalar_41_check

def row42Digit (j : ℕ) : ℕ :=
  match j with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 1
  | 4 => 1
  | 5 => 2
  | 6 => 1
  | 7 => 1
  | 8 => 0
  | 9 => 1
  | 10 => 1
  | 11 => 2
  | 12 => 0
  | 13 => 1
  | 14 => 2
  | 15 => 1
  | 16 => 2
  | 17 => 1
  | 18 => 1
  | 19 => 2
  | 20 => 2
  | 21 => 2
  | 22 => 2
  | 23 => 0
  | 24 => 1
  | 25 => 0
  | 26 => 2
  | 27 => 2
  | 28 => 2
  | 29 => 1
  | 30 => 0
  | 31 => 1
  | 32 => 0
  | 33 => 1
  | 34 => 2
  | 35 => 1
  | 36 => 0
  | 37 => 1
  | 38 => 1
  | 39 => 2
  | 40 => 1
  | 41 => 1
  | 42 => 0
  | 43 => 1
  | 44 => 0
  | 45 => 1
  | 46 => 1
  | 47 => 1
  | 48 => 2
  | 49 => 2
  | 50 => 2
  | 51 => 0
  | 52 => 2
  | 53 => 0
  | 54 => 1
  | 55 => 1
  | 56 => 1
  | 57 => 2
  | 58 => 2
  | 59 => 0
  | 60 => 2
  | 61 => 0
  | 62 => 0
  | 63 => 0
  | _ => 0

def row42Code : ℕ := 2873006674020942181203970217219479908

theorem raw_row_42_binding : ∀ j : Fin 64,
    rawDigit CFSG.Models.MatrixGroups.Suz.rows1 42 j.val = row42Digit j.val := by
  decide +kernel

theorem packed_row_42_binding : ∀ j : Fin 64,
    packedDigit 2 row42Code j.val = row42Digit j.val := by
  decide +kernel

theorem scalar_42_check : packedDot 2 row42Code columnCode 64 % 3 = 0 % 3 := by
  decide +kernel

theorem actual_row_42_dot :
    (a *ᵥ (fun j => a j 0)) (42 : Fin 64) = 0 := by
  apply selected_packed_row_dot_mod 3 64 2 CFSG.Models.MatrixGroups.Suz.rows1
    (42 : Fin 64) (0 : Fin 64) row42Code columnCode 0
  · intro j
    exact (raw_row_42_binding j).trans (packed_row_42_binding j).symm
  · intro j
    exact (raw_column_binding j).trans (packed_column_binding j).symm
  · exact scalar_42_check

def row43Digit (j : ℕ) : ℕ :=
  match j with
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 2
  | 4 => 2
  | 5 => 2
  | 6 => 0
  | 7 => 2
  | 8 => 1
  | 9 => 0
  | 10 => 0
  | 11 => 1
  | 12 => 2
  | 13 => 2
  | 14 => 0
  | 15 => 2
  | 16 => 0
  | 17 => 2
  | 18 => 1
  | 19 => 1
  | 20 => 1
  | 21 => 2
  | 22 => 2
  | 23 => 2
  | 24 => 1
  | 25 => 1
  | 26 => 2
  | 27 => 2
  | 28 => 0
  | 29 => 2
  | 30 => 2
  | 31 => 0
  | 32 => 2
  | 33 => 2
  | 34 => 1
  | 35 => 1
  | 36 => 2
  | 37 => 2
  | 38 => 0
  | 39 => 2
  | 40 => 1
  | 41 => 2
  | 42 => 1
  | 43 => 1
  | 44 => 1
  | 45 => 1
  | 46 => 1
  | 47 => 0
  | 48 => 2
  | 49 => 0
  | 50 => 1
  | 51 => 0
  | 52 => 2
  | 53 => 2
  | 54 => 0
  | 55 => 2
  | 56 => 1
  | 57 => 1
  | 58 => 1
  | 59 => 1
  | 60 => 1
  | 61 => 0
  | 62 => 1
  | 63 => 0
  | _ => 0

def row43Code : ℕ := 23041021566558692328970878032302672512

theorem raw_row_43_binding : ∀ j : Fin 64,
    rawDigit CFSG.Models.MatrixGroups.Suz.rows1 43 j.val = row43Digit j.val := by
  decide +kernel

theorem packed_row_43_binding : ∀ j : Fin 64,
    packedDigit 2 row43Code j.val = row43Digit j.val := by
  decide +kernel

theorem scalar_43_check : packedDot 2 row43Code columnCode 64 % 3 = 0 % 3 := by
  decide +kernel

theorem actual_row_43_dot :
    (a *ᵥ (fun j => a j 0)) (43 : Fin 64) = 0 := by
  apply selected_packed_row_dot_mod 3 64 2 CFSG.Models.MatrixGroups.Suz.rows1
    (43 : Fin 64) (0 : Fin 64) row43Code columnCode 0
  · intro j
    exact (raw_row_43_binding j).trans (packed_row_43_binding j).symm
  · intro j
    exact (raw_column_binding j).trans (packed_column_binding j).symm
  · exact scalar_43_check

def row44Digit (j : ℕ) : ℕ :=
  match j with
  | 0 => 2
  | 1 => 2
  | 2 => 2
  | 3 => 0
  | 4 => 1
  | 5 => 2
  | 6 => 1
  | 7 => 0
  | 8 => 0
  | 9 => 0
  | 10 => 1
  | 11 => 1
  | 12 => 0
  | 13 => 1
  | 14 => 2
  | 15 => 0
  | 16 => 2
  | 17 => 2
  | 18 => 2
  | 19 => 1
  | 20 => 1
  | 21 => 0
  | 22 => 2
  | 23 => 0
  | 24 => 1
  | 25 => 1
  | 26 => 2
  | 27 => 1
  | 28 => 0
  | 29 => 2
  | 30 => 2
  | 31 => 2
  | 32 => 2
  | 33 => 2
  | 34 => 0
  | 35 => 0
  | 36 => 0
  | 37 => 1
  | 38 => 2
  | 39 => 2
  | 40 => 2
  | 41 => 0
  | 42 => 2
  | 43 => 2
  | 44 => 2
  | 45 => 1
  | 46 => 1
  | 47 => 1
  | 48 => 2
  | 49 => 2
  | 50 => 2
  | 51 => 2
  | 52 => 0
  | 53 => 2
  | 54 => 0
  | 55 => 1
  | 56 => 0
  | 57 => 1
  | 58 => 0
  | 59 => 2
  | 60 => 0
  | 61 => 0
  | 62 => 1
  | 63 => 1
  | _ => 0

def row44Code : ℕ := 107025096677211288916596524148772051242

theorem raw_row_44_binding : ∀ j : Fin 64,
    rawDigit CFSG.Models.MatrixGroups.Suz.rows1 44 j.val = row44Digit j.val := by
  decide +kernel

theorem packed_row_44_binding : ∀ j : Fin 64,
    packedDigit 2 row44Code j.val = row44Digit j.val := by
  decide +kernel

theorem scalar_44_check : packedDot 2 row44Code columnCode 64 % 3 = 0 % 3 := by
  decide +kernel

theorem actual_row_44_dot :
    (a *ᵥ (fun j => a j 0)) (44 : Fin 64) = 0 := by
  apply selected_packed_row_dot_mod 3 64 2 CFSG.Models.MatrixGroups.Suz.rows1
    (44 : Fin 64) (0 : Fin 64) row44Code columnCode 0
  · intro j
    exact (raw_row_44_binding j).trans (packed_row_44_binding j).symm
  · intro j
    exact (raw_column_binding j).trans (packed_column_binding j).symm
  · exact scalar_44_check

def row45Digit (j : ℕ) : ℕ :=
  match j with
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 0
  | 4 => 1
  | 5 => 0
  | 6 => 0
  | 7 => 1
  | 8 => 0
  | 9 => 0
  | 10 => 1
  | 11 => 0
  | 12 => 2
  | 13 => 0
  | 14 => 2
  | 15 => 2
  | 16 => 1
  | 17 => 1
  | 18 => 1
  | 19 => 0
  | 20 => 2
  | 21 => 2
  | 22 => 0
  | 23 => 0
  | 24 => 0
  | 25 => 1
  | 26 => 2
  | 27 => 2
  | 28 => 2
  | 29 => 2
  | 30 => 2
  | 31 => 1
  | 32 => 1
  | 33 => 2
  | 34 => 2
  | 35 => 0
  | 36 => 0
  | 37 => 1
  | 38 => 1
  | 39 => 2
  | 40 => 0
  | 41 => 2
  | 42 => 2
  | 43 => 2
  | 44 => 0
  | 45 => 0
  | 46 => 2
  | 47 => 0
  | 48 => 1
  | 49 => 2
  | 50 => 0
  | 51 => 0
  | 52 => 1
  | 53 => 1
  | 54 => 0
  | 55 => 2
  | 56 => 2
  | 57 => 2
  | 58 => 2
  | 59 => 2
  | 60 => 0
  | 61 => 2
  | 62 => 2
  | 63 => 0
  | _ => 0

def row45Code : ℕ := 54054508580985623439766439695855141136

theorem raw_row_45_binding : ∀ j : Fin 64,
    rawDigit CFSG.Models.MatrixGroups.Suz.rows1 45 j.val = row45Digit j.val := by
  decide +kernel

theorem packed_row_45_binding : ∀ j : Fin 64,
    packedDigit 2 row45Code j.val = row45Digit j.val := by
  decide +kernel

theorem scalar_45_check : packedDot 2 row45Code columnCode 64 % 3 = 0 % 3 := by
  decide +kernel

theorem actual_row_45_dot :
    (a *ᵥ (fun j => a j 0)) (45 : Fin 64) = 0 := by
  apply selected_packed_row_dot_mod 3 64 2 CFSG.Models.MatrixGroups.Suz.rows1
    (45 : Fin 64) (0 : Fin 64) row45Code columnCode 0
  · intro j
    exact (raw_row_45_binding j).trans (packed_row_45_binding j).symm
  · intro j
    exact (raw_column_binding j).trans (packed_column_binding j).symm
  · exact scalar_45_check

def row46Digit (j : ℕ) : ℕ :=
  match j with
  | 0 => 1
  | 1 => 0
  | 2 => 2
  | 3 => 1
  | 4 => 0
  | 5 => 0
  | 6 => 1
  | 7 => 0
  | 8 => 0
  | 9 => 0
  | 10 => 0
  | 11 => 1
  | 12 => 1
  | 13 => 0
  | 14 => 1
  | 15 => 0
  | 16 => 2
  | 17 => 2
  | 18 => 1
  | 19 => 1
  | 20 => 1
  | 21 => 1
  | 22 => 2
  | 23 => 2
  | 24 => 1
  | 25 => 0
  | 26 => 1
  | 27 => 0
  | 28 => 2
  | 29 => 0
  | 30 => 0
  | 31 => 0
  | 32 => 2
  | 33 => 1
  | 34 => 0
  | 35 => 1
  | 36 => 2
  | 37 => 2
  | 38 => 2
  | 39 => 0
  | 40 => 0
  | 41 => 1
  | 42 => 1
  | 43 => 1
  | 44 => 2
  | 45 => 0
  | 46 => 0
  | 47 => 0
  | 48 => 0
  | 49 => 2
  | 50 => 0
  | 51 => 0
  | 52 => 0
  | 53 => 1
  | 54 => 2
  | 55 => 0
  | 56 => 1
  | 57 => 1
  | 58 => 0
  | 59 => 1
  | 60 => 0
  | 61 => 1
  | 62 => 1
  | 63 => 2
  | _ => 0

def row46Code : ℕ := 197084742660698203289685778759432540257

theorem raw_row_46_binding : ∀ j : Fin 64,
    rawDigit CFSG.Models.MatrixGroups.Suz.rows1 46 j.val = row46Digit j.val := by
  decide +kernel

theorem packed_row_46_binding : ∀ j : Fin 64,
    packedDigit 2 row46Code j.val = row46Digit j.val := by
  decide +kernel

theorem scalar_46_check : packedDot 2 row46Code columnCode 64 % 3 = 0 % 3 := by
  decide +kernel

theorem actual_row_46_dot :
    (a *ᵥ (fun j => a j 0)) (46 : Fin 64) = 0 := by
  apply selected_packed_row_dot_mod 3 64 2 CFSG.Models.MatrixGroups.Suz.rows1
    (46 : Fin 64) (0 : Fin 64) row46Code columnCode 0
  · intro j
    exact (raw_row_46_binding j).trans (packed_row_46_binding j).symm
  · intro j
    exact (raw_column_binding j).trans (packed_column_binding j).symm
  · exact scalar_46_check

def row47Digit (j : ℕ) : ℕ :=
  match j with
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 2
  | 4 => 2
  | 5 => 2
  | 6 => 1
  | 7 => 1
  | 8 => 1
  | 9 => 0
  | 10 => 1
  | 11 => 1
  | 12 => 1
  | 13 => 1
  | 14 => 2
  | 15 => 2
  | 16 => 0
  | 17 => 2
  | 18 => 2
  | 19 => 2
  | 20 => 1
  | 21 => 2
  | 22 => 1
  | 23 => 2
  | 24 => 2
  | 25 => 0
  | 26 => 1
  | 27 => 0
  | 28 => 2
  | 29 => 1
  | 30 => 1
  | 31 => 2
  | 32 => 1
  | 33 => 2
  | 34 => 1
  | 35 => 1
  | 36 => 1
  | 37 => 2
  | 38 => 1
  | 39 => 0
  | 40 => 0
  | 41 => 2
  | 42 => 1
  | 43 => 0
  | 44 => 0
  | 45 => 2
  | 46 => 1
  | 47 => 1
  | 48 => 0
  | 49 => 2
  | 50 => 1
  | 51 => 1
  | 52 => 0
  | 53 => 1
  | 54 => 1
  | 55 => 2
  | 56 => 0
  | 57 => 2
  | 58 => 1
  | 59 => 1
  | 60 => 0
  | 61 => 2
  | 62 => 0
  | 63 => 1
  | _ => 0

def row47Code : ℕ := 96164346616028464178554530496345365136

theorem raw_row_47_binding : ∀ j : Fin 64,
    rawDigit CFSG.Models.MatrixGroups.Suz.rows1 47 j.val = row47Digit j.val := by
  decide +kernel

theorem packed_row_47_binding : ∀ j : Fin 64,
    packedDigit 2 row47Code j.val = row47Digit j.val := by
  decide +kernel

theorem scalar_47_check : packedDot 2 row47Code columnCode 64 % 3 = 0 % 3 := by
  decide +kernel

theorem actual_row_47_dot :
    (a *ᵥ (fun j => a j 0)) (47 : Fin 64) = 0 := by
  apply selected_packed_row_dot_mod 3 64 2 CFSG.Models.MatrixGroups.Suz.rows1
    (47 : Fin 64) (0 : Fin 64) row47Code columnCode 0
  · intro j
    exact (raw_row_47_binding j).trans (packed_row_47_binding j).symm
  · intro j
    exact (raw_column_binding j).trans (packed_column_binding j).symm
  · exact scalar_47_check

end SymmetricSubgroupAsymptotics.CFSGSuzPackedRows40To47
