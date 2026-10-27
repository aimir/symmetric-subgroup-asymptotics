import SymmetricSubgroupAsymptotics.CFSGSuzPackedRowZeroPilot

/-! Exactly rows56 through63.
Generated from one hash-guarded first Suz matrix and its first column only.
Literal data require the closed kernel bindings and scalar checks below.
No resource limit is raised. The checked row-zero pilot supplies the shared
column and row-zero theorem; its source bytes are guarded by the producer. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGSuzPackedRows56To63
open MatrixNaturalRowDotReflection
open CFSGSuzPackedRowZeroPilot

def row56Digit (j : ℕ) : ℕ :=
  match j with
  | 0 => 1
  | 1 => 2
  | 2 => 1
  | 3 => 0
  | 4 => 0
  | 5 => 1
  | 6 => 0
  | 7 => 0
  | 8 => 1
  | 9 => 0
  | 10 => 1
  | 11 => 2
  | 12 => 1
  | 13 => 0
  | 14 => 1
  | 15 => 1
  | 16 => 2
  | 17 => 1
  | 18 => 2
  | 19 => 2
  | 20 => 0
  | 21 => 0
  | 22 => 0
  | 23 => 0
  | 24 => 1
  | 25 => 2
  | 26 => 1
  | 27 => 1
  | 28 => 2
  | 29 => 2
  | 30 => 2
  | 31 => 0
  | 32 => 1
  | 33 => 0
  | 34 => 1
  | 35 => 1
  | 36 => 1
  | 37 => 1
  | 38 => 1
  | 39 => 1
  | 40 => 1
  | 41 => 0
  | 42 => 0
  | 43 => 1
  | 44 => 2
  | 45 => 0
  | 46 => 1
  | 47 => 0
  | 48 => 1
  | 49 => 1
  | 50 => 0
  | 51 => 2
  | 52 => 1
  | 53 => 2
  | 54 => 1
  | 55 => 1
  | 56 => 1
  | 57 => 0
  | 58 => 1
  | 59 => 1
  | 60 => 1
  | 61 => 1
  | 62 => 0
  | 63 => 2
  | _ => 0

def row56Code : ℕ := 177209715162385184783389887427234563097

theorem raw_row_56_binding : ∀ j : Fin 64,
    rawDigit CFSG.Models.MatrixGroups.Suz.rows1 56 j.val = row56Digit j.val := by
  decide +kernel

theorem packed_row_56_binding : ∀ j : Fin 64,
    packedDigit 2 row56Code j.val = row56Digit j.val := by
  decide +kernel

theorem scalar_56_check : packedDot 2 row56Code columnCode 64 % 3 = 0 % 3 := by
  decide +kernel

theorem actual_row_56_dot :
    (a *ᵥ (fun j => a j 0)) (56 : Fin 64) = 0 := by
  apply selected_packed_row_dot_mod 3 64 2 CFSG.Models.MatrixGroups.Suz.rows1
    (56 : Fin 64) (0 : Fin 64) row56Code columnCode 0
  · intro j
    exact (raw_row_56_binding j).trans (packed_row_56_binding j).symm
  · intro j
    exact (raw_column_binding j).trans (packed_column_binding j).symm
  · exact scalar_56_check

def row57Digit (j : ℕ) : ℕ :=
  match j with
  | 0 => 0
  | 1 => 1
  | 2 => 0
  | 3 => 1
  | 4 => 0
  | 5 => 1
  | 6 => 2
  | 7 => 1
  | 8 => 0
  | 9 => 2
  | 10 => 0
  | 11 => 1
  | 12 => 0
  | 13 => 1
  | 14 => 2
  | 15 => 2
  | 16 => 2
  | 17 => 0
  | 18 => 2
  | 19 => 2
  | 20 => 2
  | 21 => 0
  | 22 => 0
  | 23 => 2
  | 24 => 0
  | 25 => 2
  | 26 => 2
  | 27 => 1
  | 28 => 2
  | 29 => 2
  | 30 => 2
  | 31 => 1
  | 32 => 0
  | 33 => 2
  | 34 => 1
  | 35 => 2
  | 36 => 2
  | 37 => 2
  | 38 => 0
  | 39 => 1
  | 40 => 2
  | 41 => 2
  | 42 => 2
  | 43 => 1
  | 44 => 0
  | 45 => 1
  | 46 => 1
  | 47 => 0
  | 48 => 1
  | 49 => 1
  | 50 => 0
  | 51 => 1
  | 52 => 1
  | 53 => 2
  | 54 => 1
  | 55 => 1
  | 56 => 1
  | 57 => 1
  | 58 => 1
  | 59 => 2
  | 60 => 0
  | 61 => 0
  | 62 => 1
  | 63 => 0
  | _ => 0

def row57Code : ℕ := 22043110771996480366017387802699260996

theorem raw_row_57_binding : ∀ j : Fin 64,
    rawDigit CFSG.Models.MatrixGroups.Suz.rows1 57 j.val = row57Digit j.val := by
  decide +kernel

theorem packed_row_57_binding : ∀ j : Fin 64,
    packedDigit 2 row57Code j.val = row57Digit j.val := by
  decide +kernel

theorem scalar_57_check : packedDot 2 row57Code columnCode 64 % 3 = 0 % 3 := by
  decide +kernel

theorem actual_row_57_dot :
    (a *ᵥ (fun j => a j 0)) (57 : Fin 64) = 0 := by
  apply selected_packed_row_dot_mod 3 64 2 CFSG.Models.MatrixGroups.Suz.rows1
    (57 : Fin 64) (0 : Fin 64) row57Code columnCode 0
  · intro j
    exact (raw_row_57_binding j).trans (packed_row_57_binding j).symm
  · intro j
    exact (raw_column_binding j).trans (packed_column_binding j).symm
  · exact scalar_57_check

def row58Digit (j : ℕ) : ℕ :=
  match j with
  | 0 => 2
  | 1 => 0
  | 2 => 2
  | 3 => 1
  | 4 => 2
  | 5 => 1
  | 6 => 0
  | 7 => 1
  | 8 => 1
  | 9 => 1
  | 10 => 1
  | 11 => 0
  | 12 => 0
  | 13 => 1
  | 14 => 1
  | 15 => 1
  | 16 => 2
  | 17 => 1
  | 18 => 1
  | 19 => 1
  | 20 => 1
  | 21 => 1
  | 22 => 1
  | 23 => 2
  | 24 => 1
  | 25 => 0
  | 26 => 2
  | 27 => 2
  | 28 => 0
  | 29 => 2
  | 30 => 1
  | 31 => 0
  | 32 => 0
  | 33 => 1
  | 34 => 2
  | 35 => 1
  | 36 => 1
  | 37 => 0
  | 38 => 1
  | 39 => 0
  | 40 => 1
  | 41 => 1
  | 42 => 0
  | 43 => 0
  | 44 => 2
  | 45 => 0
  | 46 => 0
  | 47 => 2
  | 48 => 0
  | 49 => 1
  | 50 => 2
  | 51 => 0
  | 52 => 0
  | 53 => 0
  | 54 => 2
  | 55 => 1
  | 56 => 2
  | 57 => 2
  | 58 => 2
  | 59 => 2
  | 60 => 1
  | 61 => 2
  | 62 => 1
  | 63 => 0
  | _ => 0

def row58Code : ℕ := 34115340364348796625874625347871655522

theorem raw_row_58_binding : ∀ j : Fin 64,
    rawDigit CFSG.Models.MatrixGroups.Suz.rows1 58 j.val = row58Digit j.val := by
  decide +kernel

theorem packed_row_58_binding : ∀ j : Fin 64,
    packedDigit 2 row58Code j.val = row58Digit j.val := by
  decide +kernel

theorem scalar_58_check : packedDot 2 row58Code columnCode 64 % 3 = 0 % 3 := by
  decide +kernel

theorem actual_row_58_dot :
    (a *ᵥ (fun j => a j 0)) (58 : Fin 64) = 0 := by
  apply selected_packed_row_dot_mod 3 64 2 CFSG.Models.MatrixGroups.Suz.rows1
    (58 : Fin 64) (0 : Fin 64) row58Code columnCode 0
  · intro j
    exact (raw_row_58_binding j).trans (packed_row_58_binding j).symm
  · intro j
    exact (raw_column_binding j).trans (packed_column_binding j).symm
  · exact scalar_58_check

def row59Digit (j : ℕ) : ℕ :=
  match j with
  | 0 => 1
  | 1 => 1
  | 2 => 0
  | 3 => 1
  | 4 => 1
  | 5 => 0
  | 6 => 2
  | 7 => 0
  | 8 => 0
  | 9 => 0
  | 10 => 1
  | 11 => 0
  | 12 => 0
  | 13 => 2
  | 14 => 1
  | 15 => 2
  | 16 => 2
  | 17 => 0
  | 18 => 0
  | 19 => 2
  | 20 => 0
  | 21 => 1
  | 22 => 1
  | 23 => 1
  | 24 => 0
  | 25 => 2
  | 26 => 1
  | 27 => 2
  | 28 => 1
  | 29 => 0
  | 30 => 1
  | 31 => 0
  | 32 => 2
  | 33 => 0
  | 34 => 2
  | 35 => 1
  | 36 => 1
  | 37 => 2
  | 38 => 1
  | 39 => 0
  | 40 => 0
  | 41 => 0
  | 42 => 2
  | 43 => 0
  | 44 => 2
  | 45 => 1
  | 46 => 0
  | 47 => 2
  | 48 => 2
  | 49 => 0
  | 50 => 0
  | 51 => 2
  | 52 => 2
  | 53 => 1
  | 54 => 1
  | 55 => 1
  | 56 => 0
  | 57 => 2
  | 58 => 0
  | 59 => 0
  | 60 => 1
  | 61 => 0
  | 62 => 2
  | 63 => 0
  | _ => 0

def row59Code : ℕ := 43907816864167340135372978106565402949

theorem raw_row_59_binding : ∀ j : Fin 64,
    rawDigit CFSG.Models.MatrixGroups.Suz.rows1 59 j.val = row59Digit j.val := by
  decide +kernel

theorem packed_row_59_binding : ∀ j : Fin 64,
    packedDigit 2 row59Code j.val = row59Digit j.val := by
  decide +kernel

theorem scalar_59_check : packedDot 2 row59Code columnCode 64 % 3 = 0 % 3 := by
  decide +kernel

theorem actual_row_59_dot :
    (a *ᵥ (fun j => a j 0)) (59 : Fin 64) = 0 := by
  apply selected_packed_row_dot_mod 3 64 2 CFSG.Models.MatrixGroups.Suz.rows1
    (59 : Fin 64) (0 : Fin 64) row59Code columnCode 0
  · intro j
    exact (raw_row_59_binding j).trans (packed_row_59_binding j).symm
  · intro j
    exact (raw_column_binding j).trans (packed_column_binding j).symm
  · exact scalar_59_check

def row60Digit (j : ℕ) : ℕ :=
  match j with
  | 0 => 0
  | 1 => 2
  | 2 => 1
  | 3 => 2
  | 4 => 2
  | 5 => 2
  | 6 => 0
  | 7 => 2
  | 8 => 0
  | 9 => 1
  | 10 => 2
  | 11 => 2
  | 12 => 1
  | 13 => 1
  | 14 => 2
  | 15 => 0
  | 16 => 0
  | 17 => 1
  | 18 => 2
  | 19 => 0
  | 20 => 1
  | 21 => 0
  | 22 => 0
  | 23 => 2
  | 24 => 0
  | 25 => 2
  | 26 => 1
  | 27 => 1
  | 28 => 2
  | 29 => 0
  | 30 => 2
  | 31 => 1
  | 32 => 0
  | 33 => 2
  | 34 => 0
  | 35 => 1
  | 36 => 0
  | 37 => 1
  | 38 => 2
  | 39 => 1
  | 40 => 1
  | 41 => 1
  | 42 => 0
  | 43 => 1
  | 44 => 1
  | 45 => 1
  | 46 => 1
  | 47 => 2
  | 48 => 0
  | 49 => 1
  | 50 => 0
  | 51 => 0
  | 52 => 0
  | 53 => 0
  | 54 => 2
  | 55 => 0
  | 56 => 0
  | 57 => 2
  | 58 => 0
  | 59 => 0
  | 60 => 2
  | 61 => 1
  | 62 => 2
  | 63 => 1
  | _ => 0

def row60Code : ℕ := 135623443345146820484561721736019872408

theorem raw_row_60_binding : ∀ j : Fin 64,
    rawDigit CFSG.Models.MatrixGroups.Suz.rows1 60 j.val = row60Digit j.val := by
  decide +kernel

theorem packed_row_60_binding : ∀ j : Fin 64,
    packedDigit 2 row60Code j.val = row60Digit j.val := by
  decide +kernel

theorem scalar_60_check : packedDot 2 row60Code columnCode 64 % 3 = 0 % 3 := by
  decide +kernel

theorem actual_row_60_dot :
    (a *ᵥ (fun j => a j 0)) (60 : Fin 64) = 0 := by
  apply selected_packed_row_dot_mod 3 64 2 CFSG.Models.MatrixGroups.Suz.rows1
    (60 : Fin 64) (0 : Fin 64) row60Code columnCode 0
  · intro j
    exact (raw_row_60_binding j).trans (packed_row_60_binding j).symm
  · intro j
    exact (raw_column_binding j).trans (packed_column_binding j).symm
  · exact scalar_60_check

def row61Digit (j : ℕ) : ℕ :=
  match j with
  | 0 => 0
  | 1 => 1
  | 2 => 0
  | 3 => 1
  | 4 => 0
  | 5 => 2
  | 6 => 2
  | 7 => 0
  | 8 => 1
  | 9 => 2
  | 10 => 0
  | 11 => 2
  | 12 => 1
  | 13 => 2
  | 14 => 1
  | 15 => 0
  | 16 => 2
  | 17 => 2
  | 18 => 2
  | 19 => 0
  | 20 => 0
  | 21 => 0
  | 22 => 0
  | 23 => 0
  | 24 => 1
  | 25 => 0
  | 26 => 0
  | 27 => 2
  | 28 => 2
  | 29 => 0
  | 30 => 0
  | 31 => 1
  | 32 => 0
  | 33 => 1
  | 34 => 0
  | 35 => 2
  | 36 => 2
  | 37 => 1
  | 38 => 2
  | 39 => 1
  | 40 => 1
  | 41 => 2
  | 42 => 1
  | 43 => 1
  | 44 => 1
  | 45 => 0
  | 46 => 2
  | 47 => 0
  | 48 => 0
  | 49 => 1
  | 50 => 0
  | 51 => 0
  | 52 => 0
  | 53 => 1
  | 54 => 1
  | 55 => 2
  | 56 => 1
  | 57 => 0
  | 58 => 2
  | 59 => 1
  | 60 => 0
  | 61 => 0
  | 62 => 0
  | 63 => 0
  | _ => 0

def row61Code : ℕ := 506654919132952627441224068555679812

theorem raw_row_61_binding : ∀ j : Fin 64,
    rawDigit CFSG.Models.MatrixGroups.Suz.rows1 61 j.val = row61Digit j.val := by
  decide +kernel

theorem packed_row_61_binding : ∀ j : Fin 64,
    packedDigit 2 row61Code j.val = row61Digit j.val := by
  decide +kernel

theorem scalar_61_check : packedDot 2 row61Code columnCode 64 % 3 = 0 % 3 := by
  decide +kernel

theorem actual_row_61_dot :
    (a *ᵥ (fun j => a j 0)) (61 : Fin 64) = 0 := by
  apply selected_packed_row_dot_mod 3 64 2 CFSG.Models.MatrixGroups.Suz.rows1
    (61 : Fin 64) (0 : Fin 64) row61Code columnCode 0
  · intro j
    exact (raw_row_61_binding j).trans (packed_row_61_binding j).symm
  · intro j
    exact (raw_column_binding j).trans (packed_column_binding j).symm
  · exact scalar_61_check

def row62Digit (j : ℕ) : ℕ :=
  match j with
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | 5 => 2
  | 6 => 2
  | 7 => 1
  | 8 => 0
  | 9 => 0
  | 10 => 2
  | 11 => 0
  | 12 => 2
  | 13 => 2
  | 14 => 0
  | 15 => 2
  | 16 => 2
  | 17 => 2
  | 18 => 1
  | 19 => 0
  | 20 => 2
  | 21 => 0
  | 22 => 0
  | 23 => 2
  | 24 => 0
  | 25 => 1
  | 26 => 2
  | 27 => 1
  | 28 => 2
  | 29 => 2
  | 30 => 1
  | 31 => 1
  | 32 => 1
  | 33 => 0
  | 34 => 1
  | 35 => 1
  | 36 => 2
  | 37 => 1
  | 38 => 0
  | 39 => 1
  | 40 => 2
  | 41 => 0
  | 42 => 0
  | 43 => 2
  | 44 => 2
  | 45 => 0
  | 46 => 2
  | 47 => 1
  | 48 => 0
  | 49 => 0
  | 50 => 0
  | 51 => 2
  | 52 => 0
  | 53 => 1
  | 54 => 1
  | 55 => 0
  | 56 => 1
  | 57 => 0
  | 58 => 2
  | 59 => 2
  | 60 => 0
  | 61 => 0
  | 62 => 0
  | 63 => 1
  | _ => 0

def row62Code : ℕ := 85906967344342621358676016070559557972

theorem raw_row_62_binding : ∀ j : Fin 64,
    rawDigit CFSG.Models.MatrixGroups.Suz.rows1 62 j.val = row62Digit j.val := by
  decide +kernel

theorem packed_row_62_binding : ∀ j : Fin 64,
    packedDigit 2 row62Code j.val = row62Digit j.val := by
  decide +kernel

theorem scalar_62_check : packedDot 2 row62Code columnCode 64 % 3 = 0 % 3 := by
  decide +kernel

theorem actual_row_62_dot :
    (a *ᵥ (fun j => a j 0)) (62 : Fin 64) = 0 := by
  apply selected_packed_row_dot_mod 3 64 2 CFSG.Models.MatrixGroups.Suz.rows1
    (62 : Fin 64) (0 : Fin 64) row62Code columnCode 0
  · intro j
    exact (raw_row_62_binding j).trans (packed_row_62_binding j).symm
  · intro j
    exact (raw_column_binding j).trans (packed_column_binding j).symm
  · exact scalar_62_check

def row63Digit (j : ℕ) : ℕ :=
  match j with
  | 0 => 1
  | 1 => 0
  | 2 => 2
  | 3 => 1
  | 4 => 1
  | 5 => 0
  | 6 => 2
  | 7 => 1
  | 8 => 1
  | 9 => 0
  | 10 => 0
  | 11 => 1
  | 12 => 0
  | 13 => 2
  | 14 => 2
  | 15 => 2
  | 16 => 1
  | 17 => 1
  | 18 => 1
  | 19 => 2
  | 20 => 0
  | 21 => 2
  | 22 => 1
  | 23 => 0
  | 24 => 1
  | 25 => 2
  | 26 => 1
  | 27 => 0
  | 28 => 0
  | 29 => 0
  | 30 => 2
  | 31 => 2
  | 32 => 0
  | 33 => 0
  | 34 => 2
  | 35 => 2
  | 36 => 1
  | 37 => 2
  | 38 => 1
  | 39 => 0
  | 40 => 2
  | 41 => 1
  | 42 => 1
  | 43 => 2
  | 44 => 1
  | 45 => 1
  | 46 => 2
  | 47 => 1
  | 48 => 0
  | 49 => 1
  | 50 => 2
  | 51 => 2
  | 52 => 1
  | 53 => 1
  | 54 => 2
  | 55 => 0
  | 56 => 0
  | 57 => 1
  | 58 => 1
  | 59 => 2
  | 60 => 0
  | 61 => 1
  | 62 => 2
  | 63 => 0
  | _ => 0

def row63Code : ℕ := 48621431257333559251792067819928117601

theorem raw_row_63_binding : ∀ j : Fin 64,
    rawDigit CFSG.Models.MatrixGroups.Suz.rows1 63 j.val = row63Digit j.val := by
  decide +kernel

theorem packed_row_63_binding : ∀ j : Fin 64,
    packedDigit 2 row63Code j.val = row63Digit j.val := by
  decide +kernel

theorem scalar_63_check : packedDot 2 row63Code columnCode 64 % 3 = 0 % 3 := by
  decide +kernel

theorem actual_row_63_dot :
    (a *ᵥ (fun j => a j 0)) (63 : Fin 64) = 0 := by
  apply selected_packed_row_dot_mod 3 64 2 CFSG.Models.MatrixGroups.Suz.rows1
    (63 : Fin 64) (0 : Fin 64) row63Code columnCode 0
  · intro j
    exact (raw_row_63_binding j).trans (packed_row_63_binding j).symm
  · intro j
    exact (raw_column_binding j).trans (packed_column_binding j).symm
  · exact scalar_63_check

end SymmetricSubgroupAsymptotics.CFSGSuzPackedRows56To63
