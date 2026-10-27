import SymmetricSubgroupAsymptotics.CFSGSuzPackedRowZeroPilot

/-! Exactly rows16 through23.
Generated from one hash-guarded first Suz matrix and its first column only.
Literal data require the closed kernel bindings and scalar checks below.
No resource limit is raised. The checked row-zero pilot supplies the shared
column and row-zero theorem; its source bytes are guarded by the producer. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGSuzPackedRows16To23
open MatrixNaturalRowDotReflection
open CFSGSuzPackedRowZeroPilot

def row16Digit (j : ℕ) : ℕ :=
  match j with
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 2
  | 5 => 0
  | 6 => 2
  | 7 => 0
  | 8 => 2
  | 9 => 1
  | 10 => 2
  | 11 => 0
  | 12 => 2
  | 13 => 1
  | 14 => 1
  | 15 => 0
  | 16 => 2
  | 17 => 1
  | 18 => 2
  | 19 => 0
  | 20 => 0
  | 21 => 0
  | 22 => 0
  | 23 => 1
  | 24 => 2
  | 25 => 0
  | 26 => 1
  | 27 => 1
  | 28 => 2
  | 29 => 1
  | 30 => 0
  | 31 => 2
  | 32 => 1
  | 33 => 1
  | 34 => 2
  | 35 => 0
  | 36 => 2
  | 37 => 1
  | 38 => 1
  | 39 => 2
  | 40 => 0
  | 41 => 2
  | 42 => 1
  | 43 => 2
  | 44 => 0
  | 45 => 2
  | 46 => 2
  | 47 => 1
  | 48 => 2
  | 49 => 1
  | 50 => 1
  | 51 => 2
  | 52 => 2
  | 53 => 1
  | 54 => 1
  | 55 => 0
  | 56 => 1
  | 57 => 1
  | 58 => 0
  | 59 => 2
  | 60 => 1
  | 61 => 2
  | 62 => 0
  | 63 => 2
  | _ => 0

def row16Code : ℕ := 182795269034325170931998230178779505152

theorem raw_row_16_binding : ∀ j : Fin 64,
    rawDigit CFSG.Models.MatrixGroups.Suz.rows1 16 j.val = row16Digit j.val := by
  decide +kernel

theorem packed_row_16_binding : ∀ j : Fin 64,
    packedDigit 2 row16Code j.val = row16Digit j.val := by
  decide +kernel

theorem scalar_16_check : packedDot 2 row16Code columnCode 64 % 3 = 0 % 3 := by
  decide +kernel

theorem actual_row_16_dot :
    (a *ᵥ (fun j => a j 0)) (16 : Fin 64) = 0 := by
  apply selected_packed_row_dot_mod 3 64 2 CFSG.Models.MatrixGroups.Suz.rows1
    (16 : Fin 64) (0 : Fin 64) row16Code columnCode 0
  · intro j
    exact (raw_row_16_binding j).trans (packed_row_16_binding j).symm
  · intro j
    exact (raw_column_binding j).trans (packed_column_binding j).symm
  · exact scalar_16_check

def row17Digit (j : ℕ) : ℕ :=
  match j with
  | 0 => 0
  | 1 => 1
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => 1
  | 6 => 0
  | 7 => 0
  | 8 => 0
  | 9 => 1
  | 10 => 1
  | 11 => 0
  | 12 => 0
  | 13 => 2
  | 14 => 1
  | 15 => 2
  | 16 => 0
  | 17 => 0
  | 18 => 2
  | 19 => 2
  | 20 => 1
  | 21 => 2
  | 22 => 2
  | 23 => 0
  | 24 => 0
  | 25 => 1
  | 26 => 2
  | 27 => 0
  | 28 => 1
  | 29 => 0
  | 30 => 0
  | 31 => 2
  | 32 => 2
  | 33 => 0
  | 34 => 2
  | 35 => 0
  | 36 => 0
  | 37 => 1
  | 38 => 1
  | 39 => 0
  | 40 => 2
  | 41 => 0
  | 42 => 1
  | 43 => 0
  | 44 => 2
  | 45 => 1
  | 46 => 2
  | 47 => 2
  | 48 => 1
  | 49 => 1
  | 50 => 2
  | 51 => 2
  | 52 => 1
  | 53 => 1
  | 54 => 0
  | 55 => 1
  | 56 => 0
  | 57 => 2
  | 58 => 1
  | 59 => 0
  | 60 => 0
  | 61 => 1
  | 62 => 0
  | 63 => 0
  | _ => 0

def row17Code : ℕ := 5442939718050333552495824580377838596

theorem raw_row_17_binding : ∀ j : Fin 64,
    rawDigit CFSG.Models.MatrixGroups.Suz.rows1 17 j.val = row17Digit j.val := by
  decide +kernel

theorem packed_row_17_binding : ∀ j : Fin 64,
    packedDigit 2 row17Code j.val = row17Digit j.val := by
  decide +kernel

theorem scalar_17_check : packedDot 2 row17Code columnCode 64 % 3 = 0 % 3 := by
  decide +kernel

theorem actual_row_17_dot :
    (a *ᵥ (fun j => a j 0)) (17 : Fin 64) = 0 := by
  apply selected_packed_row_dot_mod 3 64 2 CFSG.Models.MatrixGroups.Suz.rows1
    (17 : Fin 64) (0 : Fin 64) row17Code columnCode 0
  · intro j
    exact (raw_row_17_binding j).trans (packed_row_17_binding j).symm
  · intro j
    exact (raw_column_binding j).trans (packed_column_binding j).symm
  · exact scalar_17_check

def row18Digit (j : ℕ) : ℕ :=
  match j with
  | 0 => 1
  | 1 => 1
  | 2 => 0
  | 3 => 0
  | 4 => 1
  | 5 => 0
  | 6 => 2
  | 7 => 2
  | 8 => 0
  | 9 => 0
  | 10 => 2
  | 11 => 2
  | 12 => 2
  | 13 => 0
  | 14 => 0
  | 15 => 1
  | 16 => 0
  | 17 => 0
  | 18 => 0
  | 19 => 0
  | 20 => 1
  | 21 => 2
  | 22 => 1
  | 23 => 2
  | 24 => 1
  | 25 => 2
  | 26 => 0
  | 27 => 2
  | 28 => 1
  | 29 => 0
  | 30 => 1
  | 31 => 0
  | 32 => 2
  | 33 => 2
  | 34 => 1
  | 35 => 1
  | 36 => 2
  | 37 => 1
  | 38 => 0
  | 39 => 2
  | 40 => 1
  | 41 => 2
  | 42 => 1
  | 43 => 0
  | 44 => 1
  | 45 => 0
  | 46 => 2
  | 47 => 0
  | 48 => 1
  | 49 => 2
  | 50 => 0
  | 51 => 1
  | 52 => 0
  | 53 => 1
  | 54 => 2
  | 55 => 0
  | 56 => 1
  | 57 => 2
  | 58 => 2
  | 59 => 1
  | 60 => 2
  | 61 => 2
  | 62 => 1
  | 63 => 1
  | _ => 0

def row18Code : ℕ := 120176446751434043391944377530008510725

theorem raw_row_18_binding : ∀ j : Fin 64,
    rawDigit CFSG.Models.MatrixGroups.Suz.rows1 18 j.val = row18Digit j.val := by
  decide +kernel

theorem packed_row_18_binding : ∀ j : Fin 64,
    packedDigit 2 row18Code j.val = row18Digit j.val := by
  decide +kernel

theorem scalar_18_check : packedDot 2 row18Code columnCode 64 % 3 = 0 % 3 := by
  decide +kernel

theorem actual_row_18_dot :
    (a *ᵥ (fun j => a j 0)) (18 : Fin 64) = 0 := by
  apply selected_packed_row_dot_mod 3 64 2 CFSG.Models.MatrixGroups.Suz.rows1
    (18 : Fin 64) (0 : Fin 64) row18Code columnCode 0
  · intro j
    exact (raw_row_18_binding j).trans (packed_row_18_binding j).symm
  · intro j
    exact (raw_column_binding j).trans (packed_column_binding j).symm
  · exact scalar_18_check

def row19Digit (j : ℕ) : ℕ :=
  match j with
  | 0 => 0
  | 1 => 0
  | 2 => 2
  | 3 => 1
  | 4 => 1
  | 5 => 2
  | 6 => 1
  | 7 => 1
  | 8 => 0
  | 9 => 0
  | 10 => 2
  | 11 => 1
  | 12 => 2
  | 13 => 1
  | 14 => 2
  | 15 => 1
  | 16 => 2
  | 17 => 1
  | 18 => 2
  | 19 => 0
  | 20 => 2
  | 21 => 2
  | 22 => 1
  | 23 => 1
  | 24 => 1
  | 25 => 2
  | 26 => 2
  | 27 => 1
  | 28 => 1
  | 29 => 2
  | 30 => 0
  | 31 => 1
  | 32 => 0
  | 33 => 0
  | 34 => 1
  | 35 => 0
  | 36 => 0
  | 37 => 2
  | 38 => 2
  | 39 => 0
  | 40 => 0
  | 41 => 1
  | 42 => 1
  | 43 => 0
  | 44 => 2
  | 45 => 0
  | 46 => 1
  | 47 => 1
  | 48 => 2
  | 49 => 0
  | 50 => 0
  | 51 => 0
  | 52 => 0
  | 53 => 2
  | 54 => 1
  | 55 => 1
  | 56 => 1
  | 57 => 1
  | 58 => 1
  | 59 => 2
  | 60 => 1
  | 61 => 0
  | 62 => 2
  | 63 => 1
  | _ => 0

def row19Code : ℕ := 129710552858962113880685977887832037728

theorem raw_row_19_binding : ∀ j : Fin 64,
    rawDigit CFSG.Models.MatrixGroups.Suz.rows1 19 j.val = row19Digit j.val := by
  decide +kernel

theorem packed_row_19_binding : ∀ j : Fin 64,
    packedDigit 2 row19Code j.val = row19Digit j.val := by
  decide +kernel

theorem scalar_19_check : packedDot 2 row19Code columnCode 64 % 3 = 0 % 3 := by
  decide +kernel

theorem actual_row_19_dot :
    (a *ᵥ (fun j => a j 0)) (19 : Fin 64) = 0 := by
  apply selected_packed_row_dot_mod 3 64 2 CFSG.Models.MatrixGroups.Suz.rows1
    (19 : Fin 64) (0 : Fin 64) row19Code columnCode 0
  · intro j
    exact (raw_row_19_binding j).trans (packed_row_19_binding j).symm
  · intro j
    exact (raw_column_binding j).trans (packed_column_binding j).symm
  · exact scalar_19_check

def row20Digit (j : ℕ) : ℕ :=
  match j with
  | 0 => 2
  | 1 => 0
  | 2 => 0
  | 3 => 2
  | 4 => 1
  | 5 => 2
  | 6 => 0
  | 7 => 0
  | 8 => 2
  | 9 => 1
  | 10 => 1
  | 11 => 0
  | 12 => 1
  | 13 => 0
  | 14 => 0
  | 15 => 1
  | 16 => 2
  | 17 => 2
  | 18 => 0
  | 19 => 1
  | 20 => 0
  | 21 => 1
  | 22 => 0
  | 23 => 1
  | 24 => 2
  | 25 => 1
  | 26 => 2
  | 27 => 1
  | 28 => 0
  | 29 => 2
  | 30 => 2
  | 31 => 2
  | 32 => 2
  | 33 => 0
  | 34 => 2
  | 35 => 0
  | 36 => 0
  | 37 => 0
  | 38 => 1
  | 39 => 0
  | 40 => 2
  | 41 => 0
  | 42 => 0
  | 43 => 0
  | 44 => 1
  | 45 => 2
  | 46 => 2
  | 47 => 0
  | 48 => 0
  | 49 => 2
  | 50 => 1
  | 51 => 2
  | 52 => 1
  | 53 => 0
  | 54 => 0
  | 55 => 1
  | 56 => 0
  | 57 => 1
  | 58 => 0
  | 59 => 1
  | 60 => 2
  | 61 => 1
  | 62 => 1
  | 63 => 2
  | _ => 0

def row20Code : ℕ := 199738605966114068192569866410672916866

theorem raw_row_20_binding : ∀ j : Fin 64,
    rawDigit CFSG.Models.MatrixGroups.Suz.rows1 20 j.val = row20Digit j.val := by
  decide +kernel

theorem packed_row_20_binding : ∀ j : Fin 64,
    packedDigit 2 row20Code j.val = row20Digit j.val := by
  decide +kernel

theorem scalar_20_check : packedDot 2 row20Code columnCode 64 % 3 = 0 % 3 := by
  decide +kernel

theorem actual_row_20_dot :
    (a *ᵥ (fun j => a j 0)) (20 : Fin 64) = 0 := by
  apply selected_packed_row_dot_mod 3 64 2 CFSG.Models.MatrixGroups.Suz.rows1
    (20 : Fin 64) (0 : Fin 64) row20Code columnCode 0
  · intro j
    exact (raw_row_20_binding j).trans (packed_row_20_binding j).symm
  · intro j
    exact (raw_column_binding j).trans (packed_column_binding j).symm
  · exact scalar_20_check

def row21Digit (j : ℕ) : ℕ :=
  match j with
  | 0 => 1
  | 1 => 0
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | 5 => 2
  | 6 => 1
  | 7 => 1
  | 8 => 2
  | 9 => 2
  | 10 => 1
  | 11 => 0
  | 12 => 0
  | 13 => 2
  | 14 => 2
  | 15 => 2
  | 16 => 0
  | 17 => 0
  | 18 => 2
  | 19 => 0
  | 20 => 0
  | 21 => 0
  | 22 => 0
  | 23 => 2
  | 24 => 0
  | 25 => 1
  | 26 => 0
  | 27 => 2
  | 28 => 0
  | 29 => 0
  | 30 => 0
  | 31 => 2
  | 32 => 1
  | 33 => 0
  | 34 => 2
  | 35 => 2
  | 36 => 1
  | 37 => 2
  | 38 => 0
  | 39 => 0
  | 40 => 2
  | 41 => 0
  | 42 => 2
  | 43 => 0
  | 44 => 0
  | 45 => 2
  | 46 => 0
  | 47 => 0
  | 48 => 0
  | 49 => 1
  | 50 => 2
  | 51 => 0
  | 52 => 1
  | 53 => 0
  | 54 => 2
  | 55 => 1
  | 56 => 2
  | 57 => 2
  | 58 => 1
  | 59 => 1
  | 60 => 2
  | 61 => 2
  | 62 => 1
  | 63 => 1
  | _ => 0

def row21Code : ℕ := 120099796586372996810380123593128958289

theorem raw_row_21_binding : ∀ j : Fin 64,
    rawDigit CFSG.Models.MatrixGroups.Suz.rows1 21 j.val = row21Digit j.val := by
  decide +kernel

theorem packed_row_21_binding : ∀ j : Fin 64,
    packedDigit 2 row21Code j.val = row21Digit j.val := by
  decide +kernel

theorem scalar_21_check : packedDot 2 row21Code columnCode 64 % 3 = 0 % 3 := by
  decide +kernel

theorem actual_row_21_dot :
    (a *ᵥ (fun j => a j 0)) (21 : Fin 64) = 0 := by
  apply selected_packed_row_dot_mod 3 64 2 CFSG.Models.MatrixGroups.Suz.rows1
    (21 : Fin 64) (0 : Fin 64) row21Code columnCode 0
  · intro j
    exact (raw_row_21_binding j).trans (packed_row_21_binding j).symm
  · intro j
    exact (raw_column_binding j).trans (packed_column_binding j).symm
  · exact scalar_21_check

def row22Digit (j : ℕ) : ℕ :=
  match j with
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 0
  | 4 => 2
  | 5 => 1
  | 6 => 0
  | 7 => 0
  | 8 => 1
  | 9 => 0
  | 10 => 2
  | 11 => 2
  | 12 => 0
  | 13 => 2
  | 14 => 0
  | 15 => 0
  | 16 => 0
  | 17 => 1
  | 18 => 0
  | 19 => 2
  | 20 => 0
  | 21 => 1
  | 22 => 2
  | 23 => 2
  | 24 => 1
  | 25 => 0
  | 26 => 0
  | 27 => 0
  | 28 => 0
  | 29 => 0
  | 30 => 0
  | 31 => 1
  | 32 => 1
  | 33 => 0
  | 34 => 1
  | 35 => 2
  | 36 => 2
  | 37 => 1
  | 38 => 0
  | 39 => 1
  | 40 => 1
  | 41 => 0
  | 42 => 0
  | 43 => 1
  | 44 => 1
  | 45 => 2
  | 46 => 0
  | 47 => 0
  | 48 => 0
  | 49 => 0
  | 50 => 1
  | 51 => 2
  | 52 => 1
  | 53 => 2
  | 54 => 1
  | 55 => 1
  | 56 => 2
  | 57 => 2
  | 58 => 0
  | 59 => 0
  | 60 => 2
  | 61 => 1
  | 62 => 2
  | 63 => 1
  | _ => 0

def row22Code : ℕ := 135634995084821172876916866345901032980

theorem raw_row_22_binding : ∀ j : Fin 64,
    rawDigit CFSG.Models.MatrixGroups.Suz.rows1 22 j.val = row22Digit j.val := by
  decide +kernel

theorem packed_row_22_binding : ∀ j : Fin 64,
    packedDigit 2 row22Code j.val = row22Digit j.val := by
  decide +kernel

theorem scalar_22_check : packedDot 2 row22Code columnCode 64 % 3 = 0 % 3 := by
  decide +kernel

theorem actual_row_22_dot :
    (a *ᵥ (fun j => a j 0)) (22 : Fin 64) = 0 := by
  apply selected_packed_row_dot_mod 3 64 2 CFSG.Models.MatrixGroups.Suz.rows1
    (22 : Fin 64) (0 : Fin 64) row22Code columnCode 0
  · intro j
    exact (raw_row_22_binding j).trans (packed_row_22_binding j).symm
  · intro j
    exact (raw_column_binding j).trans (packed_column_binding j).symm
  · exact scalar_22_check

def row23Digit (j : ℕ) : ℕ :=
  match j with
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 1
  | 4 => 2
  | 5 => 1
  | 6 => 1
  | 7 => 2
  | 8 => 1
  | 9 => 2
  | 10 => 0
  | 11 => 1
  | 12 => 0
  | 13 => 0
  | 14 => 2
  | 15 => 2
  | 16 => 0
  | 17 => 1
  | 18 => 0
  | 19 => 2
  | 20 => 0
  | 21 => 0
  | 22 => 1
  | 23 => 1
  | 24 => 1
  | 25 => 2
  | 26 => 2
  | 27 => 2
  | 28 => 2
  | 29 => 2
  | 30 => 1
  | 31 => 0
  | 32 => 0
  | 33 => 2
  | 34 => 0
  | 35 => 2
  | 36 => 2
  | 37 => 0
  | 38 => 1
  | 39 => 1
  | 40 => 0
  | 41 => 1
  | 42 => 2
  | 43 => 2
  | 44 => 0
  | 45 => 1
  | 46 => 0
  | 47 => 0
  | 48 => 0
  | 49 => 2
  | 50 => 1
  | 51 => 1
  | 52 => 2
  | 53 => 0
  | 54 => 0
  | 55 => 1
  | 56 => 0
  | 57 => 0
  | 58 => 1
  | 59 => 1
  | 60 => 2
  | 61 => 1
  | 62 => 0
  | 63 => 0
  | _ => 0

def row23Code : ℕ := 8392097335941017331647094860034971216

theorem raw_row_23_binding : ∀ j : Fin 64,
    rawDigit CFSG.Models.MatrixGroups.Suz.rows1 23 j.val = row23Digit j.val := by
  decide +kernel

theorem packed_row_23_binding : ∀ j : Fin 64,
    packedDigit 2 row23Code j.val = row23Digit j.val := by
  decide +kernel

theorem scalar_23_check : packedDot 2 row23Code columnCode 64 % 3 = 0 % 3 := by
  decide +kernel

theorem actual_row_23_dot :
    (a *ᵥ (fun j => a j 0)) (23 : Fin 64) = 0 := by
  apply selected_packed_row_dot_mod 3 64 2 CFSG.Models.MatrixGroups.Suz.rows1
    (23 : Fin 64) (0 : Fin 64) row23Code columnCode 0
  · intro j
    exact (raw_row_23_binding j).trans (packed_row_23_binding j).symm
  · intro j
    exact (raw_column_binding j).trans (packed_column_binding j).symm
  · exact scalar_23_check

end SymmetricSubgroupAsymptotics.CFSGSuzPackedRows16To23
