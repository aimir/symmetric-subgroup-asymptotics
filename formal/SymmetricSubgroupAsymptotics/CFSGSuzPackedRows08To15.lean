import SymmetricSubgroupAsymptotics.CFSGSuzPackedRowZeroPilot

/-! Exactly rows8 through15.
Generated from one hash-guarded first Suz matrix and its first column only.
Literal data require the closed kernel bindings and scalar checks below.
No resource limit is raised. The checked row-zero pilot supplies the shared
column and row-zero theorem; its source bytes are guarded by the producer. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGSuzPackedRows08To15
open MatrixNaturalRowDotReflection
open CFSGSuzPackedRowZeroPilot

def row08Digit (j : ℕ) : ℕ :=
  match j with
  | 0 => 1
  | 1 => 2
  | 2 => 2
  | 3 => 1
  | 4 => 1
  | 5 => 2
  | 6 => 0
  | 7 => 0
  | 8 => 1
  | 9 => 2
  | 10 => 1
  | 11 => 2
  | 12 => 0
  | 13 => 1
  | 14 => 2
  | 15 => 0
  | 16 => 2
  | 17 => 0
  | 18 => 1
  | 19 => 0
  | 20 => 2
  | 21 => 2
  | 22 => 0
  | 23 => 2
  | 24 => 0
  | 25 => 0
  | 26 => 0
  | 27 => 1
  | 28 => 2
  | 29 => 2
  | 30 => 2
  | 31 => 1
  | 32 => 0
  | 33 => 1
  | 34 => 0
  | 35 => 2
  | 36 => 1
  | 37 => 0
  | 38 => 2
  | 39 => 1
  | 40 => 2
  | 41 => 0
  | 42 => 1
  | 43 => 2
  | 44 => 0
  | 45 => 2
  | 46 => 0
  | 47 => 0
  | 48 => 0
  | 49 => 0
  | 50 => 2
  | 51 => 1
  | 52 => 2
  | 53 => 0
  | 54 => 0
  | 55 => 1
  | 56 => 2
  | 57 => 2
  | 58 => 1
  | 59 => 2
  | 60 => 1
  | 61 => 0
  | 62 => 2
  | 63 => 1
  | _ => 0

def row08Code : ℕ := 129736075554941489266497194452307216745

theorem raw_row_08_binding : ∀ j : Fin 64,
    rawDigit CFSG.Models.MatrixGroups.Suz.rows1 8 j.val = row08Digit j.val := by
  decide +kernel

theorem packed_row_08_binding : ∀ j : Fin 64,
    packedDigit 2 row08Code j.val = row08Digit j.val := by
  decide +kernel

theorem scalar_08_check : packedDot 2 row08Code columnCode 64 % 3 = 0 % 3 := by
  decide +kernel

theorem actual_row_08_dot :
    (a *ᵥ (fun j => a j 0)) (8 : Fin 64) = 0 := by
  apply selected_packed_row_dot_mod 3 64 2 CFSG.Models.MatrixGroups.Suz.rows1
    (8 : Fin 64) (0 : Fin 64) row08Code columnCode 0
  · intro j
    exact (raw_row_08_binding j).trans (packed_row_08_binding j).symm
  · intro j
    exact (raw_column_binding j).trans (packed_column_binding j).symm
  · exact scalar_08_check

def row09Digit (j : ℕ) : ℕ :=
  match j with
  | 0 => 2
  | 1 => 0
  | 2 => 2
  | 3 => 0
  | 4 => 2
  | 5 => 2
  | 6 => 0
  | 7 => 0
  | 8 => 2
  | 9 => 0
  | 10 => 0
  | 11 => 0
  | 12 => 2
  | 13 => 2
  | 14 => 1
  | 15 => 2
  | 16 => 1
  | 17 => 2
  | 18 => 1
  | 19 => 2
  | 20 => 1
  | 21 => 2
  | 22 => 2
  | 23 => 1
  | 24 => 2
  | 25 => 2
  | 26 => 1
  | 27 => 0
  | 28 => 2
  | 29 => 2
  | 30 => 1
  | 31 => 2
  | 32 => 1
  | 33 => 0
  | 34 => 0
  | 35 => 1
  | 36 => 1
  | 37 => 1
  | 38 => 2
  | 39 => 0
  | 40 => 0
  | 41 => 0
  | 42 => 0
  | 43 => 0
  | 44 => 2
  | 45 => 1
  | 46 => 2
  | 47 => 2
  | 48 => 2
  | 49 => 2
  | 50 => 1
  | 51 => 1
  | 52 => 2
  | 53 => 0
  | 54 => 1
  | 55 => 0
  | 56 => 0
  | 57 => 1
  | 58 => 1
  | 59 => 1
  | 60 => 0
  | 61 => 0
  | 62 => 0
  | 63 => 1
  | _ => 0

def row09Code : ℕ := 85507116931633720968544044335052753442

theorem raw_row_09_binding : ∀ j : Fin 64,
    rawDigit CFSG.Models.MatrixGroups.Suz.rows1 9 j.val = row09Digit j.val := by
  decide +kernel

theorem packed_row_09_binding : ∀ j : Fin 64,
    packedDigit 2 row09Code j.val = row09Digit j.val := by
  decide +kernel

theorem scalar_09_check : packedDot 2 row09Code columnCode 64 % 3 = 0 % 3 := by
  decide +kernel

theorem actual_row_09_dot :
    (a *ᵥ (fun j => a j 0)) (9 : Fin 64) = 0 := by
  apply selected_packed_row_dot_mod 3 64 2 CFSG.Models.MatrixGroups.Suz.rows1
    (9 : Fin 64) (0 : Fin 64) row09Code columnCode 0
  · intro j
    exact (raw_row_09_binding j).trans (packed_row_09_binding j).symm
  · intro j
    exact (raw_column_binding j).trans (packed_column_binding j).symm
  · exact scalar_09_check

def row10Digit (j : ℕ) : ℕ :=
  match j with
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 0
  | 4 => 0
  | 5 => 2
  | 6 => 2
  | 7 => 2
  | 8 => 1
  | 9 => 0
  | 10 => 1
  | 11 => 1
  | 12 => 2
  | 13 => 2
  | 14 => 1
  | 15 => 0
  | 16 => 1
  | 17 => 1
  | 18 => 2
  | 19 => 2
  | 20 => 1
  | 21 => 1
  | 22 => 0
  | 23 => 2
  | 24 => 2
  | 25 => 1
  | 26 => 0
  | 27 => 2
  | 28 => 2
  | 29 => 2
  | 30 => 1
  | 31 => 2
  | 32 => 1
  | 33 => 0
  | 34 => 1
  | 35 => 2
  | 36 => 1
  | 37 => 0
  | 38 => 2
  | 39 => 1
  | 40 => 1
  | 41 => 1
  | 42 => 1
  | 43 => 2
  | 44 => 2
  | 45 => 0
  | 46 => 2
  | 47 => 0
  | 48 => 0
  | 49 => 2
  | 50 => 2
  | 51 => 2
  | 52 => 2
  | 53 => 2
  | 54 => 0
  | 55 => 1
  | 56 => 0
  | 57 => 2
  | 58 => 2
  | 59 => 1
  | 60 => 1
  | 61 => 1
  | 62 => 0
  | 63 => 2
  | _ => 0

def row10Code : ℕ := 177328836532026486826103373647525816336

theorem raw_row_10_binding : ∀ j : Fin 64,
    rawDigit CFSG.Models.MatrixGroups.Suz.rows1 10 j.val = row10Digit j.val := by
  decide +kernel

theorem packed_row_10_binding : ∀ j : Fin 64,
    packedDigit 2 row10Code j.val = row10Digit j.val := by
  decide +kernel

theorem scalar_10_check : packedDot 2 row10Code columnCode 64 % 3 = 0 % 3 := by
  decide +kernel

theorem actual_row_10_dot :
    (a *ᵥ (fun j => a j 0)) (10 : Fin 64) = 0 := by
  apply selected_packed_row_dot_mod 3 64 2 CFSG.Models.MatrixGroups.Suz.rows1
    (10 : Fin 64) (0 : Fin 64) row10Code columnCode 0
  · intro j
    exact (raw_row_10_binding j).trans (packed_row_10_binding j).symm
  · intro j
    exact (raw_column_binding j).trans (packed_column_binding j).symm
  · exact scalar_10_check

def row11Digit (j : ℕ) : ℕ :=
  match j with
  | 0 => 1
  | 1 => 2
  | 2 => 1
  | 3 => 2
  | 4 => 2
  | 5 => 0
  | 6 => 1
  | 7 => 0
  | 8 => 2
  | 9 => 1
  | 10 => 1
  | 11 => 1
  | 12 => 0
  | 13 => 2
  | 14 => 0
  | 15 => 1
  | 16 => 0
  | 17 => 0
  | 18 => 2
  | 19 => 1
  | 20 => 0
  | 21 => 0
  | 22 => 0
  | 23 => 1
  | 24 => 1
  | 25 => 1
  | 26 => 0
  | 27 => 2
  | 28 => 0
  | 29 => 2
  | 30 => 2
  | 31 => 2
  | 32 => 0
  | 33 => 0
  | 34 => 1
  | 35 => 1
  | 36 => 1
  | 37 => 1
  | 38 => 0
  | 39 => 0
  | 40 => 0
  | 41 => 0
  | 42 => 2
  | 43 => 0
  | 44 => 1
  | 45 => 0
  | 46 => 2
  | 47 => 1
  | 48 => 0
  | 49 => 2
  | 50 => 2
  | 51 => 2
  | 52 => 0
  | 53 => 1
  | 54 => 0
  | 55 => 2
  | 56 => 2
  | 57 => 2
  | 58 => 2
  | 59 => 1
  | 60 => 1
  | 61 => 1
  | 62 => 2
  | 63 => 0
  | _ => 0

def row11Code : ℕ := 49734509929504320121583033391257096857

theorem raw_row_11_binding : ∀ j : Fin 64,
    rawDigit CFSG.Models.MatrixGroups.Suz.rows1 11 j.val = row11Digit j.val := by
  decide +kernel

theorem packed_row_11_binding : ∀ j : Fin 64,
    packedDigit 2 row11Code j.val = row11Digit j.val := by
  decide +kernel

theorem scalar_11_check : packedDot 2 row11Code columnCode 64 % 3 = 0 % 3 := by
  decide +kernel

theorem actual_row_11_dot :
    (a *ᵥ (fun j => a j 0)) (11 : Fin 64) = 0 := by
  apply selected_packed_row_dot_mod 3 64 2 CFSG.Models.MatrixGroups.Suz.rows1
    (11 : Fin 64) (0 : Fin 64) row11Code columnCode 0
  · intro j
    exact (raw_row_11_binding j).trans (packed_row_11_binding j).symm
  · intro j
    exact (raw_column_binding j).trans (packed_column_binding j).symm
  · exact scalar_11_check

def row12Digit (j : ℕ) : ℕ :=
  match j with
  | 0 => 0
  | 1 => 1
  | 2 => 0
  | 3 => 1
  | 4 => 0
  | 5 => 2
  | 6 => 0
  | 7 => 1
  | 8 => 2
  | 9 => 2
  | 10 => 1
  | 11 => 1
  | 12 => 1
  | 13 => 1
  | 14 => 2
  | 15 => 1
  | 16 => 1
  | 17 => 2
  | 18 => 2
  | 19 => 1
  | 20 => 0
  | 21 => 0
  | 22 => 2
  | 23 => 0
  | 24 => 0
  | 25 => 0
  | 26 => 1
  | 27 => 2
  | 28 => 0
  | 29 => 0
  | 30 => 2
  | 31 => 2
  | 32 => 1
  | 33 => 1
  | 34 => 1
  | 35 => 2
  | 36 => 1
  | 37 => 0
  | 38 => 1
  | 39 => 2
  | 40 => 1
  | 41 => 1
  | 42 => 2
  | 43 => 1
  | 44 => 2
  | 45 => 0
  | 46 => 1
  | 47 => 1
  | 48 => 0
  | 49 => 1
  | 50 => 0
  | 51 => 2
  | 52 => 0
  | 53 => 1
  | 54 => 1
  | 55 => 2
  | 56 => 2
  | 57 => 1
  | 58 => 2
  | 59 => 1
  | 60 => 1
  | 61 => 0
  | 62 => 0
  | 63 => 1
  | _ => 0

def row12Code : ℕ := 86932446285829436303378915427910043716

theorem raw_row_12_binding : ∀ j : Fin 64,
    rawDigit CFSG.Models.MatrixGroups.Suz.rows1 12 j.val = row12Digit j.val := by
  decide +kernel

theorem packed_row_12_binding : ∀ j : Fin 64,
    packedDigit 2 row12Code j.val = row12Digit j.val := by
  decide +kernel

theorem scalar_12_check : packedDot 2 row12Code columnCode 64 % 3 = 0 % 3 := by
  decide +kernel

theorem actual_row_12_dot :
    (a *ᵥ (fun j => a j 0)) (12 : Fin 64) = 0 := by
  apply selected_packed_row_dot_mod 3 64 2 CFSG.Models.MatrixGroups.Suz.rows1
    (12 : Fin 64) (0 : Fin 64) row12Code columnCode 0
  · intro j
    exact (raw_row_12_binding j).trans (packed_row_12_binding j).symm
  · intro j
    exact (raw_column_binding j).trans (packed_column_binding j).symm
  · exact scalar_12_check

def row13Digit (j : ℕ) : ℕ :=
  match j with
  | 0 => 1
  | 1 => 2
  | 2 => 1
  | 3 => 2
  | 4 => 2
  | 5 => 1
  | 6 => 1
  | 7 => 1
  | 8 => 0
  | 9 => 2
  | 10 => 2
  | 11 => 2
  | 12 => 1
  | 13 => 2
  | 14 => 0
  | 15 => 0
  | 16 => 0
  | 17 => 0
  | 18 => 2
  | 19 => 1
  | 20 => 1
  | 21 => 1
  | 22 => 1
  | 23 => 1
  | 24 => 2
  | 25 => 2
  | 26 => 2
  | 27 => 0
  | 28 => 0
  | 29 => 0
  | 30 => 0
  | 31 => 0
  | 32 => 0
  | 33 => 2
  | 34 => 2
  | 35 => 1
  | 36 => 0
  | 37 => 0
  | 38 => 0
  | 39 => 0
  | 40 => 0
  | 41 => 1
  | 42 => 2
  | 43 => 1
  | 44 => 2
  | 45 => 0
  | 46 => 1
  | 47 => 1
  | 48 => 1
  | 49 => 1
  | 50 => 0
  | 51 => 0
  | 52 => 1
  | 53 => 2
  | 54 => 2
  | 55 => 1
  | 56 => 2
  | 57 => 2
  | 58 => 2
  | 59 => 1
  | 60 => 1
  | 61 => 1
  | 62 => 0
  | 63 => 2
  | _ => 0

def row13Code : ℕ := 177339836981046364127331832095973070489

theorem raw_row_13_binding : ∀ j : Fin 64,
    rawDigit CFSG.Models.MatrixGroups.Suz.rows1 13 j.val = row13Digit j.val := by
  decide +kernel

theorem packed_row_13_binding : ∀ j : Fin 64,
    packedDigit 2 row13Code j.val = row13Digit j.val := by
  decide +kernel

theorem scalar_13_check : packedDot 2 row13Code columnCode 64 % 3 = 0 % 3 := by
  decide +kernel

theorem actual_row_13_dot :
    (a *ᵥ (fun j => a j 0)) (13 : Fin 64) = 0 := by
  apply selected_packed_row_dot_mod 3 64 2 CFSG.Models.MatrixGroups.Suz.rows1
    (13 : Fin 64) (0 : Fin 64) row13Code columnCode 0
  · intro j
    exact (raw_row_13_binding j).trans (packed_row_13_binding j).symm
  · intro j
    exact (raw_column_binding j).trans (packed_column_binding j).symm
  · exact scalar_13_check

def row14Digit (j : ℕ) : ℕ :=
  match j with
  | 0 => 1
  | 1 => 0
  | 2 => 0
  | 3 => 1
  | 4 => 2
  | 5 => 0
  | 6 => 2
  | 7 => 2
  | 8 => 2
  | 9 => 0
  | 10 => 1
  | 11 => 0
  | 12 => 1
  | 13 => 1
  | 14 => 0
  | 15 => 0
  | 16 => 2
  | 17 => 0
  | 18 => 0
  | 19 => 2
  | 20 => 1
  | 21 => 2
  | 22 => 0
  | 23 => 1
  | 24 => 0
  | 25 => 2
  | 26 => 2
  | 27 => 1
  | 28 => 1
  | 29 => 2
  | 30 => 2
  | 31 => 0
  | 32 => 2
  | 33 => 2
  | 34 => 0
  | 35 => 0
  | 36 => 0
  | 37 => 1
  | 38 => 1
  | 39 => 2
  | 40 => 1
  | 41 => 0
  | 42 => 0
  | 43 => 0
  | 44 => 2
  | 45 => 2
  | 46 => 0
  | 47 => 2
  | 48 => 1
  | 49 => 2
  | 50 => 0
  | 51 => 2
  | 52 => 2
  | 53 => 0
  | 54 => 2
  | 55 => 2
  | 56 => 1
  | 57 => 2
  | 58 => 1
  | 59 => 1
  | 60 => 2
  | 61 => 0
  | 62 => 1
  | 63 => 0
  | _ => 0

def row14Code : ℕ := 24391514991862980774886526162270593601

theorem raw_row_14_binding : ∀ j : Fin 64,
    rawDigit CFSG.Models.MatrixGroups.Suz.rows1 14 j.val = row14Digit j.val := by
  decide +kernel

theorem packed_row_14_binding : ∀ j : Fin 64,
    packedDigit 2 row14Code j.val = row14Digit j.val := by
  decide +kernel

theorem scalar_14_check : packedDot 2 row14Code columnCode 64 % 3 = 0 % 3 := by
  decide +kernel

theorem actual_row_14_dot :
    (a *ᵥ (fun j => a j 0)) (14 : Fin 64) = 0 := by
  apply selected_packed_row_dot_mod 3 64 2 CFSG.Models.MatrixGroups.Suz.rows1
    (14 : Fin 64) (0 : Fin 64) row14Code columnCode 0
  · intro j
    exact (raw_row_14_binding j).trans (packed_row_14_binding j).symm
  · intro j
    exact (raw_column_binding j).trans (packed_column_binding j).symm
  · exact scalar_14_check

def row15Digit (j : ℕ) : ℕ :=
  match j with
  | 0 => 1
  | 1 => 2
  | 2 => 2
  | 3 => 2
  | 4 => 2
  | 5 => 2
  | 6 => 1
  | 7 => 1
  | 8 => 2
  | 9 => 2
  | 10 => 0
  | 11 => 1
  | 12 => 1
  | 13 => 1
  | 14 => 2
  | 15 => 0
  | 16 => 0
  | 17 => 0
  | 18 => 0
  | 19 => 1
  | 20 => 0
  | 21 => 2
  | 22 => 0
  | 23 => 2
  | 24 => 1
  | 25 => 2
  | 26 => 2
  | 27 => 0
  | 28 => 1
  | 29 => 0
  | 30 => 1
  | 31 => 2
  | 32 => 0
  | 33 => 0
  | 34 => 0
  | 35 => 2
  | 36 => 2
  | 37 => 0
  | 38 => 2
  | 39 => 1
  | 40 => 0
  | 41 => 2
  | 42 => 2
  | 43 => 0
  | 44 => 1
  | 45 => 0
  | 46 => 2
  | 47 => 2
  | 48 => 1
  | 49 => 0
  | 50 => 1
  | 51 => 0
  | 52 => 1
  | 53 => 0
  | 54 => 1
  | 55 => 2
  | 56 => 0
  | 57 => 0
  | 58 => 1
  | 59 => 1
  | 60 => 2
  | 61 => 1
  | 62 => 2
  | 63 => 0
  | _ => 0

def row15Code : ℕ := 50928989934656790392912064749035477673

theorem raw_row_15_binding : ∀ j : Fin 64,
    rawDigit CFSG.Models.MatrixGroups.Suz.rows1 15 j.val = row15Digit j.val := by
  decide +kernel

theorem packed_row_15_binding : ∀ j : Fin 64,
    packedDigit 2 row15Code j.val = row15Digit j.val := by
  decide +kernel

theorem scalar_15_check : packedDot 2 row15Code columnCode 64 % 3 = 0 % 3 := by
  decide +kernel

theorem actual_row_15_dot :
    (a *ᵥ (fun j => a j 0)) (15 : Fin 64) = 0 := by
  apply selected_packed_row_dot_mod 3 64 2 CFSG.Models.MatrixGroups.Suz.rows1
    (15 : Fin 64) (0 : Fin 64) row15Code columnCode 0
  · intro j
    exact (raw_row_15_binding j).trans (packed_row_15_binding j).symm
  · intro j
    exact (raw_column_binding j).trans (packed_column_binding j).symm
  · exact scalar_15_check

end SymmetricSubgroupAsymptotics.CFSGSuzPackedRows08To15
