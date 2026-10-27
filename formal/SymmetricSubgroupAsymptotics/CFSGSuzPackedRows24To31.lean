import SymmetricSubgroupAsymptotics.CFSGSuzPackedRowZeroPilot

/-! Exactly rows24 through31.
Generated from one hash-guarded first Suz matrix and its first column only.
Literal data require the closed kernel bindings and scalar checks below.
No resource limit is raised. The checked row-zero pilot supplies the shared
column and row-zero theorem; its source bytes are guarded by the producer. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGSuzPackedRows24To31
open MatrixNaturalRowDotReflection
open CFSGSuzPackedRowZeroPilot

def row24Digit (j : ℕ) : ℕ :=
  match j with
  | 0 => 2
  | 1 => 2
  | 2 => 2
  | 3 => 0
  | 4 => 2
  | 5 => 0
  | 6 => 1
  | 7 => 0
  | 8 => 0
  | 9 => 1
  | 10 => 0
  | 11 => 0
  | 12 => 0
  | 13 => 2
  | 14 => 0
  | 15 => 1
  | 16 => 1
  | 17 => 2
  | 18 => 2
  | 19 => 2
  | 20 => 1
  | 21 => 0
  | 22 => 0
  | 23 => 1
  | 24 => 2
  | 25 => 0
  | 26 => 0
  | 27 => 2
  | 28 => 1
  | 29 => 2
  | 30 => 0
  | 31 => 1
  | 32 => 1
  | 33 => 0
  | 34 => 2
  | 35 => 1
  | 36 => 2
  | 37 => 1
  | 38 => 0
  | 39 => 2
  | 40 => 2
  | 41 => 2
  | 42 => 1
  | 43 => 1
  | 44 => 0
  | 45 => 2
  | 46 => 0
  | 47 => 0
  | 48 => 0
  | 49 => 1
  | 50 => 1
  | 51 => 2
  | 52 => 0
  | 53 => 1
  | 54 => 0
  | 55 => 0
  | 56 => 1
  | 57 => 2
  | 58 => 0
  | 59 => 2
  | 60 => 0
  | 61 => 2
  | 62 => 2
  | 63 => 1
  | _ => 0

def row24Code : ℕ := 138951149089242306878984097064630358570

theorem raw_row_24_binding : ∀ j : Fin 64,
    rawDigit CFSG.Models.MatrixGroups.Suz.rows1 24 j.val = row24Digit j.val := by
  decide +kernel

theorem packed_row_24_binding : ∀ j : Fin 64,
    packedDigit 2 row24Code j.val = row24Digit j.val := by
  decide +kernel

theorem scalar_24_check : packedDot 2 row24Code columnCode 64 % 3 = 0 % 3 := by
  decide +kernel

theorem actual_row_24_dot :
    (a *ᵥ (fun j => a j 0)) (24 : Fin 64) = 0 := by
  apply selected_packed_row_dot_mod 3 64 2 CFSG.Models.MatrixGroups.Suz.rows1
    (24 : Fin 64) (0 : Fin 64) row24Code columnCode 0
  · intro j
    exact (raw_row_24_binding j).trans (packed_row_24_binding j).symm
  · intro j
    exact (raw_column_binding j).trans (packed_column_binding j).symm
  · exact scalar_24_check

def row25Digit (j : ℕ) : ℕ :=
  match j with
  | 0 => 0
  | 1 => 1
  | 2 => 0
  | 3 => 0
  | 4 => 2
  | 5 => 2
  | 6 => 2
  | 7 => 2
  | 8 => 0
  | 9 => 1
  | 10 => 2
  | 11 => 2
  | 12 => 2
  | 13 => 1
  | 14 => 0
  | 15 => 0
  | 16 => 0
  | 17 => 0
  | 18 => 1
  | 19 => 1
  | 20 => 2
  | 21 => 2
  | 22 => 1
  | 23 => 1
  | 24 => 2
  | 25 => 2
  | 26 => 0
  | 27 => 2
  | 28 => 0
  | 29 => 0
  | 30 => 1
  | 31 => 2
  | 32 => 0
  | 33 => 2
  | 34 => 2
  | 35 => 1
  | 36 => 1
  | 37 => 0
  | 38 => 0
  | 39 => 0
  | 40 => 0
  | 41 => 1
  | 42 => 1
  | 43 => 2
  | 44 => 1
  | 45 => 2
  | 46 => 1
  | 47 => 0
  | 48 => 1
  | 49 => 0
  | 50 => 0
  | 51 => 1
  | 52 => 2
  | 53 => 2
  | 54 => 1
  | 55 => 2
  | 56 => 1
  | 57 => 0
  | 58 => 1
  | 59 => 2
  | 60 => 1
  | 61 => 2
  | 62 => 1
  | 63 => 1
  | _ => 0

def row25Code : ℕ := 119057303318170641397082676549160053252

theorem raw_row_25_binding : ∀ j : Fin 64,
    rawDigit CFSG.Models.MatrixGroups.Suz.rows1 25 j.val = row25Digit j.val := by
  decide +kernel

theorem packed_row_25_binding : ∀ j : Fin 64,
    packedDigit 2 row25Code j.val = row25Digit j.val := by
  decide +kernel

theorem scalar_25_check : packedDot 2 row25Code columnCode 64 % 3 = 0 % 3 := by
  decide +kernel

theorem actual_row_25_dot :
    (a *ᵥ (fun j => a j 0)) (25 : Fin 64) = 0 := by
  apply selected_packed_row_dot_mod 3 64 2 CFSG.Models.MatrixGroups.Suz.rows1
    (25 : Fin 64) (0 : Fin 64) row25Code columnCode 0
  · intro j
    exact (raw_row_25_binding j).trans (packed_row_25_binding j).symm
  · intro j
    exact (raw_column_binding j).trans (packed_column_binding j).symm
  · exact scalar_25_check

def row26Digit (j : ℕ) : ℕ :=
  match j with
  | 0 => 1
  | 1 => 0
  | 2 => 2
  | 3 => 2
  | 4 => 0
  | 5 => 1
  | 6 => 1
  | 7 => 1
  | 8 => 2
  | 9 => 2
  | 10 => 1
  | 11 => 1
  | 12 => 2
  | 13 => 2
  | 14 => 2
  | 15 => 0
  | 16 => 2
  | 17 => 1
  | 18 => 0
  | 19 => 0
  | 20 => 2
  | 21 => 2
  | 22 => 0
  | 23 => 2
  | 24 => 1
  | 25 => 2
  | 26 => 0
  | 27 => 2
  | 28 => 1
  | 29 => 2
  | 30 => 0
  | 31 => 1
  | 32 => 0
  | 33 => 0
  | 34 => 2
  | 35 => 1
  | 36 => 2
  | 37 => 2
  | 38 => 0
  | 39 => 0
  | 40 => 2
  | 41 => 1
  | 42 => 2
  | 43 => 0
  | 44 => 2
  | 45 => 0
  | 46 => 0
  | 47 => 2
  | 48 => 2
  | 49 => 0
  | 50 => 2
  | 51 => 2
  | 52 => 2
  | 53 => 0
  | 54 => 0
  | 55 => 1
  | 56 => 1
  | 57 => 0
  | 58 => 1
  | 59 => 0
  | 60 => 1
  | 61 => 2
  | 62 => 2
  | 63 => 1
  | _ => 0

def row26Code : ℕ := 139658560118286466503426823250830316705

theorem raw_row_26_binding : ∀ j : Fin 64,
    rawDigit CFSG.Models.MatrixGroups.Suz.rows1 26 j.val = row26Digit j.val := by
  decide +kernel

theorem packed_row_26_binding : ∀ j : Fin 64,
    packedDigit 2 row26Code j.val = row26Digit j.val := by
  decide +kernel

theorem scalar_26_check : packedDot 2 row26Code columnCode 64 % 3 = 0 % 3 := by
  decide +kernel

theorem actual_row_26_dot :
    (a *ᵥ (fun j => a j 0)) (26 : Fin 64) = 0 := by
  apply selected_packed_row_dot_mod 3 64 2 CFSG.Models.MatrixGroups.Suz.rows1
    (26 : Fin 64) (0 : Fin 64) row26Code columnCode 0
  · intro j
    exact (raw_row_26_binding j).trans (packed_row_26_binding j).symm
  · intro j
    exact (raw_column_binding j).trans (packed_column_binding j).symm
  · exact scalar_26_check

def row27Digit (j : ℕ) : ℕ :=
  match j with
  | 0 => 2
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | 5 => 0
  | 6 => 2
  | 7 => 0
  | 8 => 0
  | 9 => 0
  | 10 => 0
  | 11 => 1
  | 12 => 1
  | 13 => 1
  | 14 => 0
  | 15 => 2
  | 16 => 1
  | 17 => 0
  | 18 => 2
  | 19 => 0
  | 20 => 2
  | 21 => 0
  | 22 => 2
  | 23 => 0
  | 24 => 1
  | 25 => 2
  | 26 => 1
  | 27 => 0
  | 28 => 1
  | 29 => 1
  | 30 => 1
  | 31 => 2
  | 32 => 1
  | 33 => 0
  | 34 => 0
  | 35 => 1
  | 36 => 0
  | 37 => 1
  | 38 => 2
  | 39 => 0
  | 40 => 2
  | 41 => 2
  | 42 => 1
  | 43 => 2
  | 44 => 0
  | 45 => 0
  | 46 => 1
  | 47 => 1
  | 48 => 1
  | 49 => 1
  | 50 => 0
  | 51 => 2
  | 52 => 1
  | 53 => 1
  | 54 => 2
  | 55 => 1
  | 56 => 1
  | 57 => 2
  | 58 => 0
  | 59 => 0
  | 60 => 1
  | 61 => 2
  | 62 => 0
  | 63 => 2
  | _ => 0

def row27Code : ℕ := 182153025179921017829251722741765120342

theorem raw_row_27_binding : ∀ j : Fin 64,
    rawDigit CFSG.Models.MatrixGroups.Suz.rows1 27 j.val = row27Digit j.val := by
  decide +kernel

theorem packed_row_27_binding : ∀ j : Fin 64,
    packedDigit 2 row27Code j.val = row27Digit j.val := by
  decide +kernel

theorem scalar_27_check : packedDot 2 row27Code columnCode 64 % 3 = 0 % 3 := by
  decide +kernel

theorem actual_row_27_dot :
    (a *ᵥ (fun j => a j 0)) (27 : Fin 64) = 0 := by
  apply selected_packed_row_dot_mod 3 64 2 CFSG.Models.MatrixGroups.Suz.rows1
    (27 : Fin 64) (0 : Fin 64) row27Code columnCode 0
  · intro j
    exact (raw_row_27_binding j).trans (packed_row_27_binding j).symm
  · intro j
    exact (raw_column_binding j).trans (packed_column_binding j).symm
  · exact scalar_27_check

def row28Digit (j : ℕ) : ℕ :=
  match j with
  | 0 => 0
  | 1 => 2
  | 2 => 1
  | 3 => 0
  | 4 => 2
  | 5 => 2
  | 6 => 1
  | 7 => 0
  | 8 => 2
  | 9 => 2
  | 10 => 2
  | 11 => 2
  | 12 => 1
  | 13 => 0
  | 14 => 2
  | 15 => 0
  | 16 => 2
  | 17 => 1
  | 18 => 1
  | 19 => 0
  | 20 => 0
  | 21 => 2
  | 22 => 0
  | 23 => 0
  | 24 => 0
  | 25 => 0
  | 26 => 0
  | 27 => 0
  | 28 => 0
  | 29 => 2
  | 30 => 2
  | 31 => 2
  | 32 => 0
  | 33 => 0
  | 34 => 0
  | 35 => 0
  | 36 => 1
  | 37 => 0
  | 38 => 0
  | 39 => 1
  | 40 => 0
  | 41 => 2
  | 42 => 1
  | 43 => 2
  | 44 => 0
  | 45 => 1
  | 46 => 0
  | 47 => 1
  | 48 => 0
  | 49 => 1
  | 50 => 2
  | 51 => 1
  | 52 => 1
  | 53 => 1
  | 54 => 2
  | 55 => 1
  | 56 => 2
  | 57 => 1
  | 58 => 2
  | 59 => 1
  | 60 => 2
  | 61 => 2
  | 62 => 1
  | 63 => 1
  | _ => 0

def row28Code : ℕ := 120162190367628245582959283601884715544

theorem raw_row_28_binding : ∀ j : Fin 64,
    rawDigit CFSG.Models.MatrixGroups.Suz.rows1 28 j.val = row28Digit j.val := by
  decide +kernel

theorem packed_row_28_binding : ∀ j : Fin 64,
    packedDigit 2 row28Code j.val = row28Digit j.val := by
  decide +kernel

theorem scalar_28_check : packedDot 2 row28Code columnCode 64 % 3 = 0 % 3 := by
  decide +kernel

theorem actual_row_28_dot :
    (a *ᵥ (fun j => a j 0)) (28 : Fin 64) = 0 := by
  apply selected_packed_row_dot_mod 3 64 2 CFSG.Models.MatrixGroups.Suz.rows1
    (28 : Fin 64) (0 : Fin 64) row28Code columnCode 0
  · intro j
    exact (raw_row_28_binding j).trans (packed_row_28_binding j).symm
  · intro j
    exact (raw_column_binding j).trans (packed_column_binding j).symm
  · exact scalar_28_check

def row29Digit (j : ℕ) : ℕ :=
  match j with
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 2
  | 4 => 1
  | 5 => 0
  | 6 => 1
  | 7 => 2
  | 8 => 2
  | 9 => 2
  | 10 => 0
  | 11 => 0
  | 12 => 1
  | 13 => 2
  | 14 => 1
  | 15 => 1
  | 16 => 1
  | 17 => 1
  | 18 => 1
  | 19 => 0
  | 20 => 0
  | 21 => 0
  | 22 => 0
  | 23 => 2
  | 24 => 2
  | 25 => 0
  | 26 => 1
  | 27 => 2
  | 28 => 0
  | 29 => 0
  | 30 => 2
  | 31 => 0
  | 32 => 2
  | 33 => 1
  | 34 => 2
  | 35 => 1
  | 36 => 2
  | 37 => 1
  | 38 => 1
  | 39 => 2
  | 40 => 2
  | 41 => 1
  | 42 => 1
  | 43 => 2
  | 44 => 0
  | 45 => 1
  | 46 => 1
  | 47 => 1
  | 48 => 0
  | 49 => 1
  | 50 => 0
  | 51 => 1
  | 52 => 1
  | 53 => 2
  | 54 => 0
  | 55 => 0
  | 56 => 2
  | 57 => 1
  | 58 => 0
  | 59 => 1
  | 60 => 0
  | 61 => 0
  | 62 => 0
  | 63 => 1
  | _ => 0

def row29Code : ℕ := 85434240465712327571672143786471494016

theorem raw_row_29_binding : ∀ j : Fin 64,
    rawDigit CFSG.Models.MatrixGroups.Suz.rows1 29 j.val = row29Digit j.val := by
  decide +kernel

theorem packed_row_29_binding : ∀ j : Fin 64,
    packedDigit 2 row29Code j.val = row29Digit j.val := by
  decide +kernel

theorem scalar_29_check : packedDot 2 row29Code columnCode 64 % 3 = 0 % 3 := by
  decide +kernel

theorem actual_row_29_dot :
    (a *ᵥ (fun j => a j 0)) (29 : Fin 64) = 0 := by
  apply selected_packed_row_dot_mod 3 64 2 CFSG.Models.MatrixGroups.Suz.rows1
    (29 : Fin 64) (0 : Fin 64) row29Code columnCode 0
  · intro j
    exact (raw_row_29_binding j).trans (packed_row_29_binding j).symm
  · intro j
    exact (raw_column_binding j).trans (packed_column_binding j).symm
  · exact scalar_29_check

def row30Digit (j : ℕ) : ℕ :=
  match j with
  | 0 => 2
  | 1 => 2
  | 2 => 2
  | 3 => 1
  | 4 => 1
  | 5 => 0
  | 6 => 2
  | 7 => 1
  | 8 => 0
  | 9 => 0
  | 10 => 0
  | 11 => 0
  | 12 => 1
  | 13 => 2
  | 14 => 1
  | 15 => 1
  | 16 => 0
  | 17 => 0
  | 18 => 2
  | 19 => 2
  | 20 => 0
  | 21 => 2
  | 22 => 1
  | 23 => 0
  | 24 => 1
  | 25 => 1
  | 26 => 1
  | 27 => 1
  | 28 => 2
  | 29 => 2
  | 30 => 1
  | 31 => 2
  | 32 => 2
  | 33 => 1
  | 34 => 2
  | 35 => 1
  | 36 => 2
  | 37 => 1
  | 38 => 2
  | 39 => 0
  | 40 => 1
  | 41 => 2
  | 42 => 1
  | 43 => 0
  | 44 => 2
  | 45 => 0
  | 46 => 2
  | 47 => 0
  | 48 => 1
  | 49 => 2
  | 50 => 0
  | 51 => 0
  | 52 => 2
  | 53 => 1
  | 54 => 2
  | 55 => 2
  | 56 => 2
  | 57 => 2
  | 58 => 1
  | 59 => 1
  | 60 => 0
  | 61 => 2
  | 62 => 0
  | 63 => 0
  | _ => 0

def row30Code : ℕ := 11104498287148025097498779300212531562

theorem raw_row_30_binding : ∀ j : Fin 64,
    rawDigit CFSG.Models.MatrixGroups.Suz.rows1 30 j.val = row30Digit j.val := by
  decide +kernel

theorem packed_row_30_binding : ∀ j : Fin 64,
    packedDigit 2 row30Code j.val = row30Digit j.val := by
  decide +kernel

theorem scalar_30_check : packedDot 2 row30Code columnCode 64 % 3 = 0 % 3 := by
  decide +kernel

theorem actual_row_30_dot :
    (a *ᵥ (fun j => a j 0)) (30 : Fin 64) = 0 := by
  apply selected_packed_row_dot_mod 3 64 2 CFSG.Models.MatrixGroups.Suz.rows1
    (30 : Fin 64) (0 : Fin 64) row30Code columnCode 0
  · intro j
    exact (raw_row_30_binding j).trans (packed_row_30_binding j).symm
  · intro j
    exact (raw_column_binding j).trans (packed_column_binding j).symm
  · exact scalar_30_check

def row31Digit (j : ℕ) : ℕ :=
  match j with
  | 0 => 0
  | 1 => 2
  | 2 => 0
  | 3 => 2
  | 4 => 2
  | 5 => 1
  | 6 => 1
  | 7 => 0
  | 8 => 0
  | 9 => 2
  | 10 => 0
  | 11 => 0
  | 12 => 2
  | 13 => 2
  | 14 => 2
  | 15 => 2
  | 16 => 2
  | 17 => 1
  | 18 => 1
  | 19 => 2
  | 20 => 1
  | 21 => 0
  | 22 => 0
  | 23 => 0
  | 24 => 2
  | 25 => 1
  | 26 => 0
  | 27 => 0
  | 28 => 2
  | 29 => 0
  | 30 => 2
  | 31 => 0
  | 32 => 2
  | 33 => 2
  | 34 => 0
  | 35 => 2
  | 36 => 1
  | 37 => 2
  | 38 => 1
  | 39 => 2
  | 40 => 0
  | 41 => 0
  | 42 => 1
  | 43 => 1
  | 44 => 0
  | 45 => 0
  | 46 => 2
  | 47 => 2
  | 48 => 2
  | 49 => 1
  | 50 => 1
  | 51 => 2
  | 52 => 2
  | 53 => 0
  | 54 => 1
  | 55 => 0
  | 56 => 1
  | 57 => 0
  | 58 => 2
  | 59 => 0
  | 60 => 1
  | 61 => 1
  | 62 => 0
  | 63 => 1
  | _ => 0

def row31Code : ℕ := 91888454522703128118981054971660211848

theorem raw_row_31_binding : ∀ j : Fin 64,
    rawDigit CFSG.Models.MatrixGroups.Suz.rows1 31 j.val = row31Digit j.val := by
  decide +kernel

theorem packed_row_31_binding : ∀ j : Fin 64,
    packedDigit 2 row31Code j.val = row31Digit j.val := by
  decide +kernel

theorem scalar_31_check : packedDot 2 row31Code columnCode 64 % 3 = 0 % 3 := by
  decide +kernel

theorem actual_row_31_dot :
    (a *ᵥ (fun j => a j 0)) (31 : Fin 64) = 0 := by
  apply selected_packed_row_dot_mod 3 64 2 CFSG.Models.MatrixGroups.Suz.rows1
    (31 : Fin 64) (0 : Fin 64) row31Code columnCode 0
  · intro j
    exact (raw_row_31_binding j).trans (packed_row_31_binding j).symm
  · intro j
    exact (raw_column_binding j).trans (packed_column_binding j).symm
  · exact scalar_31_check

end SymmetricSubgroupAsymptotics.CFSGSuzPackedRows24To31
