import SymmetricSubgroupAsymptotics.CFSGSuzPackedRowZeroPilot

/-! Exactly rows0 through7.
Generated from one hash-guarded first Suz matrix and its first column only.
Literal data require the closed kernel bindings and scalar checks below.
No resource limit is raised. The checked row-zero pilot supplies the shared
column and row-zero theorem; its source bytes are guarded by the producer. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGSuzPackedRows00To07
open MatrixNaturalRowDotReflection
open CFSGSuzPackedRowZeroPilot

theorem actual_row_00_dot :
    (a *ᵥ (fun j => a j 0)) (0 : Fin 64) = 1 :=
  CFSGSuzPackedRowZeroPilot.actual_row_zero_dot

def row01Digit (j : ℕ) : ℕ :=
  match j with
  | 0 => 1
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => 1
  | 6 => 2
  | 7 => 0
  | 8 => 0
  | 9 => 0
  | 10 => 2
  | 11 => 0
  | 12 => 2
  | 13 => 2
  | 14 => 0
  | 15 => 1
  | 16 => 0
  | 17 => 0
  | 18 => 2
  | 19 => 2
  | 20 => 0
  | 21 => 2
  | 22 => 1
  | 23 => 1
  | 24 => 1
  | 25 => 0
  | 26 => 2
  | 27 => 1
  | 28 => 2
  | 29 => 0
  | 30 => 2
  | 31 => 0
  | 32 => 1
  | 33 => 1
  | 34 => 1
  | 35 => 0
  | 36 => 2
  | 37 => 1
  | 38 => 2
  | 39 => 0
  | 40 => 2
  | 41 => 0
  | 42 => 1
  | 43 => 2
  | 44 => 2
  | 45 => 1
  | 46 => 0
  | 47 => 1
  | 48 => 2
  | 49 => 0
  | 50 => 2
  | 51 => 0
  | 52 => 2
  | 53 => 2
  | 54 => 0
  | 55 => 1
  | 56 => 1
  | 57 => 2
  | 58 => 1
  | 59 => 1
  | 60 => 2
  | 61 => 0
  | 62 => 1
  | 63 => 1
  | _ => 0

def row01Code : ℕ := 109460313688681530642593467373530915841

theorem raw_row_01_binding : ∀ j : Fin 64,
    rawDigit CFSG.Models.MatrixGroups.Suz.rows1 1 j.val = row01Digit j.val := by
  decide +kernel

theorem packed_row_01_binding : ∀ j : Fin 64,
    packedDigit 2 row01Code j.val = row01Digit j.val := by
  decide +kernel

theorem scalar_01_check : packedDot 2 row01Code columnCode 64 % 3 = 0 % 3 := by
  decide +kernel

theorem actual_row_01_dot :
    (a *ᵥ (fun j => a j 0)) (1 : Fin 64) = 0 := by
  apply selected_packed_row_dot_mod 3 64 2 CFSG.Models.MatrixGroups.Suz.rows1
    (1 : Fin 64) (0 : Fin 64) row01Code columnCode 0
  · intro j
    exact (raw_row_01_binding j).trans (packed_row_01_binding j).symm
  · intro j
    exact (raw_column_binding j).trans (packed_column_binding j).symm
  · exact scalar_01_check

def row02Digit (j : ℕ) : ℕ :=
  match j with
  | 0 => 2
  | 1 => 0
  | 2 => 2
  | 3 => 0
  | 4 => 1
  | 5 => 0
  | 6 => 0
  | 7 => 1
  | 8 => 0
  | 9 => 1
  | 10 => 0
  | 11 => 0
  | 12 => 2
  | 13 => 2
  | 14 => 0
  | 15 => 2
  | 16 => 2
  | 17 => 0
  | 18 => 2
  | 19 => 2
  | 20 => 0
  | 21 => 1
  | 22 => 0
  | 23 => 0
  | 24 => 0
  | 25 => 1
  | 26 => 0
  | 27 => 1
  | 28 => 2
  | 29 => 1
  | 30 => 0
  | 31 => 2
  | 32 => 0
  | 33 => 2
  | 34 => 0
  | 35 => 1
  | 36 => 1
  | 37 => 1
  | 38 => 2
  | 39 => 1
  | 40 => 0
  | 41 => 1
  | 42 => 0
  | 43 => 2
  | 44 => 0
  | 45 => 2
  | 46 => 0
  | 47 => 0
  | 48 => 1
  | 49 => 2
  | 50 => 2
  | 51 => 2
  | 52 => 1
  | 53 => 1
  | 54 => 2
  | 55 => 1
  | 56 => 1
  | 57 => 0
  | 58 => 2
  | 59 => 2
  | 60 => 0
  | 61 => 0
  | 62 => 1
  | 63 => 1
  | _ => 0

def row02Code : ℕ := 107176261372582747393498944450498674978

theorem raw_row_02_binding : ∀ j : Fin 64,
    rawDigit CFSG.Models.MatrixGroups.Suz.rows1 2 j.val = row02Digit j.val := by
  decide +kernel

theorem packed_row_02_binding : ∀ j : Fin 64,
    packedDigit 2 row02Code j.val = row02Digit j.val := by
  decide +kernel

theorem scalar_02_check : packedDot 2 row02Code columnCode 64 % 3 = 0 % 3 := by
  decide +kernel

theorem actual_row_02_dot :
    (a *ᵥ (fun j => a j 0)) (2 : Fin 64) = 0 := by
  apply selected_packed_row_dot_mod 3 64 2 CFSG.Models.MatrixGroups.Suz.rows1
    (2 : Fin 64) (0 : Fin 64) row02Code columnCode 0
  · intro j
    exact (raw_row_02_binding j).trans (packed_row_02_binding j).symm
  · intro j
    exact (raw_column_binding j).trans (packed_column_binding j).symm
  · exact scalar_02_check

def row03Digit (j : ℕ) : ℕ :=
  match j with
  | 0 => 1
  | 1 => 1
  | 2 => 0
  | 3 => 0
  | 4 => 2
  | 5 => 2
  | 6 => 2
  | 7 => 0
  | 8 => 1
  | 9 => 2
  | 10 => 1
  | 11 => 0
  | 12 => 0
  | 13 => 1
  | 14 => 1
  | 15 => 0
  | 16 => 2
  | 17 => 0
  | 18 => 0
  | 19 => 1
  | 20 => 1
  | 21 => 2
  | 22 => 1
  | 23 => 0
  | 24 => 0
  | 25 => 2
  | 26 => 1
  | 27 => 1
  | 28 => 0
  | 29 => 0
  | 30 => 0
  | 31 => 1
  | 32 => 0
  | 33 => 0
  | 34 => 2
  | 35 => 1
  | 36 => 2
  | 37 => 2
  | 38 => 2
  | 39 => 1
  | 40 => 1
  | 41 => 2
  | 42 => 2
  | 43 => 2
  | 44 => 1
  | 45 => 2
  | 46 => 2
  | 47 => 0
  | 48 => 1
  | 49 => 2
  | 50 => 1
  | 51 => 0
  | 52 => 1
  | 53 => 0
  | 54 => 0
  | 55 => 2
  | 56 => 2
  | 57 => 0
  | 58 => 1
  | 59 => 2
  | 60 => 2
  | 61 => 2
  | 62 => 0
  | 63 => 0
  | _ => 0

def row03Code : ℕ := 14052973723631873697457771095608863237

theorem raw_row_03_binding : ∀ j : Fin 64,
    rawDigit CFSG.Models.MatrixGroups.Suz.rows1 3 j.val = row03Digit j.val := by
  decide +kernel

theorem packed_row_03_binding : ∀ j : Fin 64,
    packedDigit 2 row03Code j.val = row03Digit j.val := by
  decide +kernel

theorem scalar_03_check : packedDot 2 row03Code columnCode 64 % 3 = 0 % 3 := by
  decide +kernel

theorem actual_row_03_dot :
    (a *ᵥ (fun j => a j 0)) (3 : Fin 64) = 0 := by
  apply selected_packed_row_dot_mod 3 64 2 CFSG.Models.MatrixGroups.Suz.rows1
    (3 : Fin 64) (0 : Fin 64) row03Code columnCode 0
  · intro j
    exact (raw_row_03_binding j).trans (packed_row_03_binding j).symm
  · intro j
    exact (raw_column_binding j).trans (packed_column_binding j).symm
  · exact scalar_03_check

def row04Digit (j : ℕ) : ℕ :=
  match j with
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 0
  | 4 => 0
  | 5 => 2
  | 6 => 1
  | 7 => 1
  | 8 => 2
  | 9 => 0
  | 10 => 2
  | 11 => 1
  | 12 => 0
  | 13 => 1
  | 14 => 0
  | 15 => 2
  | 16 => 2
  | 17 => 2
  | 18 => 1
  | 19 => 0
  | 20 => 0
  | 21 => 2
  | 22 => 2
  | 23 => 0
  | 24 => 2
  | 25 => 0
  | 26 => 0
  | 27 => 0
  | 28 => 1
  | 29 => 0
  | 30 => 2
  | 31 => 1
  | 32 => 1
  | 33 => 2
  | 34 => 1
  | 35 => 1
  | 36 => 1
  | 37 => 1
  | 38 => 2
  | 39 => 0
  | 40 => 0
  | 41 => 1
  | 42 => 1
  | 43 => 2
  | 44 => 2
  | 45 => 2
  | 46 => 2
  | 47 => 1
  | 48 => 1
  | 49 => 0
  | 50 => 0
  | 51 => 0
  | 52 => 2
  | 53 => 0
  | 54 => 0
  | 55 => 2
  | 56 => 0
  | 57 => 2
  | 58 => 0
  | 59 => 2
  | 60 => 1
  | 61 => 0
  | 62 => 0
  | 63 => 2
  | _ => 0

def row04Code : ℕ := 172179200654476029832166533818843551781

theorem raw_row_04_binding : ∀ j : Fin 64,
    rawDigit CFSG.Models.MatrixGroups.Suz.rows1 4 j.val = row04Digit j.val := by
  decide +kernel

theorem packed_row_04_binding : ∀ j : Fin 64,
    packedDigit 2 row04Code j.val = row04Digit j.val := by
  decide +kernel

theorem scalar_04_check : packedDot 2 row04Code columnCode 64 % 3 = 0 % 3 := by
  decide +kernel

theorem actual_row_04_dot :
    (a *ᵥ (fun j => a j 0)) (4 : Fin 64) = 0 := by
  apply selected_packed_row_dot_mod 3 64 2 CFSG.Models.MatrixGroups.Suz.rows1
    (4 : Fin 64) (0 : Fin 64) row04Code columnCode 0
  · intro j
    exact (raw_row_04_binding j).trans (packed_row_04_binding j).symm
  · intro j
    exact (raw_column_binding j).trans (packed_column_binding j).symm
  · exact scalar_04_check

def row05Digit (j : ℕ) : ℕ :=
  match j with
  | 0 => 1
  | 1 => 0
  | 2 => 1
  | 3 => 0
  | 4 => 2
  | 5 => 1
  | 6 => 1
  | 7 => 1
  | 8 => 1
  | 9 => 2
  | 10 => 1
  | 11 => 0
  | 12 => 2
  | 13 => 1
  | 14 => 2
  | 15 => 0
  | 16 => 1
  | 17 => 2
  | 18 => 2
  | 19 => 2
  | 20 => 0
  | 21 => 2
  | 22 => 1
  | 23 => 0
  | 24 => 1
  | 25 => 2
  | 26 => 1
  | 27 => 0
  | 28 => 1
  | 29 => 0
  | 30 => 2
  | 31 => 1
  | 32 => 1
  | 33 => 2
  | 34 => 2
  | 35 => 2
  | 36 => 1
  | 37 => 0
  | 38 => 0
  | 39 => 0
  | 40 => 2
  | 41 => 1
  | 42 => 2
  | 43 => 1
  | 44 => 2
  | 45 => 1
  | 46 => 0
  | 47 => 2
  | 48 => 2
  | 49 => 2
  | 50 => 1
  | 51 => 2
  | 52 => 2
  | 53 => 1
  | 54 => 2
  | 55 => 2
  | 56 => 2
  | 57 => 0
  | 58 => 1
  | 59 => 2
  | 60 => 0
  | 61 => 2
  | 62 => 0
  | 63 => 0
  | _ => 0

def row05Code : ℕ := 11395278430350954787518086918155359761

theorem raw_row_05_binding : ∀ j : Fin 64,
    rawDigit CFSG.Models.MatrixGroups.Suz.rows1 5 j.val = row05Digit j.val := by
  decide +kernel

theorem packed_row_05_binding : ∀ j : Fin 64,
    packedDigit 2 row05Code j.val = row05Digit j.val := by
  decide +kernel

theorem scalar_05_check : packedDot 2 row05Code columnCode 64 % 3 = 0 % 3 := by
  decide +kernel

theorem actual_row_05_dot :
    (a *ᵥ (fun j => a j 0)) (5 : Fin 64) = 0 := by
  apply selected_packed_row_dot_mod 3 64 2 CFSG.Models.MatrixGroups.Suz.rows1
    (5 : Fin 64) (0 : Fin 64) row05Code columnCode 0
  · intro j
    exact (raw_row_05_binding j).trans (packed_row_05_binding j).symm
  · intro j
    exact (raw_column_binding j).trans (packed_column_binding j).symm
  · exact scalar_05_check

def row06Digit (j : ℕ) : ℕ :=
  match j with
  | 0 => 0
  | 1 => 1
  | 2 => 0
  | 3 => 2
  | 4 => 1
  | 5 => 1
  | 6 => 0
  | 7 => 1
  | 8 => 2
  | 9 => 0
  | 10 => 1
  | 11 => 1
  | 12 => 2
  | 13 => 0
  | 14 => 2
  | 15 => 2
  | 16 => 1
  | 17 => 2
  | 18 => 2
  | 19 => 2
  | 20 => 2
  | 21 => 0
  | 22 => 1
  | 23 => 2
  | 24 => 2
  | 25 => 0
  | 26 => 1
  | 27 => 2
  | 28 => 1
  | 29 => 0
  | 30 => 0
  | 31 => 2
  | 32 => 0
  | 33 => 0
  | 34 => 0
  | 35 => 0
  | 36 => 0
  | 37 => 2
  | 38 => 1
  | 39 => 0
  | 40 => 1
  | 41 => 2
  | 42 => 2
  | 43 => 1
  | 44 => 1
  | 45 => 1
  | 46 => 1
  | 47 => 2
  | 48 => 1
  | 49 => 1
  | 50 => 1
  | 51 => 0
  | 52 => 0
  | 53 => 1
  | 54 => 2
  | 55 => 2
  | 56 => 0
  | 57 => 0
  | 58 => 1
  | 59 => 0
  | 60 => 1
  | 61 => 0
  | 62 => 2
  | 63 => 1
  | _ => 0

def row06Code : ℕ := 129021520366080125607798616011679352196

theorem raw_row_06_binding : ∀ j : Fin 64,
    rawDigit CFSG.Models.MatrixGroups.Suz.rows1 6 j.val = row06Digit j.val := by
  decide +kernel

theorem packed_row_06_binding : ∀ j : Fin 64,
    packedDigit 2 row06Code j.val = row06Digit j.val := by
  decide +kernel

theorem scalar_06_check : packedDot 2 row06Code columnCode 64 % 3 = 0 % 3 := by
  decide +kernel

theorem actual_row_06_dot :
    (a *ᵥ (fun j => a j 0)) (6 : Fin 64) = 0 := by
  apply selected_packed_row_dot_mod 3 64 2 CFSG.Models.MatrixGroups.Suz.rows1
    (6 : Fin 64) (0 : Fin 64) row06Code columnCode 0
  · intro j
    exact (raw_row_06_binding j).trans (packed_row_06_binding j).symm
  · intro j
    exact (raw_column_binding j).trans (packed_column_binding j).symm
  · exact scalar_06_check

def row07Digit (j : ℕ) : ℕ :=
  match j with
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 1
  | 4 => 1
  | 5 => 2
  | 6 => 0
  | 7 => 2
  | 8 => 0
  | 9 => 0
  | 10 => 0
  | 11 => 1
  | 12 => 2
  | 13 => 2
  | 14 => 2
  | 15 => 0
  | 16 => 1
  | 17 => 0
  | 18 => 2
  | 19 => 2
  | 20 => 0
  | 21 => 2
  | 22 => 1
  | 23 => 0
  | 24 => 2
  | 25 => 1
  | 26 => 1
  | 27 => 2
  | 28 => 1
  | 29 => 1
  | 30 => 2
  | 31 => 2
  | 32 => 2
  | 33 => 0
  | 34 => 0
  | 35 => 2
  | 36 => 1
  | 37 => 0
  | 38 => 0
  | 39 => 2
  | 40 => 0
  | 41 => 0
  | 42 => 2
  | 43 => 1
  | 44 => 2
  | 45 => 2
  | 46 => 0
  | 47 => 2
  | 48 => 2
  | 49 => 0
  | 50 => 1
  | 51 => 0
  | 52 => 2
  | 53 => 2
  | 54 => 1
  | 55 => 0
  | 56 => 1
  | 57 => 1
  | 58 => 2
  | 59 => 2
  | 60 => 2
  | 61 => 2
  | 62 => 1
  | 63 => 1
  | _ => 0

def row07Code : ℕ := 120487777413882895149552661626385107301

theorem raw_row_07_binding : ∀ j : Fin 64,
    rawDigit CFSG.Models.MatrixGroups.Suz.rows1 7 j.val = row07Digit j.val := by
  decide +kernel

theorem packed_row_07_binding : ∀ j : Fin 64,
    packedDigit 2 row07Code j.val = row07Digit j.val := by
  decide +kernel

theorem scalar_07_check : packedDot 2 row07Code columnCode 64 % 3 = 0 % 3 := by
  decide +kernel

theorem actual_row_07_dot :
    (a *ᵥ (fun j => a j 0)) (7 : Fin 64) = 0 := by
  apply selected_packed_row_dot_mod 3 64 2 CFSG.Models.MatrixGroups.Suz.rows1
    (7 : Fin 64) (0 : Fin 64) row07Code columnCode 0
  · intro j
    exact (raw_row_07_binding j).trans (packed_row_07_binding j).symm
  · intro j
    exact (raw_column_binding j).trans (packed_column_binding j).symm
  · exact scalar_07_check

end SymmetricSubgroupAsymptotics.CFSGSuzPackedRows00To07
