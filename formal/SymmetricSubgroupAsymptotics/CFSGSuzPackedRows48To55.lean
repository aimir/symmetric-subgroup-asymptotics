import SymmetricSubgroupAsymptotics.CFSGSuzPackedRowZeroPilot

/-! Exactly rows48 through55.
Generated from one hash-guarded first Suz matrix and its first column only.
Literal data require the closed kernel bindings and scalar checks below.
No resource limit is raised. The checked row-zero pilot supplies the shared
column and row-zero theorem; its source bytes are guarded by the producer. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGSuzPackedRows48To55
open MatrixNaturalRowDotReflection
open CFSGSuzPackedRowZeroPilot

def row48Digit (j : ℕ) : ℕ :=
  match j with
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 0
  | 4 => 0
  | 5 => 0
  | 6 => 0
  | 7 => 1
  | 8 => 0
  | 9 => 2
  | 10 => 2
  | 11 => 2
  | 12 => 0
  | 13 => 0
  | 14 => 0
  | 15 => 0
  | 16 => 1
  | 17 => 0
  | 18 => 1
  | 19 => 2
  | 20 => 0
  | 21 => 0
  | 22 => 1
  | 23 => 0
  | 24 => 2
  | 25 => 2
  | 26 => 1
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
  | 37 => 0
  | 38 => 1
  | 39 => 2
  | 40 => 1
  | 41 => 0
  | 42 => 1
  | 43 => 1
  | 44 => 1
  | 45 => 2
  | 46 => 0
  | 47 => 0
  | 48 => 2
  | 49 => 1
  | 50 => 0
  | 51 => 0
  | 52 => 1
  | 53 => 1
  | 54 => 2
  | 55 => 2
  | 56 => 2
  | 57 => 1
  | 58 => 0
  | 59 => 1
  | 60 => 2
  | 61 => 1
  | 62 => 1
  | 63 => 0
  | _ => 0

def row48Code : ℕ := 29609823763203144734143640774359138320

theorem raw_row_48_binding : ∀ j : Fin 64,
    rawDigit CFSG.Models.MatrixGroups.Suz.rows1 48 j.val = row48Digit j.val := by
  decide +kernel

theorem packed_row_48_binding : ∀ j : Fin 64,
    packedDigit 2 row48Code j.val = row48Digit j.val := by
  decide +kernel

theorem scalar_48_check : packedDot 2 row48Code columnCode 64 % 3 = 0 % 3 := by
  decide +kernel

theorem actual_row_48_dot :
    (a *ᵥ (fun j => a j 0)) (48 : Fin 64) = 0 := by
  apply selected_packed_row_dot_mod 3 64 2 CFSG.Models.MatrixGroups.Suz.rows1
    (48 : Fin 64) (0 : Fin 64) row48Code columnCode 0
  · intro j
    exact (raw_row_48_binding j).trans (packed_row_48_binding j).symm
  · intro j
    exact (raw_column_binding j).trans (packed_column_binding j).symm
  · exact scalar_48_check

def row49Digit (j : ℕ) : ℕ :=
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
  | 9 => 1
  | 10 => 1
  | 11 => 1
  | 12 => 1
  | 13 => 2
  | 14 => 2
  | 15 => 2
  | 16 => 1
  | 17 => 1
  | 18 => 1
  | 19 => 2
  | 20 => 0
  | 21 => 1
  | 22 => 2
  | 23 => 2
  | 24 => 1
  | 25 => 0
  | 26 => 2
  | 27 => 2
  | 28 => 2
  | 29 => 0
  | 30 => 1
  | 31 => 1
  | 32 => 0
  | 33 => 2
  | 34 => 0
  | 35 => 1
  | 36 => 0
  | 37 => 2
  | 38 => 1
  | 39 => 2
  | 40 => 0
  | 41 => 2
  | 42 => 0
  | 43 => 1
  | 44 => 1
  | 45 => 1
  | 46 => 0
  | 47 => 1
  | 48 => 2
  | 49 => 2
  | 50 => 2
  | 51 => 2
  | 52 => 1
  | 53 => 0
  | 54 => 2
  | 55 => 1
  | 56 => 2
  | 57 => 0
  | 58 => 1
  | 59 => 0
  | 60 => 0
  | 61 => 0
  | 62 => 2
  | 63 => 0
  | _ => 0

def row49Code : ℕ := 42630738092532343937714142329550744069

theorem raw_row_49_binding : ∀ j : Fin 64,
    rawDigit CFSG.Models.MatrixGroups.Suz.rows1 49 j.val = row49Digit j.val := by
  decide +kernel

theorem packed_row_49_binding : ∀ j : Fin 64,
    packedDigit 2 row49Code j.val = row49Digit j.val := by
  decide +kernel

theorem scalar_49_check : packedDot 2 row49Code columnCode 64 % 3 = 0 % 3 := by
  decide +kernel

theorem actual_row_49_dot :
    (a *ᵥ (fun j => a j 0)) (49 : Fin 64) = 0 := by
  apply selected_packed_row_dot_mod 3 64 2 CFSG.Models.MatrixGroups.Suz.rows1
    (49 : Fin 64) (0 : Fin 64) row49Code columnCode 0
  · intro j
    exact (raw_row_49_binding j).trans (packed_row_49_binding j).symm
  · intro j
    exact (raw_column_binding j).trans (packed_column_binding j).symm
  · exact scalar_49_check

def row50Digit (j : ℕ) : ℕ :=
  match j with
  | 0 => 1
  | 1 => 0
  | 2 => 1
  | 3 => 0
  | 4 => 0
  | 5 => 1
  | 6 => 0
  | 7 => 2
  | 8 => 1
  | 9 => 1
  | 10 => 0
  | 11 => 2
  | 12 => 1
  | 13 => 1
  | 14 => 1
  | 15 => 2
  | 16 => 1
  | 17 => 0
  | 18 => 1
  | 19 => 2
  | 20 => 0
  | 21 => 0
  | 22 => 0
  | 23 => 1
  | 24 => 2
  | 25 => 2
  | 26 => 2
  | 27 => 0
  | 28 => 1
  | 29 => 0
  | 30 => 0
  | 31 => 0
  | 32 => 0
  | 33 => 0
  | 34 => 2
  | 35 => 0
  | 36 => 2
  | 37 => 1
  | 38 => 2
  | 39 => 2
  | 40 => 1
  | 41 => 1
  | 42 => 0
  | 43 => 0
  | 44 => 2
  | 45 => 1
  | 46 => 1
  | 47 => 2
  | 48 => 0
  | 49 => 0
  | 50 => 1
  | 51 => 2
  | 52 => 1
  | 53 => 0
  | 54 => 0
  | 55 => 2
  | 56 => 1
  | 57 => 1
  | 58 => 0
  | 59 => 1
  | 60 => 1
  | 61 => 1
  | 62 => 0
  | 63 => 2
  | _ => 0

def row50Code : ℕ := 177148219808756567927639996641231340561

theorem raw_row_50_binding : ∀ j : Fin 64,
    rawDigit CFSG.Models.MatrixGroups.Suz.rows1 50 j.val = row50Digit j.val := by
  decide +kernel

theorem packed_row_50_binding : ∀ j : Fin 64,
    packedDigit 2 row50Code j.val = row50Digit j.val := by
  decide +kernel

theorem scalar_50_check : packedDot 2 row50Code columnCode 64 % 3 = 0 % 3 := by
  decide +kernel

theorem actual_row_50_dot :
    (a *ᵥ (fun j => a j 0)) (50 : Fin 64) = 0 := by
  apply selected_packed_row_dot_mod 3 64 2 CFSG.Models.MatrixGroups.Suz.rows1
    (50 : Fin 64) (0 : Fin 64) row50Code columnCode 0
  · intro j
    exact (raw_row_50_binding j).trans (packed_row_50_binding j).symm
  · intro j
    exact (raw_column_binding j).trans (packed_column_binding j).symm
  · exact scalar_50_check

def row51Digit (j : ℕ) : ℕ :=
  match j with
  | 0 => 0
  | 1 => 1
  | 2 => 0
  | 3 => 2
  | 4 => 0
  | 5 => 1
  | 6 => 2
  | 7 => 2
  | 8 => 1
  | 9 => 1
  | 10 => 1
  | 11 => 1
  | 12 => 0
  | 13 => 0
  | 14 => 2
  | 15 => 0
  | 16 => 0
  | 17 => 1
  | 18 => 2
  | 19 => 1
  | 20 => 2
  | 21 => 1
  | 22 => 2
  | 23 => 0
  | 24 => 2
  | 25 => 1
  | 26 => 0
  | 27 => 0
  | 28 => 2
  | 29 => 2
  | 30 => 1
  | 31 => 0
  | 32 => 2
  | 33 => 1
  | 34 => 2
  | 35 => 2
  | 36 => 0
  | 37 => 2
  | 38 => 0
  | 39 => 2
  | 40 => 2
  | 41 => 1
  | 42 => 2
  | 43 => 1
  | 44 => 1
  | 45 => 2
  | 46 => 0
  | 47 => 1
  | 48 => 2
  | 49 => 2
  | 50 => 0
  | 51 => 1
  | 52 => 0
  | 53 => 2
  | 54 => 0
  | 55 => 1
  | 56 => 0
  | 57 => 1
  | 58 => 2
  | 59 => 2
  | 60 => 0
  | 61 => 2
  | 62 => 0
  | 63 => 2
  | _ => 0

def row51Code : ℕ := 181628010330640120878263564927055012996

theorem raw_row_51_binding : ∀ j : Fin 64,
    rawDigit CFSG.Models.MatrixGroups.Suz.rows1 51 j.val = row51Digit j.val := by
  decide +kernel

theorem packed_row_51_binding : ∀ j : Fin 64,
    packedDigit 2 row51Code j.val = row51Digit j.val := by
  decide +kernel

theorem scalar_51_check : packedDot 2 row51Code columnCode 64 % 3 = 0 % 3 := by
  decide +kernel

theorem actual_row_51_dot :
    (a *ᵥ (fun j => a j 0)) (51 : Fin 64) = 0 := by
  apply selected_packed_row_dot_mod 3 64 2 CFSG.Models.MatrixGroups.Suz.rows1
    (51 : Fin 64) (0 : Fin 64) row51Code columnCode 0
  · intro j
    exact (raw_row_51_binding j).trans (packed_row_51_binding j).symm
  · intro j
    exact (raw_column_binding j).trans (packed_column_binding j).symm
  · exact scalar_51_check

def row52Digit (j : ℕ) : ℕ :=
  match j with
  | 0 => 1
  | 1 => 2
  | 2 => 1
  | 3 => 0
  | 4 => 0
  | 5 => 2
  | 6 => 0
  | 7 => 2
  | 8 => 0
  | 9 => 1
  | 10 => 0
  | 11 => 1
  | 12 => 1
  | 13 => 1
  | 14 => 1
  | 15 => 0
  | 16 => 2
  | 17 => 2
  | 18 => 0
  | 19 => 2
  | 20 => 1
  | 21 => 0
  | 22 => 2
  | 23 => 0
  | 24 => 1
  | 25 => 0
  | 26 => 2
  | 27 => 2
  | 28 => 2
  | 29 => 0
  | 30 => 2
  | 31 => 1
  | 32 => 1
  | 33 => 1
  | 34 => 0
  | 35 => 1
  | 36 => 0
  | 37 => 1
  | 38 => 1
  | 39 => 2
  | 40 => 2
  | 41 => 2
  | 42 => 0
  | 43 => 2
  | 44 => 2
  | 45 => 2
  | 46 => 1
  | 47 => 2
  | 48 => 2
  | 49 => 1
  | 50 => 2
  | 51 => 2
  | 52 => 0
  | 53 => 0
  | 54 => 2
  | 55 => 2
  | 56 => 2
  | 57 => 0
  | 58 => 2
  | 59 => 1
  | 60 => 1
  | 61 => 2
  | 62 => 0
  | 63 => 2
  | _ => 0

def row52Code : ℕ := 182616338899909672796331191754262087705

theorem raw_row_52_binding : ∀ j : Fin 64,
    rawDigit CFSG.Models.MatrixGroups.Suz.rows1 52 j.val = row52Digit j.val := by
  decide +kernel

theorem packed_row_52_binding : ∀ j : Fin 64,
    packedDigit 2 row52Code j.val = row52Digit j.val := by
  decide +kernel

theorem scalar_52_check : packedDot 2 row52Code columnCode 64 % 3 = 0 % 3 := by
  decide +kernel

theorem actual_row_52_dot :
    (a *ᵥ (fun j => a j 0)) (52 : Fin 64) = 0 := by
  apply selected_packed_row_dot_mod 3 64 2 CFSG.Models.MatrixGroups.Suz.rows1
    (52 : Fin 64) (0 : Fin 64) row52Code columnCode 0
  · intro j
    exact (raw_row_52_binding j).trans (packed_row_52_binding j).symm
  · intro j
    exact (raw_column_binding j).trans (packed_column_binding j).symm
  · exact scalar_52_check

def row53Digit (j : ℕ) : ℕ :=
  match j with
  | 0 => 0
  | 1 => 2
  | 2 => 1
  | 3 => 2
  | 4 => 2
  | 5 => 1
  | 6 => 2
  | 7 => 2
  | 8 => 2
  | 9 => 2
  | 10 => 0
  | 11 => 1
  | 12 => 0
  | 13 => 0
  | 14 => 2
  | 15 => 2
  | 16 => 1
  | 17 => 0
  | 18 => 0
  | 19 => 1
  | 20 => 0
  | 21 => 0
  | 22 => 2
  | 23 => 1
  | 24 => 1
  | 25 => 0
  | 26 => 2
  | 27 => 1
  | 28 => 2
  | 29 => 1
  | 30 => 1
  | 31 => 2
  | 32 => 1
  | 33 => 1
  | 34 => 0
  | 35 => 0
  | 36 => 1
  | 37 => 1
  | 38 => 0
  | 39 => 1
  | 40 => 1
  | 41 => 1
  | 42 => 1
  | 43 => 1
  | 44 => 2
  | 45 => 1
  | 46 => 2
  | 47 => 1
  | 48 => 0
  | 49 => 1
  | 50 => 0
  | 51 => 1
  | 52 => 1
  | 53 => 2
  | 54 => 1
  | 55 => 2
  | 56 => 0
  | 57 => 0
  | 58 => 2
  | 59 => 1
  | 60 => 1
  | 61 => 2
  | 62 => 1
  | 63 => 2
  | _ => 0

def row53Code : ℕ := 203873452481366437324972755038186940056

theorem raw_row_53_binding : ∀ j : Fin 64,
    rawDigit CFSG.Models.MatrixGroups.Suz.rows1 53 j.val = row53Digit j.val := by
  decide +kernel

theorem packed_row_53_binding : ∀ j : Fin 64,
    packedDigit 2 row53Code j.val = row53Digit j.val := by
  decide +kernel

theorem scalar_53_check : packedDot 2 row53Code columnCode 64 % 3 = 0 % 3 := by
  decide +kernel

theorem actual_row_53_dot :
    (a *ᵥ (fun j => a j 0)) (53 : Fin 64) = 0 := by
  apply selected_packed_row_dot_mod 3 64 2 CFSG.Models.MatrixGroups.Suz.rows1
    (53 : Fin 64) (0 : Fin 64) row53Code columnCode 0
  · intro j
    exact (raw_row_53_binding j).trans (packed_row_53_binding j).symm
  · intro j
    exact (raw_column_binding j).trans (packed_column_binding j).symm
  · exact scalar_53_check

def row54Digit (j : ℕ) : ℕ :=
  match j with
  | 0 => 1
  | 1 => 0
  | 2 => 1
  | 3 => 1
  | 4 => 0
  | 5 => 1
  | 6 => 2
  | 7 => 1
  | 8 => 1
  | 9 => 2
  | 10 => 2
  | 11 => 2
  | 12 => 1
  | 13 => 1
  | 14 => 2
  | 15 => 1
  | 16 => 2
  | 17 => 1
  | 18 => 0
  | 19 => 0
  | 20 => 2
  | 21 => 1
  | 22 => 2
  | 23 => 2
  | 24 => 2
  | 25 => 0
  | 26 => 0
  | 27 => 0
  | 28 => 2
  | 29 => 0
  | 30 => 0
  | 31 => 1
  | 32 => 0
  | 33 => 0
  | 34 => 2
  | 35 => 1
  | 36 => 1
  | 37 => 2
  | 38 => 2
  | 39 => 2
  | 40 => 1
  | 41 => 1
  | 42 => 1
  | 43 => 0
  | 44 => 0
  | 45 => 0
  | 46 => 1
  | 47 => 0
  | 48 => 2
  | 49 => 1
  | 50 => 1
  | 51 => 1
  | 52 => 0
  | 53 => 2
  | 54 => 0
  | 55 => 0
  | 56 => 2
  | 57 => 0
  | 58 => 1
  | 59 => 2
  | 60 => 2
  | 61 => 1
  | 62 => 2
  | 63 => 2
  | _ => 0

def row54Code : ℕ := 221410091719518872630826860154679026769

theorem raw_row_54_binding : ∀ j : Fin 64,
    rawDigit CFSG.Models.MatrixGroups.Suz.rows1 54 j.val = row54Digit j.val := by
  decide +kernel

theorem packed_row_54_binding : ∀ j : Fin 64,
    packedDigit 2 row54Code j.val = row54Digit j.val := by
  decide +kernel

theorem scalar_54_check : packedDot 2 row54Code columnCode 64 % 3 = 0 % 3 := by
  decide +kernel

theorem actual_row_54_dot :
    (a *ᵥ (fun j => a j 0)) (54 : Fin 64) = 0 := by
  apply selected_packed_row_dot_mod 3 64 2 CFSG.Models.MatrixGroups.Suz.rows1
    (54 : Fin 64) (0 : Fin 64) row54Code columnCode 0
  · intro j
    exact (raw_row_54_binding j).trans (packed_row_54_binding j).symm
  · intro j
    exact (raw_column_binding j).trans (packed_column_binding j).symm
  · exact scalar_54_check

def row55Digit (j : ℕ) : ℕ :=
  match j with
  | 0 => 2
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | 5 => 0
  | 6 => 1
  | 7 => 2
  | 8 => 2
  | 9 => 0
  | 10 => 0
  | 11 => 0
  | 12 => 1
  | 13 => 2
  | 14 => 1
  | 15 => 1
  | 16 => 0
  | 17 => 0
  | 18 => 1
  | 19 => 1
  | 20 => 2
  | 21 => 0
  | 22 => 0
  | 23 => 2
  | 24 => 2
  | 25 => 2
  | 26 => 0
  | 27 => 0
  | 28 => 2
  | 29 => 2
  | 30 => 0
  | 31 => 2
  | 32 => 0
  | 33 => 2
  | 34 => 1
  | 35 => 0
  | 36 => 0
  | 37 => 0
  | 38 => 1
  | 39 => 2
  | 40 => 1
  | 41 => 1
  | 42 => 1
  | 43 => 2
  | 44 => 0
  | 45 => 0
  | 46 => 2
  | 47 => 1
  | 48 => 1
  | 49 => 2
  | 50 => 0
  | 51 => 2
  | 52 => 2
  | 53 => 1
  | 54 => 0
  | 55 => 0
  | 56 => 0
  | 57 => 0
  | 58 => 1
  | 59 => 2
  | 60 => 1
  | 61 => 2
  | 62 => 1
  | 63 => 0
  | _ => 0

def row55Code : ℕ := 33978523220859169728754365328598929750

theorem raw_row_55_binding : ∀ j : Fin 64,
    rawDigit CFSG.Models.MatrixGroups.Suz.rows1 55 j.val = row55Digit j.val := by
  decide +kernel

theorem packed_row_55_binding : ∀ j : Fin 64,
    packedDigit 2 row55Code j.val = row55Digit j.val := by
  decide +kernel

theorem scalar_55_check : packedDot 2 row55Code columnCode 64 % 3 = 0 % 3 := by
  decide +kernel

theorem actual_row_55_dot :
    (a *ᵥ (fun j => a j 0)) (55 : Fin 64) = 0 := by
  apply selected_packed_row_dot_mod 3 64 2 CFSG.Models.MatrixGroups.Suz.rows1
    (55 : Fin 64) (0 : Fin 64) row55Code columnCode 0
  · intro j
    exact (raw_row_55_binding j).trans (packed_row_55_binding j).symm
  · intro j
    exact (raw_column_binding j).trans (packed_column_binding j).symm
  · exact scalar_55_check

end SymmetricSubgroupAsymptotics.CFSGSuzPackedRows48To55
