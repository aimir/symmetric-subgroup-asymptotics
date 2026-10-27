import SymmetricSubgroupAsymptotics.CFSGSuzPackedRowZeroPilot

/-! Exactly rows32 through39.
Generated from one hash-guarded first Suz matrix and its first column only.
Literal data require the closed kernel bindings and scalar checks below.
No resource limit is raised. The checked row-zero pilot supplies the shared
column and row-zero theorem; its source bytes are guarded by the producer. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGSuzPackedRows32To39
open MatrixNaturalRowDotReflection
open CFSGSuzPackedRowZeroPilot

def row32Digit (j : ℕ) : ℕ :=
  match j with
  | 0 => 1
  | 1 => 0
  | 2 => 1
  | 3 => 2
  | 4 => 2
  | 5 => 2
  | 6 => 0
  | 7 => 2
  | 8 => 1
  | 9 => 0
  | 10 => 0
  | 11 => 2
  | 12 => 0
  | 13 => 1
  | 14 => 0
  | 15 => 2
  | 16 => 2
  | 17 => 2
  | 18 => 2
  | 19 => 2
  | 20 => 1
  | 21 => 0
  | 22 => 1
  | 23 => 2
  | 24 => 0
  | 25 => 1
  | 26 => 2
  | 27 => 2
  | 28 => 0
  | 29 => 1
  | 30 => 1
  | 31 => 2
  | 32 => 2
  | 33 => 0
  | 34 => 1
  | 35 => 1
  | 36 => 2
  | 37 => 1
  | 38 => 1
  | 39 => 0
  | 40 => 1
  | 41 => 1
  | 42 => 1
  | 43 => 0
  | 44 => 2
  | 45 => 0
  | 46 => 0
  | 47 => 2
  | 48 => 2
  | 49 => 0
  | 50 => 2
  | 51 => 1
  | 52 => 1
  | 53 => 0
  | 54 => 0
  | 55 => 0
  | 56 => 1
  | 57 => 0
  | 58 => 1
  | 59 => 2
  | 60 => 1
  | 61 => 1
  | 62 => 1
  | 63 => 0
  | _ => 0

def row32Code : ℕ := 28666699042998857521085627646798301841

theorem raw_row_32_binding : ∀ j : Fin 64,
    rawDigit CFSG.Models.MatrixGroups.Suz.rows1 32 j.val = row32Digit j.val := by
  decide +kernel

theorem packed_row_32_binding : ∀ j : Fin 64,
    packedDigit 2 row32Code j.val = row32Digit j.val := by
  decide +kernel

theorem scalar_32_check : packedDot 2 row32Code columnCode 64 % 3 = 0 % 3 := by
  decide +kernel

theorem actual_row_32_dot :
    (a *ᵥ (fun j => a j 0)) (32 : Fin 64) = 0 := by
  apply selected_packed_row_dot_mod 3 64 2 CFSG.Models.MatrixGroups.Suz.rows1
    (32 : Fin 64) (0 : Fin 64) row32Code columnCode 0
  · intro j
    exact (raw_row_32_binding j).trans (packed_row_32_binding j).symm
  · intro j
    exact (raw_column_binding j).trans (packed_column_binding j).symm
  · exact scalar_32_check

def row33Digit (j : ℕ) : ℕ :=
  match j with
  | 0 => 2
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | 5 => 0
  | 6 => 0
  | 7 => 1
  | 8 => 2
  | 9 => 1
  | 10 => 1
  | 11 => 1
  | 12 => 1
  | 13 => 2
  | 14 => 1
  | 15 => 0
  | 16 => 2
  | 17 => 1
  | 18 => 1
  | 19 => 0
  | 20 => 2
  | 21 => 2
  | 22 => 2
  | 23 => 2
  | 24 => 0
  | 25 => 1
  | 26 => 2
  | 27 => 1
  | 28 => 0
  | 29 => 0
  | 30 => 1
  | 31 => 1
  | 32 => 1
  | 33 => 2
  | 34 => 1
  | 35 => 1
  | 36 => 1
  | 37 => 0
  | 38 => 0
  | 39 => 0
  | 40 => 2
  | 41 => 1
  | 42 => 0
  | 43 => 1
  | 44 => 0
  | 45 => 1
  | 46 => 2
  | 47 => 0
  | 48 => 1
  | 49 => 1
  | 50 => 2
  | 51 => 1
  | 52 => 0
  | 53 => 2
  | 54 => 1
  | 55 => 1
  | 56 => 0
  | 57 => 1
  | 58 => 1
  | 59 => 2
  | 60 => 0
  | 61 => 0
  | 62 => 2
  | 63 => 1
  | _ => 0

def row33Code : ℕ := 128376140395730705106344489528403050838

theorem raw_row_33_binding : ∀ j : Fin 64,
    rawDigit CFSG.Models.MatrixGroups.Suz.rows1 33 j.val = row33Digit j.val := by
  decide +kernel

theorem packed_row_33_binding : ∀ j : Fin 64,
    packedDigit 2 row33Code j.val = row33Digit j.val := by
  decide +kernel

theorem scalar_33_check : packedDot 2 row33Code columnCode 64 % 3 = 0 % 3 := by
  decide +kernel

theorem actual_row_33_dot :
    (a *ᵥ (fun j => a j 0)) (33 : Fin 64) = 0 := by
  apply selected_packed_row_dot_mod 3 64 2 CFSG.Models.MatrixGroups.Suz.rows1
    (33 : Fin 64) (0 : Fin 64) row33Code columnCode 0
  · intro j
    exact (raw_row_33_binding j).trans (packed_row_33_binding j).symm
  · intro j
    exact (raw_column_binding j).trans (packed_column_binding j).symm
  · exact scalar_33_check

def row34Digit (j : ℕ) : ℕ :=
  match j with
  | 0 => 2
  | 1 => 0
  | 2 => 0
  | 3 => 2
  | 4 => 0
  | 5 => 0
  | 6 => 1
  | 7 => 1
  | 8 => 2
  | 9 => 2
  | 10 => 0
  | 11 => 2
  | 12 => 2
  | 13 => 0
  | 14 => 2
  | 15 => 2
  | 16 => 2
  | 17 => 1
  | 18 => 2
  | 19 => 0
  | 20 => 2
  | 21 => 0
  | 22 => 0
  | 23 => 2
  | 24 => 1
  | 25 => 0
  | 26 => 0
  | 27 => 1
  | 28 => 0
  | 29 => 1
  | 30 => 1
  | 31 => 2
  | 32 => 1
  | 33 => 1
  | 34 => 1
  | 35 => 2
  | 36 => 2
  | 37 => 2
  | 38 => 0
  | 39 => 2
  | 40 => 2
  | 41 => 1
  | 42 => 1
  | 43 => 2
  | 44 => 2
  | 45 => 1
  | 46 => 2
  | 47 => 0
  | 48 => 1
  | 49 => 2
  | 50 => 1
  | 51 => 1
  | 52 => 0
  | 53 => 1
  | 54 => 2
  | 55 => 1
  | 56 => 1
  | 57 => 2
  | 58 => 1
  | 59 => 1
  | 60 => 0
  | 61 => 2
  | 62 => 2
  | 63 => 0
  | _ => 0

def row34Code : ℕ := 53633269556015487203635710010111709314

theorem raw_row_34_binding : ∀ j : Fin 64,
    rawDigit CFSG.Models.MatrixGroups.Suz.rows1 34 j.val = row34Digit j.val := by
  decide +kernel

theorem packed_row_34_binding : ∀ j : Fin 64,
    packedDigit 2 row34Code j.val = row34Digit j.val := by
  decide +kernel

theorem scalar_34_check : packedDot 2 row34Code columnCode 64 % 3 = 0 % 3 := by
  decide +kernel

theorem actual_row_34_dot :
    (a *ᵥ (fun j => a j 0)) (34 : Fin 64) = 0 := by
  apply selected_packed_row_dot_mod 3 64 2 CFSG.Models.MatrixGroups.Suz.rows1
    (34 : Fin 64) (0 : Fin 64) row34Code columnCode 0
  · intro j
    exact (raw_row_34_binding j).trans (packed_row_34_binding j).symm
  · intro j
    exact (raw_column_binding j).trans (packed_column_binding j).symm
  · exact scalar_34_check

def row35Digit (j : ℕ) : ℕ :=
  match j with
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 0
  | 4 => 2
  | 5 => 0
  | 6 => 2
  | 7 => 0
  | 8 => 1
  | 9 => 2
  | 10 => 1
  | 11 => 1
  | 12 => 2
  | 13 => 0
  | 14 => 0
  | 15 => 1
  | 16 => 2
  | 17 => 1
  | 18 => 2
  | 19 => 0
  | 20 => 2
  | 21 => 2
  | 22 => 1
  | 23 => 1
  | 24 => 0
  | 25 => 0
  | 26 => 1
  | 27 => 2
  | 28 => 2
  | 29 => 2
  | 30 => 2
  | 31 => 2
  | 32 => 0
  | 33 => 1
  | 34 => 1
  | 35 => 0
  | 36 => 0
  | 37 => 2
  | 38 => 0
  | 39 => 1
  | 40 => 0
  | 41 => 0
  | 42 => 1
  | 43 => 1
  | 44 => 1
  | 45 => 2
  | 46 => 0
  | 47 => 2
  | 48 => 2
  | 49 => 0
  | 50 => 1
  | 51 => 0
  | 52 => 0
  | 53 => 2
  | 54 => 0
  | 55 => 1
  | 56 => 0
  | 57 => 2
  | 58 => 1
  | 59 => 1
  | 60 => 0
  | 61 => 1
  | 62 => 0
  | 63 => 2
  | _ => 0

def row35Code : ℕ := 175916479369254849034347331861240947220

theorem raw_row_35_binding : ∀ j : Fin 64,
    rawDigit CFSG.Models.MatrixGroups.Suz.rows1 35 j.val = row35Digit j.val := by
  decide +kernel

theorem packed_row_35_binding : ∀ j : Fin 64,
    packedDigit 2 row35Code j.val = row35Digit j.val := by
  decide +kernel

theorem scalar_35_check : packedDot 2 row35Code columnCode 64 % 3 = 0 % 3 := by
  decide +kernel

theorem actual_row_35_dot :
    (a *ᵥ (fun j => a j 0)) (35 : Fin 64) = 0 := by
  apply selected_packed_row_dot_mod 3 64 2 CFSG.Models.MatrixGroups.Suz.rows1
    (35 : Fin 64) (0 : Fin 64) row35Code columnCode 0
  · intro j
    exact (raw_row_35_binding j).trans (packed_row_35_binding j).symm
  · intro j
    exact (raw_column_binding j).trans (packed_column_binding j).symm
  · exact scalar_35_check

def row36Digit (j : ℕ) : ℕ :=
  match j with
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 0
  | 4 => 0
  | 5 => 2
  | 6 => 2
  | 7 => 0
  | 8 => 2
  | 9 => 2
  | 10 => 0
  | 11 => 1
  | 12 => 1
  | 13 => 0
  | 14 => 2
  | 15 => 1
  | 16 => 1
  | 17 => 0
  | 18 => 1
  | 19 => 1
  | 20 => 2
  | 21 => 2
  | 22 => 1
  | 23 => 0
  | 24 => 0
  | 25 => 2
  | 26 => 1
  | 27 => 1
  | 28 => 2
  | 29 => 1
  | 30 => 1
  | 31 => 1
  | 32 => 0
  | 33 => 0
  | 34 => 0
  | 35 => 0
  | 36 => 0
  | 37 => 0
  | 38 => 2
  | 39 => 1
  | 40 => 1
  | 41 => 1
  | 42 => 0
  | 43 => 1
  | 44 => 1
  | 45 => 1
  | 46 => 0
  | 47 => 0
  | 48 => 2
  | 49 => 2
  | 50 => 0
  | 51 => 2
  | 52 => 2
  | 53 => 2
  | 54 => 1
  | 55 => 2
  | 56 => 1
  | 57 => 2
  | 58 => 2
  | 59 => 2
  | 60 => 1
  | 61 => 1
  | 62 => 0
  | 63 => 2
  | _ => 0

def row36Code : ℕ := 177667956034682880575216110747345627156

theorem raw_row_36_binding : ∀ j : Fin 64,
    rawDigit CFSG.Models.MatrixGroups.Suz.rows1 36 j.val = row36Digit j.val := by
  decide +kernel

theorem packed_row_36_binding : ∀ j : Fin 64,
    packedDigit 2 row36Code j.val = row36Digit j.val := by
  decide +kernel

theorem scalar_36_check : packedDot 2 row36Code columnCode 64 % 3 = 0 % 3 := by
  decide +kernel

theorem actual_row_36_dot :
    (a *ᵥ (fun j => a j 0)) (36 : Fin 64) = 0 := by
  apply selected_packed_row_dot_mod 3 64 2 CFSG.Models.MatrixGroups.Suz.rows1
    (36 : Fin 64) (0 : Fin 64) row36Code columnCode 0
  · intro j
    exact (raw_row_36_binding j).trans (packed_row_36_binding j).symm
  · intro j
    exact (raw_column_binding j).trans (packed_column_binding j).symm
  · exact scalar_36_check

def row37Digit (j : ℕ) : ℕ :=
  match j with
  | 0 => 0
  | 1 => 2
  | 2 => 1
  | 3 => 0
  | 4 => 1
  | 5 => 0
  | 6 => 0
  | 7 => 2
  | 8 => 1
  | 9 => 1
  | 10 => 2
  | 11 => 1
  | 12 => 1
  | 13 => 0
  | 14 => 0
  | 15 => 0
  | 16 => 2
  | 17 => 0
  | 18 => 0
  | 19 => 0
  | 20 => 0
  | 21 => 1
  | 22 => 1
  | 23 => 0
  | 24 => 0
  | 25 => 2
  | 26 => 0
  | 27 => 0
  | 28 => 1
  | 29 => 2
  | 30 => 2
  | 31 => 2
  | 32 => 2
  | 33 => 0
  | 34 => 0
  | 35 => 0
  | 36 => 1
  | 37 => 1
  | 38 => 1
  | 39 => 2
  | 40 => 2
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
  | 51 => 0
  | 52 => 2
  | 53 => 0
  | 54 => 1
  | 55 => 1
  | 56 => 1
  | 57 => 1
  | 58 => 2
  | 59 => 0
  | 60 => 0
  | 61 => 0
  | 62 => 0
  | 63 => 1
  | _ => 0

def row37Code : ℕ := 85264369958735234239493645500223422744

theorem raw_row_37_binding : ∀ j : Fin 64,
    rawDigit CFSG.Models.MatrixGroups.Suz.rows1 37 j.val = row37Digit j.val := by
  decide +kernel

theorem packed_row_37_binding : ∀ j : Fin 64,
    packedDigit 2 row37Code j.val = row37Digit j.val := by
  decide +kernel

theorem scalar_37_check : packedDot 2 row37Code columnCode 64 % 3 = 0 % 3 := by
  decide +kernel

theorem actual_row_37_dot :
    (a *ᵥ (fun j => a j 0)) (37 : Fin 64) = 0 := by
  apply selected_packed_row_dot_mod 3 64 2 CFSG.Models.MatrixGroups.Suz.rows1
    (37 : Fin 64) (0 : Fin 64) row37Code columnCode 0
  · intro j
    exact (raw_row_37_binding j).trans (packed_row_37_binding j).symm
  · intro j
    exact (raw_column_binding j).trans (packed_column_binding j).symm
  · exact scalar_37_check

def row38Digit (j : ℕ) : ℕ :=
  match j with
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 2
  | 4 => 1
  | 5 => 2
  | 6 => 1
  | 7 => 0
  | 8 => 0
  | 9 => 0
  | 10 => 1
  | 11 => 2
  | 12 => 0
  | 13 => 1
  | 14 => 2
  | 15 => 2
  | 16 => 0
  | 17 => 2
  | 18 => 2
  | 19 => 0
  | 20 => 2
  | 21 => 1
  | 22 => 1
  | 23 => 2
  | 24 => 1
  | 25 => 1
  | 26 => 0
  | 27 => 1
  | 28 => 0
  | 29 => 0
  | 30 => 2
  | 31 => 1
  | 32 => 1
  | 33 => 0
  | 34 => 2
  | 35 => 1
  | 36 => 1
  | 37 => 1
  | 38 => 2
  | 39 => 1
  | 40 => 2
  | 41 => 1
  | 42 => 0
  | 43 => 1
  | 44 => 2
  | 45 => 2
  | 46 => 0
  | 47 => 2
  | 48 => 1
  | 49 => 2
  | 50 => 1
  | 51 => 1
  | 52 => 0
  | 53 => 2
  | 54 => 1
  | 55 => 0
  | 56 => 2
  | 57 => 2
  | 58 => 1
  | 59 => 0
  | 60 => 2
  | 61 => 2
  | 62 => 1
  | 63 => 0
  | _ => 0

def row38Code : ℕ := 34695421480660704541461701443871316368

theorem raw_row_38_binding : ∀ j : Fin 64,
    rawDigit CFSG.Models.MatrixGroups.Suz.rows1 38 j.val = row38Digit j.val := by
  decide +kernel

theorem packed_row_38_binding : ∀ j : Fin 64,
    packedDigit 2 row38Code j.val = row38Digit j.val := by
  decide +kernel

theorem scalar_38_check : packedDot 2 row38Code columnCode 64 % 3 = 0 % 3 := by
  decide +kernel

theorem actual_row_38_dot :
    (a *ᵥ (fun j => a j 0)) (38 : Fin 64) = 0 := by
  apply selected_packed_row_dot_mod 3 64 2 CFSG.Models.MatrixGroups.Suz.rows1
    (38 : Fin 64) (0 : Fin 64) row38Code columnCode 0
  · intro j
    exact (raw_row_38_binding j).trans (packed_row_38_binding j).symm
  · intro j
    exact (raw_column_binding j).trans (packed_column_binding j).symm
  · exact scalar_38_check

def row39Digit (j : ℕ) : ℕ :=
  match j with
  | 0 => 2
  | 1 => 1
  | 2 => 1
  | 3 => 0
  | 4 => 0
  | 5 => 0
  | 6 => 1
  | 7 => 1
  | 8 => 0
  | 9 => 0
  | 10 => 1
  | 11 => 1
  | 12 => 0
  | 13 => 0
  | 14 => 2
  | 15 => 2
  | 16 => 1
  | 17 => 1
  | 18 => 1
  | 19 => 1
  | 20 => 1
  | 21 => 0
  | 22 => 1
  | 23 => 0
  | 24 => 2
  | 25 => 0
  | 26 => 0
  | 27 => 1
  | 28 => 2
  | 29 => 0
  | 30 => 0
  | 31 => 2
  | 32 => 2
  | 33 => 0
  | 34 => 2
  | 35 => 1
  | 36 => 0
  | 37 => 2
  | 38 => 0
  | 39 => 0
  | 40 => 1
  | 41 => 2
  | 42 => 0
  | 43 => 1
  | 44 => 2
  | 45 => 2
  | 46 => 1
  | 47 => 1
  | 48 => 1
  | 49 => 1
  | 50 => 2
  | 51 => 1
  | 52 => 2
  | 53 => 1
  | 54 => 0
  | 55 => 1
  | 56 => 1
  | 57 => 0
  | 58 => 2
  | 59 => 0
  | 60 => 1
  | 61 => 1
  | 62 => 0
  | 63 => 0
  | _ => 0

def row39Code : ℕ := 6818913573914840298740104864329650198

theorem raw_row_39_binding : ∀ j : Fin 64,
    rawDigit CFSG.Models.MatrixGroups.Suz.rows1 39 j.val = row39Digit j.val := by
  decide +kernel

theorem packed_row_39_binding : ∀ j : Fin 64,
    packedDigit 2 row39Code j.val = row39Digit j.val := by
  decide +kernel

theorem scalar_39_check : packedDot 2 row39Code columnCode 64 % 3 = 0 % 3 := by
  decide +kernel

theorem actual_row_39_dot :
    (a *ᵥ (fun j => a j 0)) (39 : Fin 64) = 0 := by
  apply selected_packed_row_dot_mod 3 64 2 CFSG.Models.MatrixGroups.Suz.rows1
    (39 : Fin 64) (0 : Fin 64) row39Code columnCode 0
  · intro j
    exact (raw_row_39_binding j).trans (packed_row_39_binding j).symm
  · intro j
    exact (raw_column_binding j).trans (packed_column_binding j).symm
  · exact scalar_39_check

end SymmetricSubgroupAsymptotics.CFSGSuzPackedRows32To39
