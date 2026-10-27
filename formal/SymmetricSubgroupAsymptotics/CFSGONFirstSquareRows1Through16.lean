import SymmetricSubgroupAsymptotics.CFSGONFirstSquareRowZeroPilot

/-! ONE selected bounded block of original ON A^2 rows,
1..16. All numerical commands are separate
per row. Checked source columns are reused. No full matrix identity. -/
set_option autoImplicit false
set_option Elab.async false
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows1Through16
open MatrixNaturalRowDotReflection MatrixNaturalRowPowerReflection
open CFSG.Models.MatrixGroups.ON
open CFSGONFirstSquareRowZeroPilot (columnCode source_column_binding)

namespace Row1

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 4
  | 1 => 1
  | 2 => 4
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 1 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 1 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 1 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 1 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 1 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 1 z :=
  (square_power_row z).trans (selected_row_return z)

end Row1

namespace Row2

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 16
  | 1 => 64
  | 2 => 16
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 2 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 2 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 2 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 2 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 2 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 2 z :=
  (square_power_row z).trans (selected_row_return z)

end Row2

namespace Row3

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 64
  | 1 => 16
  | 2 => 64
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 3 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 3 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 3 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 3 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 3 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 3 z :=
  (square_power_row z).trans (selected_row_return z)

end Row3

namespace Row4

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 256
  | 1 => 4096
  | 2 => 256
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 4 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 4 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 4 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 4 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 4 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 4 z :=
  (square_power_row z).trans (selected_row_return z)

end Row4

namespace Row5

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 1024
  | 1 => 16384
  | 2 => 1024
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 5 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 5 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 5 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 5 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 5 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 5 z :=
  (square_power_row z).trans (selected_row_return z)

end Row5

namespace Row6

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 4096
  | 1 => 256
  | 2 => 4096
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 6 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 6 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 6 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 6 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 6 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 6 z :=
  (square_power_row z).trans (selected_row_return z)

end Row6

namespace Row7

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 16384
  | 1 => 1024
  | 2 => 16384
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 7 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 7 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 7 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 7 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 7 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 7 z :=
  (square_power_row z).trans (selected_row_return z)

end Row7

namespace Row8

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 65536
  | 1 => 4194304
  | 2 => 65536
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 8 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 8 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 8 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 8 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 8 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 8 z :=
  (square_power_row z).trans (selected_row_return z)

end Row8

namespace Row9

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 262144
  | 1 => 67108864
  | 2 => 262144
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 9 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 9 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 9 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 9 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 9 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 9 z :=
  (square_power_row z).trans (selected_row_return z)

end Row9

namespace Row10

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 1048576
  | 1 => 1073741824
  | 2 => 1048576
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 10 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 10 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 10 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 10 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 10 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 10 z :=
  (square_power_row z).trans (selected_row_return z)

end Row10

namespace Row11

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 4194304
  | 1 => 65536
  | 2 => 4194304
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 11 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 11 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 11 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 11 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 11 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 11 z :=
  (square_power_row z).trans (selected_row_return z)

end Row11

namespace Row12

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 16777216
  | 1 => 68719476736
  | 2 => 16777216
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 12 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 12 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 12 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 12 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 12 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 12 z :=
  (square_power_row z).trans (selected_row_return z)

end Row12

namespace Row13

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 67108864
  | 1 => 262144
  | 2 => 67108864
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 13 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 13 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 13 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 13 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 13 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 13 z :=
  (square_power_row z).trans (selected_row_return z)

end Row13

namespace Row14

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 268435456
  | 1 => 1099511627776
  | 2 => 268435456
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 14 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 14 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 14 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 14 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 14 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 14 z :=
  (square_power_row z).trans (selected_row_return z)

end Row14

namespace Row15

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 1073741824
  | 1 => 1048576
  | 2 => 1073741824
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 15 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 15 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 15 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 15 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 15 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 15 z :=
  (square_power_row z).trans (selected_row_return z)

end Row15

namespace Row16

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 4294967296
  | 1 => 70368744177664
  | 2 => 4294967296
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 16 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 16 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 16 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 16 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 16 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 16 z :=
  (square_power_row z).trans (selected_row_return z)

end Row16

theorem block_identity (i : Fin 16) (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) ⟨i.val + 1, by omega⟩ z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) ⟨i.val + 1, by omega⟩ z := by
  fin_cases i
  · exact Row1.row_identity z
  · exact Row2.row_identity z
  · exact Row3.row_identity z
  · exact Row4.row_identity z
  · exact Row5.row_identity z
  · exact Row6.row_identity z
  · exact Row7.row_identity z
  · exact Row8.row_identity z
  · exact Row9.row_identity z
  · exact Row10.row_identity z
  · exact Row11.row_identity z
  · exact Row12.row_identity z
  · exact Row13.row_identity z
  · exact Row14.row_identity z
  · exact Row15.row_identity z
  · exact Row16.row_identity z

end SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows1Through16
