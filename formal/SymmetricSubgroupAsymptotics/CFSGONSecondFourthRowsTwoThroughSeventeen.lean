import SymmetricSubgroupAsymptotics.CFSGONSelectedSecondFourthRowPilot

/-! SELECTED16 rows2..17 of the SAME original ON B^4, over F3.
Each row's packed_steps, initial row and final row are separate commands.
The already checked source columns are reused. No full matrix identity. -/
set_option autoImplicit false
set_option Elab.async false
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGONSecondFourthRowsTwoThroughSeventeen
open MatrixNaturalRowDotReflection MatrixNaturalRowPowerReflection
open CFSG.Models.MatrixGroups.ON
open CFSGONSelectedSecondFourthRowPilot (columnCode source_column_binding)

namespace Row2

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 16
  | 1 => 256
  | 2 => 289
  | 3 => 1
  | 4 => 16
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 2 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 2 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 2 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 2 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 2 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 2 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row2

namespace Row3

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 64
  | 1 => 1024
  | 2 => 65536
  | 3 => 16777216
  | 4 => 64
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 3 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 3 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 3 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 3 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 3 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 3 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row3

namespace Row4

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 256
  | 1 => 289
  | 2 => 1
  | 3 => 16
  | 4 => 256
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 4 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 4 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 4 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 4 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 4 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 4 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row4

namespace Row5

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 1024
  | 1 => 65536
  | 2 => 16777216
  | 3 => 64
  | 4 => 1024
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 5 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 5 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 5 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 5 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 5 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 5 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row5

namespace Row6

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 4096
  | 1 => 262144
  | 2 => 268435456
  | 3 => 4398046511104
  | 4 => 4096
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 6 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 6 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 6 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 6 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 6 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 6 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row6

namespace Row7

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 16384
  | 1 => 1048576
  | 2 => 4294967296
  | 3 => 281474976710656
  | 4 => 16384
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 7 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 7 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 7 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 7 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 7 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 7 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row7

namespace Row8

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 65536
  | 1 => 16777216
  | 2 => 64
  | 3 => 1024
  | 4 => 65536
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 8 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 8 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 8 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 8 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 8 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 8 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row8

namespace Row9

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 262144
  | 1 => 268435456
  | 2 => 4398046511104
  | 3 => 4096
  | 4 => 262144
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 9 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 9 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 9 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 9 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 9 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 9 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row9

namespace Row10

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 1048576
  | 1 => 4294967296
  | 2 => 281474976710656
  | 3 => 16384
  | 4 => 1048576
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 10 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 10 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 10 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 10 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 10 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 10 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row10

namespace Row11

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 4194304
  | 1 => 17179869184
  | 2 => 4503599627370496
  | 3 => 75557863725914323419136
  | 4 => 4194304
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 11 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 11 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 11 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 11 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 11 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 11 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row11

namespace Row12

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 16777216
  | 1 => 64
  | 2 => 1024
  | 3 => 65536
  | 4 => 16777216
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 12 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 12 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 12 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 12 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 12 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 12 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row12

namespace Row13

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 67108864
  | 1 => 274877906944
  | 2 => 288230376151711744
  | 3 => 77371252455336267181195264
  | 4 => 67108864
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 13 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 13 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 13 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 13 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 13 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 13 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row13

namespace Row14

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 268435456
  | 1 => 4398046511104
  | 2 => 4096
  | 3 => 262144
  | 4 => 268435456
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 14 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 14 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 14 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 14 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 14 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 14 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row14

namespace Row15

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 1073741824
  | 1 => 17592186044416
  | 2 => 73786976294838206464
  | 3 => 316912650057057350374175801344
  | 4 => 1073741824
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 15 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 15 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 15 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 15 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 15 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 15 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row15

namespace Row16

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 4294967296
  | 1 => 281474976710656
  | 2 => 16384
  | 3 => 1048576
  | 4 => 4294967296
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 16 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 16 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 16 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 16 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 16 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 16 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row16

namespace Row17

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 17179869184
  | 1 => 4503599627370496
  | 2 => 75557863725914323419136
  | 3 => 4194304
  | 4 => 17179869184
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 17 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 17 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 17 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 17 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 17 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 17 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row17

theorem block_identity (i : Fin 16) (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) ⟨i.val + 2, by omega⟩ z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) ⟨i.val + 2, by omega⟩ z := by
  fin_cases i
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
  · exact Row17.row_identity z

end SymmetricSubgroupAsymptotics.CFSGONSecondFourthRowsTwoThroughSeventeen
