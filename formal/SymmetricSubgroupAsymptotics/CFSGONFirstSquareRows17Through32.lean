import SymmetricSubgroupAsymptotics.CFSGONFirstSquareRowZeroPilot

/-! ONE selected bounded block of original ON A^2 rows,
17..32. All numerical commands are separate
per row. Checked source columns are reused. No full matrix identity. -/
set_option autoImplicit false
set_option Elab.async false
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows17Through32
open MatrixNaturalRowDotReflection MatrixNaturalRowPowerReflection
open CFSG.Models.MatrixGroups.ON
open CFSGONFirstSquareRowZeroPilot (columnCode source_column_binding)

namespace Row17

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 17179869184
  | 1 => 1125899906842624
  | 2 => 17179869184
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 17 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 17 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 17 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 17 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 17 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 17 z :=
  (square_power_row z).trans (selected_row_return z)

end Row17

namespace Row18

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 68719476736
  | 1 => 16777216
  | 2 => 68719476736
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 18 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 18 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 18 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 18 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 18 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 18 z :=
  (square_power_row z).trans (selected_row_return z)

end Row18

namespace Row19

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 274877906944
  | 1 => 72057594037927936
  | 2 => 274877906944
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 19 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 19 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 19 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 19 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 19 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 19 z :=
  (square_power_row z).trans (selected_row_return z)

end Row19

namespace Row20

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 1099511627776
  | 1 => 268435456
  | 2 => 1099511627776
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 20 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 20 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 20 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 20 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 20 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 20 z :=
  (square_power_row z).trans (selected_row_return z)

end Row20

namespace Row21

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 4398046511104
  | 1 => 4611686018427387904
  | 2 => 4398046511104
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 21 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 21 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 21 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 21 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 21 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 21 z :=
  (square_power_row z).trans (selected_row_return z)

end Row21

namespace Row22

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 17592186044416
  | 1 => 18446744073709551616
  | 2 => 17592186044416
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 22 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 22 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 22 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 22 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 22 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 22 z :=
  (square_power_row z).trans (selected_row_return z)

end Row22

namespace Row23

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 70368744177664
  | 1 => 4294967296
  | 2 => 70368744177664
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 23 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 23 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 23 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 23 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 23 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 23 z :=
  (square_power_row z).trans (selected_row_return z)

end Row23

namespace Row24

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 281474976710656
  | 1 => 1180591620717411303424
  | 2 => 281474976710656
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 24 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 24 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 24 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 24 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 24 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 24 z :=
  (square_power_row z).trans (selected_row_return z)

end Row24

namespace Row25

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 1125899906842624
  | 1 => 17179869184
  | 2 => 1125899906842624
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 25 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 25 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 25 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 25 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 25 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 25 z :=
  (square_power_row z).trans (selected_row_return z)

end Row25

namespace Row26

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 4503599627370496
  | 1 => 18889465931478580854784
  | 2 => 4503599627370496
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 26 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 26 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 26 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 26 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 26 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 26 z :=
  (square_power_row z).trans (selected_row_return z)

end Row26

namespace Row27

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 18014398509481984
  | 1 => 302231454903657293676544
  | 2 => 18014398509481984
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 27 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 27 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 27 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 27 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 27 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 27 z :=
  (square_power_row z).trans (selected_row_return z)

end Row27

namespace Row28

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 72057594037927936
  | 1 => 274877906944
  | 2 => 72057594037927936
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 28 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 28 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 28 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 28 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 28 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 28 z :=
  (square_power_row z).trans (selected_row_return z)

end Row28

namespace Row29

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 288230376151711744
  | 1 => 19342813113834066795298816
  | 2 => 288230376151711744
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 29 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 29 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 29 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 29 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 29 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 29 z :=
  (square_power_row z).trans (selected_row_return z)

end Row29

namespace Row30

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 1152921504606846976
  | 1 => 309485009821345068724781056
  | 2 => 1152921504606846976
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 30 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 30 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 30 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 30 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 30 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 30 z :=
  (square_power_row z).trans (selected_row_return z)

end Row30

namespace Row31

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 4611686018427387904
  | 1 => 4398046511104
  | 2 => 4611686018427387904
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 31 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 31 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 31 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 31 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 31 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 31 z :=
  (square_power_row z).trans (selected_row_return z)

end Row31

namespace Row32

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 18446744073709551616
  | 1 => 17592186044416
  | 2 => 18446744073709551616
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 32 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 32 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 32 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 32 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 32 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 32 z :=
  (square_power_row z).trans (selected_row_return z)

end Row32

theorem block_identity (i : Fin 16) (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) ⟨i.val + 17, by omega⟩ z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) ⟨i.val + 17, by omega⟩ z := by
  fin_cases i
  · exact Row17.row_identity z
  · exact Row18.row_identity z
  · exact Row19.row_identity z
  · exact Row20.row_identity z
  · exact Row21.row_identity z
  · exact Row22.row_identity z
  · exact Row23.row_identity z
  · exact Row24.row_identity z
  · exact Row25.row_identity z
  · exact Row26.row_identity z
  · exact Row27.row_identity z
  · exact Row28.row_identity z
  · exact Row29.row_identity z
  · exact Row30.row_identity z
  · exact Row31.row_identity z
  · exact Row32.row_identity z

end SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows17Through32
