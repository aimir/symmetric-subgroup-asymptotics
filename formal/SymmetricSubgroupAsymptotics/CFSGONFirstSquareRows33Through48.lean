import SymmetricSubgroupAsymptotics.CFSGONFirstSquareRowZeroPilot

/-! ONE selected bounded block of original ON A^2 rows,
33..48. All numerical commands are separate
per row. Checked source columns are reused. No full matrix identity. -/
set_option autoImplicit false
set_option Elab.async false
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows33Through48
open MatrixNaturalRowDotReflection MatrixNaturalRowPowerReflection
open CFSG.Models.MatrixGroups.ON
open CFSGONFirstSquareRowZeroPilot (columnCode source_column_binding)

namespace Row33

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 73786976294838206464
  | 1 => 79228162514264337593543950336
  | 2 => 73786976294838206464
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 33 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 33 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 33 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 33 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 33 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 33 z :=
  (square_power_row z).trans (selected_row_return z)

end Row33

namespace Row34

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 295147905179352825856
  | 1 => 1267650600228229401496703205376
  | 2 => 295147905179352825856
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 34 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 34 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 34 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 34 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 34 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 34 z :=
  (square_power_row z).trans (selected_row_return z)

end Row34

namespace Row35

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 1180591620717411303424
  | 1 => 281474976710656
  | 2 => 1180591620717411303424
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 35 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 35 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 35 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 35 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 35 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 35 z :=
  (square_power_row z).trans (selected_row_return z)

end Row35

namespace Row36

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 4722366482869645213696
  | 1 => 81129638414606681695789005144064
  | 2 => 4722366482869645213696
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 36 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 36 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 36 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 36 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 36 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 36 z :=
  (square_power_row z).trans (selected_row_return z)

end Row36

namespace Row37

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 18889465931478580854784
  | 1 => 4503599627370496
  | 2 => 18889465931478580854784
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 37 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 37 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 37 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 37 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 37 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 37 z :=
  (square_power_row z).trans (selected_row_return z)

end Row37

namespace Row38

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 75557863725914323419136
  | 1 => 5192296858534827628530496329220096
  | 2 => 75557863725914323419136
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 38 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 38 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 38 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 38 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 38 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 38 z :=
  (square_power_row z).trans (selected_row_return z)

end Row38

namespace Row39

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 302231454903657293676544
  | 1 => 18014398509481984
  | 2 => 302231454903657293676544
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 39 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 39 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 39 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 39 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 39 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 39 z :=
  (square_power_row z).trans (selected_row_return z)

end Row39

namespace Row40

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 1208925819614629174706176
  | 1 => 83076749736557242056487941267521536
  | 2 => 1208925819614629174706176
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 40 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 40 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 40 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 40 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 40 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 40 z :=
  (square_power_row z).trans (selected_row_return z)

end Row40

namespace Row41

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 4835703278458516698824704
  | 1 => 1329227995784915872903807060280344576
  | 2 => 4835703278458516698824704
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 41 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 41 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 41 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 41 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 41 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 41 z :=
  (square_power_row z).trans (selected_row_return z)

end Row41

namespace Row42

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 19342813113834066795298816
  | 1 => 288230376151711744
  | 2 => 19342813113834066795298816
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 42 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 42 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 42 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 42 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 42 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 42 z :=
  (square_power_row z).trans (selected_row_return z)

end Row42

namespace Row43

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 77371252455336267181195264
  | 1 => 85070591730234615865843651857942052864
  | 2 => 77371252455336267181195264
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 43 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 43 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 43 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 43 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 43 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 43 z :=
  (square_power_row z).trans (selected_row_return z)

end Row43

namespace Row44

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 309485009821345068724781056
  | 1 => 1152921504606846976
  | 2 => 309485009821345068724781056
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 44 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 44 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 44 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 44 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 44 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 44 z :=
  (square_power_row z).trans (selected_row_return z)

end Row44

namespace Row45

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 1237940039285380274899124224
  | 1 => 1361129467683753853853498429727072845824
  | 2 => 1237940039285380274899124224
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 45 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 45 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 45 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 45 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 45 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 45 z :=
  (square_power_row z).trans (selected_row_return z)

end Row45

namespace Row46

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 4951760157141521099596496896
  | 1 => 21778071482940061661655974875633165533184
  | 2 => 4951760157141521099596496896
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 46 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 46 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 46 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 46 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 46 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 46 z :=
  (square_power_row z).trans (selected_row_return z)

end Row46

namespace Row47

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 19807040628566084398385987584
  | 1 => 348449143727040986586495598010130648530944
  | 2 => 19807040628566084398385987584
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 47 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 47 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 47 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 47 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 47 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 47 z :=
  (square_power_row z).trans (selected_row_return z)

end Row47

namespace Row48

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 79228162514264337593543950336
  | 1 => 73786976294838206464
  | 2 => 79228162514264337593543950336
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 48 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 48 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 48 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 48 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 48 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 48 z :=
  (square_power_row z).trans (selected_row_return z)

end Row48

theorem block_identity (i : Fin 16) (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) ⟨i.val + 33, by omega⟩ z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) ⟨i.val + 33, by omega⟩ z := by
  fin_cases i
  · exact Row33.row_identity z
  · exact Row34.row_identity z
  · exact Row35.row_identity z
  · exact Row36.row_identity z
  · exact Row37.row_identity z
  · exact Row38.row_identity z
  · exact Row39.row_identity z
  · exact Row40.row_identity z
  · exact Row41.row_identity z
  · exact Row42.row_identity z
  · exact Row43.row_identity z
  · exact Row44.row_identity z
  · exact Row45.row_identity z
  · exact Row46.row_identity z
  · exact Row47.row_identity z
  · exact Row48.row_identity z

end SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows33Through48
