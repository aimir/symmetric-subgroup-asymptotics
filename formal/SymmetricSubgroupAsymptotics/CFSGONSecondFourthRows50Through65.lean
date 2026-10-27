import SymmetricSubgroupAsymptotics.CFSGONSelectedSecondFourthRowPilot

/-! ONE selected bounded block of original ON B^4 rows,
50..65. All numerical commands are separate
per row. Checked source columns are reused. No full matrix identity. -/
set_option autoImplicit false
set_option Elab.async false
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows50Through65
open MatrixNaturalRowDotReflection MatrixNaturalRowPowerReflection
open CFSG.Models.MatrixGroups.ON
open CFSGONSelectedSecondFourthRowPilot (columnCode source_column_binding)

namespace Row50

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 1267650600228229401496703205376
  | 1 => 89202980794122492566142873090593446023921664
  | 2 => 26328072917139296674479506920917608079723773850137277813577744384
  | 3 => 130370302485407109521180524058200202307293977194619920040712988758680403184853549195737432064
  | 4 => 1267650600228229401496703205376
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 50 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 50 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 50 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 50 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 50 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 50 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row50

namespace Row51

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 5070602400912917605986812821504
  | 1 => 1427247692705959881058285969449495136382746624
  | 2 => 70368744177664
  | 3 => 295147905179352825856
  | 4 => 5070602400912917605986812821504
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 51 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 51 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 51 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 51 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 51 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 51 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row51

namespace Row52

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 20282409603651670423947251286016
  | 1 => 22835963083295358096932575511191922182123945984
  | 2 => 26959946667150639794667015087019630673637144422540572481103610249216
  | 3 => 1180591620717411303424
  | 4 => 20282409603651670423947251286016
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 52 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 52 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 52 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 52 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 52 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 52 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row52

namespace Row53

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 81129638414606681695789005144064
  | 1 => 91343852333181432387730302044767688728495783936
  | 2 => 431359146674410236714672241392314090778194310760649159697657763987456
  | 3 => 302034615187171979307516848529413206773907681608956289624774289218964008946371567499371119713
  | 4 => 81129638414606681695789005144064
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 53 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 53 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 53 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 53 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 53 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 53 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row53

namespace Row54

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 324518553658426726783156020576256
  | 1 => 1461501637330902918203684832716283019655932542976
  | 2 => 1125899906842624
  | 3 => 4722366482869645213696
  | 4 => 324518553658426726783156020576256
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 54 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 54 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 54 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 54 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 54 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 54 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row54

namespace Row55

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 1298074214633706907132624082305024
  | 1 => 23384026197294446691258957323460528314494920687616
  | 2 => 441711766194596082395824375185729628956870974218904739530401550323154944
  | 3 => 18889465931478580854784
  | 4 => 1298074214633706907132624082305024
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 55 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 55 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 55 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 55 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 55 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 55 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row55

namespace Row56

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 5192296858534827628530496329220096
  | 1 => 93536104789177786765035829293842113257979682750464
  | 2 => 7067388259113537318333190002971674063309935587502475832486424805170479104
  | 3 => 85588121660331236070071918478622714271494057774694440292915090264113803040943528091576451414
  | 4 => 5192296858534827628530496329220096
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 56 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 56 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 56 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 56 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 56 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 56 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row56

namespace Row57

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 20769187434139310514121985316880384
  | 1 => 1496577676626844588240573268701473812127674924007424
  | 2 => 21778071482940062266118884682947752886561
  | 3 => 302231454903657293676544
  | 4 => 20769187434139310514121985316880384
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 57 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 57 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 57 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 57 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 57 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 57 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row57

namespace Row58

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 83076749736557242056487941267521536
  | 1 => 5986310706507378352962293074805895248510699696029696
  | 2 => 1809251394333065553493296640760748560207343510400633813116524750123642650624
  | 3 => 175873688537930819832410824069424234419760838823246374820484813584354935674625679620173736086
  | 4 => 83076749736557242056487941267521536
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 58 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 58 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 58 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 58 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 58 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 58 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row58

namespace Row59

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 332306998946228968225951765070086144
  | 1 => 68719476736
  | 2 => 18014398509481984
  | 3 => 1208925819614629174706176
  | 4 => 332306998946228968225951765070086144
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 59 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 59 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 59 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 59 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 59 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 59 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row59

namespace Row60

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 1329227995784915872903807060280344576
  | 1 => 95780971304118053647396689196894323976171195136475136
  | 2 => 115792089237316195423570985008687907853269984665640564039457584007913129639936
  | 3 => 165318832824572755970516216376178964252878650717413631691079791170992942912224367858620736024
  | 4 => 1329227995784915872903807060280344576
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 60 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 60 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 60 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 60 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 60 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 60 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row60

namespace Row61

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 5316911983139663491615228241121378304
  | 1 => 1532495540865888858358347027150309183618739122183602176
  | 2 => 72057594037927936
  | 3 => 4835703278458516698824704
  | 4 => 5316911983139663491615228241121378304
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 61 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 61 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 61 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 61 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 61 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 61 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row61

namespace Row62

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 21267647932558653966460912964485513216
  | 1 => 24519928653854221733733552434404946937899825954937634816
  | 2 => 118571099379011784113736688648896417641748464297615937576404566024103044751294464
  | 3 => 19342813113834066795298816
  | 4 => 21267647932558653966460912964485513216
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 62 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 62 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 62 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 62 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 62 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 62 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row62

namespace Row63

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 85070591730234615865843651857942052864
  | 1 => 98079714615416886934934209737619787751599303819750539264
  | 2 => 1897137590064188545819787018382342682267975428761855001222473056385648716020711424
  | 3 => 37816712447323994196165055163884006033926359288295245638517253301357802893481991815510919770
  | 4 => 85070591730234615865843651857942052864
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 63 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 63 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 63 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 63 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 63 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 63 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row63

namespace Row64

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 340282366920938463463374607431768211456
  | 1 => 1569275433846670190958947355801916604025588861116008628224
  | 2 => 121416805764108066932466369176469931665150427440758720078238275608681517825325531136
  | 3 => 309485009821345068724781056
  | 4 => 340282366920938463463374607431768211456
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 64 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 64 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 64 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 64 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 64 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 64 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row64

namespace Row65

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 1361129467683753853853498429727072845824
  | 1 => 6277101735386680763835789423207666416102355444464034512896
  | 2 => 1942668892225729070919461906823518906642406839052139521251812409738904285205208498176
  | 3 => 78681169935539002302568107317423734959450588172137539501951643508459419777547614939504870922
  | 4 => 1361129467683753853853498429727072845824
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 65 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 65 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 65 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 65 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 65 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 65 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row65

theorem block_identity (i : Fin 16) (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) ⟨i.val + 50, by omega⟩ z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) ⟨i.val + 50, by omega⟩ z := by
  fin_cases i
  · exact Row50.row_identity z
  · exact Row51.row_identity z
  · exact Row52.row_identity z
  · exact Row53.row_identity z
  · exact Row54.row_identity z
  · exact Row55.row_identity z
  · exact Row56.row_identity z
  · exact Row57.row_identity z
  · exact Row58.row_identity z
  · exact Row59.row_identity z
  · exact Row60.row_identity z
  · exact Row61.row_identity z
  · exact Row62.row_identity z
  · exact Row63.row_identity z
  · exact Row64.row_identity z
  · exact Row65.row_identity z

end SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows50Through65
