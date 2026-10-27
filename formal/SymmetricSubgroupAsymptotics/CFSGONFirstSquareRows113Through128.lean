import SymmetricSubgroupAsymptotics.CFSGONFirstSquareRowZeroPilot

/-! ONE selected bounded block of original ON A^2 rows,
113..128. All numerical commands are separate
per row. Checked source columns are reused. No full matrix identity. -/
set_option autoImplicit false
set_option Elab.async false
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows113Through128
open MatrixNaturalRowDotReflection MatrixNaturalRowPowerReflection
open CFSG.Models.MatrixGroups.ON
open CFSGONFirstSquareRowZeroPilot (columnCode source_column_binding)

namespace Row113

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 107839786668602559178668060348078522694548577690162289924414440996864
  | 1 => 91343852333181432387730302044767688728495783936
  | 2 => 107839786668602559178668060348078522694548577690162289924414440996864
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 113 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 113 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 113 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 113 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 113 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 113 z :=
  (square_power_row z).trans (selected_row_return z)

end Row113

namespace Row114

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 431359146674410236714672241392314090778194310760649159697657763987456
  | 1 => 263943557511026537616197689913038072219255130897774076500671973048566487416948087320369975424
  | 2 => 431359146674410236714672241392314090778194310760649159697657763987456
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 114 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 114 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 114 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 114 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 114 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 114 z :=
  (square_power_row z).trans (selected_row_return z)

end Row114

namespace Row115

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 1725436586697640946858688965569256363112777243042596638790631055949824
  | 1 => 85694948041970402038226260628812880640209577831472826704686080507480342905729921398671512090
  | 2 => 1725436586697640946858688965569256363112777243042596638790631055949824
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 115 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 115 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 115 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 115 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 115 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 115 z :=
  (square_power_row z).trans (selected_row_return z)

end Row115

namespace Row116

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 6901746346790563787434755862277025452451108972170386555162524223799296
  | 1 => 1461501637330902918203684832716283019655932542976
  | 2 => 6901746346790563787434755862277025452451108972170386555162524223799296
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 116 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 116 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 116 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 116 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 116 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 116 z :=
  (square_power_row z).trans (selected_row_return z)

end Row116

namespace Row117

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 27606985387162255149739023449108101809804435888681546220650096895197184
  | 1 => 298728891121604409143752941148584583923538896806706982097149072294972994714254574667354776164
  | 2 => 27606985387162255149739023449108101809804435888681546220650096895197184
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 117 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 117 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 117 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 117 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 117 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 117 z :=
  (square_power_row z).trans (selected_row_return z)

end Row117

namespace Row118

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 110427941548649020598956093796432407239217743554726184882600387580788736
  | 1 => 23384026197294446691258957323460528314494920687616
  | 2 => 110427941548649020598956093796432407239217743554726184882600387580788736
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 118 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 118 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 118 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 118 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 118 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 118 z :=
  (square_power_row z).trans (selected_row_return z)

end Row118

namespace Row119

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 441711766194596082395824375185729628956870974218904739530401550323154944
  | 1 => 139857522716094734461613207224676855298960718042832302821215273404782417829976681409679073289
  | 2 => 441711766194596082395824375185729628956870974218904739530401550323154944
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 119 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 119 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 119 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 119 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 119 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 119 z :=
  (square_power_row z).trans (selected_row_return z)

end Row119

namespace Row120

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 1766847064778384329583297500742918515827483896875618958121606201292619776
  | 1 => 93536104789177786765035829293842113257979682750464
  | 2 => 1766847064778384329583297500742918515827483896875618958121606201292619776
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 120 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 120 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 120 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 120 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 120 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 120 z :=
  (square_power_row z).trans (selected_row_return z)

end Row120

namespace Row121

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 7067388259113537318333190002971674063309935587502475832486424805170479104
  | 1 => 326055682045750908120747805311586587876824000094561925809124362047412787280866980908033385889
  | 2 => 7067388259113537318333190002971674063309935587502475832486424805170479104
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 121 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 121 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 121 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 121 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 121 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 121 z :=
  (square_power_row z).trans (selected_row_return z)

end Row121

namespace Row122

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 28269553036454149273332760011886696253239742350009903329945699220681916416
  | 1 => 49589110345661712049968562601923756112125794242850197769462595588121812100257196679155321153
  | 2 => 28269553036454149273332760011886696253239742350009903329945699220681916416
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 122 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 122 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 122 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 122 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 122 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 122 z :=
  (square_power_row z).trans (selected_row_return z)

end Row122

namespace Row123

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 113078212145816597093331040047546785012958969400039613319782796882727665664
  | 1 => 1496577676626844588240573268701473812127674924007424
  | 2 => 113078212145816597093331040047546785012958969400039613319782796882727665664
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 123 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 123 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 123 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 123 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 123 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 123 z :=
  (square_power_row z).trans (selected_row_return z)

end Row123

namespace Row124

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 452312848583266388373324160190187140051835877600158453279131187530910662656
  | 1 => 5986310706507378352962293074805895248510699696029696
  | 2 => 452312848583266388373324160190187140051835877600158453279131187530910662656
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 124 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 124 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 124 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 124 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 124 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 124 z :=
  (square_power_row z).trans (selected_row_return z)

end Row124

namespace Row125

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 1809251394333065553493296640760748560207343510400633813116524750123642650624
  | 1 => 135547456844863175424526171510356762384083595380253692808089356132022821152985324956191900762
  | 2 => 1809251394333065553493296640760748560207343510400633813116524750123642650624
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 125 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 125 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 125 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 125 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 125 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 125 z :=
  (square_power_row z).trans (selected_row_return z)

end Row125

namespace Row126

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 7237005577332262213973186563042994240829374041602535252466099000494570602496
  | 1 => 214610021044438069951196422233366486191487790950505200056888370751612666734718879630850918946
  | 2 => 7237005577332262213973186563042994240829374041602535252466099000494570602496
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 126 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 126 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 126 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 126 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 126 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 126 z :=
  (square_power_row z).trans (selected_row_return z)

end Row126

namespace Row127

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 28948022309329048855892746252171976963317496166410141009864396001978282409984
  | 1 => 95780971304118053647396689196894323976171195136475136
  | 2 => 28948022309329048855892746252171976963317496166410141009864396001978282409984
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 127 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 127 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 127 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 127 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 127 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 127 z :=
  (square_power_row z).trans (selected_row_return z)

end Row127

namespace Row128

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 115792089237316195423570985008687907853269984665640564039457584007913129639936
  | 1 => 310345664403214371348834174147662799834713886029867662876241653882079156514807200118960558692
  | 2 => 115792089237316195423570985008687907853269984665640564039457584007913129639936
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 128 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 128 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 128 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 128 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 128 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 128 z :=
  (square_power_row z).trans (selected_row_return z)

end Row128

theorem block_identity (i : Fin 16) (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) ⟨i.val + 113, by omega⟩ z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) ⟨i.val + 113, by omega⟩ z := by
  fin_cases i
  · exact Row113.row_identity z
  · exact Row114.row_identity z
  · exact Row115.row_identity z
  · exact Row116.row_identity z
  · exact Row117.row_identity z
  · exact Row118.row_identity z
  · exact Row119.row_identity z
  · exact Row120.row_identity z
  · exact Row121.row_identity z
  · exact Row122.row_identity z
  · exact Row123.row_identity z
  · exact Row124.row_identity z
  · exact Row125.row_identity z
  · exact Row126.row_identity z
  · exact Row127.row_identity z
  · exact Row128.row_identity z

end SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows113Through128
