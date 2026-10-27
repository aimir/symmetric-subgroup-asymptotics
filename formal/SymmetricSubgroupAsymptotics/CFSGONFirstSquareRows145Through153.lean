import SymmetricSubgroupAsymptotics.CFSGONFirstSquareRowZeroPilot

/-! ONE selected bounded block of original ON A^2 rows,
145..153. All numerical commands are separate
per row. Checked source columns are reused. No full matrix identity. -/
set_option autoImplicit false
set_option Elab.async false
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows145Through153
open MatrixNaturalRowDotReflection MatrixNaturalRowPowerReflection
open CFSG.Models.MatrixGroups.ON
open CFSGONFirstSquareRowZeroPilot (columnCode source_column_binding)

namespace Row145

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 1989292945639146568621528992587283360401824603189390869761855907572637988050133502132224
  | 1 => 25711008708143844408671393477458601640355247900524685364822016
  | 2 => 1989292945639146568621528992587283360401824603189390869761855907572637988050133502132224
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 145 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 145 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 145 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 145 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 145 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 145 z :=
  (square_power_row z).trans (selected_row_return z)

end Row145

namespace Row146

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 7957171782556586274486115970349133441607298412757563479047423630290551952200534008528896
  | 1 => 12541700393458550015685617381500894798380965852132455561343757308447851982137041800708893000
  | 2 => 7957171782556586274486115970349133441607298412757563479047423630290551952200534008528896
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 146 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 146 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 146 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 146 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 146 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 146 z :=
  (square_power_row z).trans (selected_row_return z)

end Row146

namespace Row147

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 31828687130226345097944463881396533766429193651030253916189694521162207808802136034115584
  | 1 => 411376139330301510538742295639337626245683966408394965837152256
  | 2 => 31828687130226345097944463881396533766429193651030253916189694521162207808802136034115584
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 147 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 147 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 147 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 147 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 147 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 147 z :=
  (square_power_row z).trans (selected_row_return z)

end Row147

namespace Row148

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 127314748520905380391777855525586135065716774604121015664758778084648831235208544136462336
  | 1 => 164287820363139962977967823616485628775421060888290776788751327359306276382878859331937870421
  | 2 => 127314748520905380391777855525586135065716774604121015664758778084648831235208544136462336
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 148 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 148 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 148 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 148 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 148 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 148 z :=
  (square_power_row z).trans (selected_row_return z)

end Row148

namespace Row149

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 509258994083621521567111422102344540262867098416484062659035112338595324940834176545849344
  | 1 => 1645504557321206042154969182557350504982735865633579863348609024
  | 2 => 509258994083621521567111422102344540262867098416484062659035112338595324940834176545849344
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 149 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 149 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 149 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 149 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 149 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 149 z :=
  (square_power_row z).trans (selected_row_return z)

end Row149

namespace Row150

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376
  | 1 => 139828056815207714096556306430469853946134886324668512480755045840293577960362235129630302826
  | 2 => 2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 150 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 150 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 150 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 150 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 150 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 150 z :=
  (square_power_row z).trans (selected_row_return z)

end Row150

namespace Row151

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 8148143905337944345073782753637512644205873574663745002544561797417525199053346824733589504
  | 1 => 179293637886606971130126386927233635498369072655429389230140311412831634132162512421644305514
  | 2 => 8148143905337944345073782753637512644205873574663745002544561797417525199053346824733589504
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 151 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 151 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 151 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 151 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 151 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 151 z :=
  (square_power_row z).trans (selected_row_return z)

end Row151

namespace Row152

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 32592575621351777380295131014550050576823494298654980010178247189670100796213387298934358016
  | 1 => 26328072917139296674479506920917608079723773850137277813577744384
  | 2 => 32592575621351777380295131014550050576823494298654980010178247189670100796213387298934358016
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 152 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 152 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 152 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 152 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 152 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 152 z :=
  (square_power_row z).trans (selected_row_return z)

end Row152

namespace Row153

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 130370302485407109521180524058200202307293977194619920040712988758680403184853549195737432064
  | 1 => 133086225968878045989396266709980500603779068224192908743032664191952970712974130765424126529
  | 2 => 130370302485407109521180524058200202307293977194619920040712988758680403184853549195737432064
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 2) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 153 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 2) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows1 j z := by
  exact (packed_row_step 3 154 2 rows1 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem square_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 153 z = rowVector 2 z :=
  matrix_pow_row_eq 3 154 rows1 153 2 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 2 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 153 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) 153 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 153 z :=
  (square_power_row z).trans (selected_row_return z)

end Row153

theorem block_identity (i : Fin 9) (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows1 ^ 2) ⟨i.val + 145, by omega⟩ z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) ⟨i.val + 145, by omega⟩ z := by
  fin_cases i
  · exact Row145.row_identity z
  · exact Row146.row_identity z
  · exact Row147.row_identity z
  · exact Row148.row_identity z
  · exact Row149.row_identity z
  · exact Row150.row_identity z
  · exact Row151.row_identity z
  · exact Row152.row_identity z
  · exact Row153.row_identity z

end SymmetricSubgroupAsymptotics.CFSGONFirstSquareRows145Through153
