import SymmetricSubgroupAsymptotics.CFSGONSelectedSecondFourthRowPilot

/-! ONE selected bounded block of original ON B^4 rows,
146..153. All numerical commands are separate
per row. Checked source columns are reused. No full matrix identity. -/
set_option autoImplicit false
set_option Elab.async false
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows146Through153
open MatrixNaturalRowDotReflection MatrixNaturalRowPowerReflection
open CFSG.Models.MatrixGroups.ON
open CFSGONSelectedSecondFourthRowPilot (columnCode source_column_binding)

namespace Row146

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 7957171782556586274486115970349133441607298412757563479047423630290551952200534008528896
  | 1 => 179837229161890588290118324295903857615147369524460203800677455228109267421063331567500953625
  | 2 => 302520546117586184721644148237502985468061298593512955132495560108416420252310685172260688969
  | 3 => 102844034832575377634685573909834406561420991602098741459288064
  | 4 => 7957171782556586274486115970349133441607298412757563479047423630290551952200534008528896
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 146 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 146 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 146 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 146 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 146 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 146 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row146

namespace Row147

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 31828687130226345097944463881396533766429193651030253916189694521162207808802136034115584
  | 1 => 313998648322300212433761758131559520783270840107057178789777126794067241790404288119925385610
  | 2 => 83654803884539031840841135857286820464276746635267624425438619969747103414891344558786412933
  | 3 => 211855017412658177599318095706733885140103744968067536401274320813468317510194931629506994177
  | 4 => 31828687130226345097944463881396533766429193651030253916189694521162207808802136034115584
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 147 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 147 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 147 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 147 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 147 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 147 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row147

namespace Row148

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 127314748520905380391777855525586135065716774604121015664758778084648831235208544136462336
  | 1 => 79228162514264337593543950336
  | 2 => 5575186299632655785383929568162090376495104
  | 3 => 411376139330301510538742295639337626245683966408394965837152256
  | 4 => 127314748520905380391777855525586135065716774604121015664758778084648831235208544136462336
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 148 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 148 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 148 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 148 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 148 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 148 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row148

namespace Row149

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 509258994083621521567111422102344540262867098416484062659035112338595324940834176545849344
  | 1 => 54128700527712209531305509470022897418026882812731412828866990033402770979853189668476987797
  | 2 => 85627907008804952716438677352605686413977027152133924141837517240765961229267642960463937929
  | 3 => 165140319797470185214707837551716501233066651080426187903690122346084616899132468937600095520
  | 4 => 509258994083621521567111422102344540262867098416484062659035112338595324940834176545849344
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 149 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 149 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 149 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 149 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 149 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 149 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row149

namespace Row150

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376
  | 1 => 52219602553956693048657739409464055110224767032292044177702573307809020812132605521824933269
  | 2 => 22300745198530623141535718272648361505980416
  | 3 => 1645504557321206042154969182557350504982735865633579863348609024
  | 4 => 2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 150 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 150 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 150 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 150 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 150 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 150 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row150

namespace Row151

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 8148143905337944345073782753637512644205873574663745002544561797417525199053346824733589504
  | 1 => 131529267846921953664429623643644324718106198162543656096475598291196165510031112810503227926
  | 2 => 21055967027066828946819845875228461999163109057246102146288464547455647218121485878431326505
  | 3 => 6582018229284824168619876730229402019930943462534319453394436096
  | 4 => 8148143905337944345073782753637512644205873574663745002544561797417525199053346824733589504
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 151 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 151 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 151 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 151 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 151 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 151 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row151

namespace Row152

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 32592575621351777380295131014550050576823494298654980010178247189670100796213387298934358016
  | 1 => 214939251112727925999123331732920650013297086614043637712310749319126847740284687729720316197
  | 2 => 17076662589475736892911881245855794497022519740364542328870502569007863759950792708453408842
  | 3 => 282306795216666804851067829645936657768083874368481417615860271956485296285750908372669334661
  | 4 => 32592575621351777380295131014550050576823494298654980010178247189670100796213387298934358016
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 152 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 152 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 152 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 152 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 152 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 152 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row152

namespace Row153

def stageCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 130370302485407109521180524058200202307293977194619920040712988758680403184853549195737432064
  | 1 => 1267650600228229401496703205376
  | 2 => 89202980794122492566142873090593446023921664
  | 3 => 26328072917139296674479506920917608079723773850137277813577744384
  | 4 => 130370302485407109521180524058200202307293977194619920040712988758680403184853549195737432064
  | _ => 0

def rowVector (k : ℕ) (z : Fin 154) : ZMod 3 := packedDigit 2 (stageCode k) z.val

theorem packed_steps : ∀ (k : Fin 4) (z : Fin 154),
    packedDot 2 (stageCode k.val) (columnCode z.val) 154 % 3 =
      packedDigit 2 (stageCode (k.val+1)) z.val % 3 := by
  decide +kernel

theorem row_zero : ∀ z : Fin 154,
    rowVector 0 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 153 z := by
  decide +kernel

theorem row_step (k : ℕ) (hk : k < 4) (z : Fin 154) :
    rowVector (k+1) z = ∑ j : Fin 154,
      rowVector k j * CFSG.Models.MatrixData.matrix 3 154 rows2 j z := by
  exact (packed_row_step 3 154 2 rows2 (stageCode k) (stageCode (k+1)) columnCode
    source_column_binding (packed_steps ⟨k,hk⟩) z).symm

theorem fourth_power_row (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 153 z = rowVector 4 z :=
  matrix_pow_row_eq 3 154 rows2 153 4 rowVector row_zero row_step z

theorem selected_row_return : ∀ z : Fin 154,
    rowVector 4 z = (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 153 z := by
  decide +kernel

theorem row_identity (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) 153 z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) 153 z :=
  (fourth_power_row z).trans (selected_row_return z)

end Row153

theorem block_identity (i : Fin 8) (z : Fin 154) :
    (CFSG.Models.MatrixData.matrix 3 154 rows2 ^ 4) ⟨i.val + 146, by omega⟩ z =
      (1 : Matrix (Fin 154) (Fin 154) (ZMod 3)) ⟨i.val + 146, by omega⟩ z := by
  fin_cases i
  · exact Row146.row_identity z
  · exact Row147.row_identity z
  · exact Row148.row_identity z
  · exact Row149.row_identity z
  · exact Row150.row_identity z
  · exact Row151.row_identity z
  · exact Row152.row_identity z
  · exact Row153.row_identity z

end SymmetricSubgroupAsymptotics.CFSGONSecondFourthRows146Through153
