import SymmetricSubgroupAsymptotics.MatrixKroneckerProductReflection
import Mathlib.Tactic.FinCases

/-! Literal14/F5 selected caches; digit bounds and both pack bindings are independently kernel checked. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedCaches00
open MatrixKroneckerProductReflection MatrixKroneckerDotReflection
open MatrixNaturalRowDotReflection SmallNaturalMatrixProductReflection

def C003_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 1649451993089
  | 1 => 1855442749442
  | 2 => 619062593035
  | 3 => 1305670189056
  | 4 => 1718037381184
  | 5 => 1100048498688
  | 6 => 1305670062080
  | 7 => 627065225216
  | 8 => 206160527360
  | 9 => 137439215616
  | 10 => 1099578736640
  | 11 => 549755813888
  | 12 => 2474974904320
  | 13 => 68719476736
  | _ => 0

def C003_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 197121
  | 1 => 65536
  | 2 => 4294967296
  | 3 => 197636
  | 4 => 281474976710656
  | 5 => 17247175424
  | 6 => 4722366482869645213696
  | 7 => 18446744073709551616
  | 8 => 4835703278458529583923459
  | 9 => 4398046773249
  | 10 => 79228162514264337593543950336
  | 11 => 72057594037927936
  | 12 => 20599322263208873874305159594752
  | 13 => 317224552918590547457183122179
  | _ => 0

def C003_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 20282414439354948885766779961347
  | 1 => 40564824043061959539731841680131
  | 2 => 60926460600302074688859665334529
  | 3 => 73786976294838207234
  | 4 => 309485083608324662097871107
  | 5 => 17179869186
  | 6 => 4722366482869645214466
  | 7 => 65793
  | 8 => 281474976711424
  | 9 => 72057594037928448
  | 10 => 4398046511106
  | 11 => 1
  | 12 => 16778244
  | 13 => 256
  | _ => 0

def C003_digit (i j : Fin 14) : ℕ := packedDigit 3 (C003_lowColumnCode j) i.val

private theorem C003_bound_00 : ∀ j : Fin 14, C003_digit 0 j < 5 := by decide +kernel

private theorem C003_bound_01 : ∀ j : Fin 14, C003_digit 1 j < 5 := by decide +kernel

private theorem C003_bound_02 : ∀ j : Fin 14, C003_digit 2 j < 5 := by decide +kernel

private theorem C003_bound_03 : ∀ j : Fin 14, C003_digit 3 j < 5 := by decide +kernel

private theorem C003_bound_04 : ∀ j : Fin 14, C003_digit 4 j < 5 := by decide +kernel

private theorem C003_bound_05 : ∀ j : Fin 14, C003_digit 5 j < 5 := by decide +kernel

private theorem C003_bound_06 : ∀ j : Fin 14, C003_digit 6 j < 5 := by decide +kernel

private theorem C003_bound_07 : ∀ j : Fin 14, C003_digit 7 j < 5 := by decide +kernel

private theorem C003_bound_08 : ∀ j : Fin 14, C003_digit 8 j < 5 := by decide +kernel

private theorem C003_bound_09 : ∀ j : Fin 14, C003_digit 9 j < 5 := by decide +kernel

private theorem C003_bound_10 : ∀ j : Fin 14, C003_digit 10 j < 5 := by decide +kernel

private theorem C003_bound_11 : ∀ j : Fin 14, C003_digit 11 j < 5 := by decide +kernel

private theorem C003_bound_12 : ∀ j : Fin 14, C003_digit 12 j < 5 := by decide +kernel

private theorem C003_bound_13 : ∀ j : Fin 14, C003_digit 13 j < 5 := by decide +kernel

theorem C003_bound : ∀ i j : Fin 14, C003_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C003_bound_00 j
  · exact C003_bound_01 j
  · exact C003_bound_02 j
  · exact C003_bound_03 j
  · exact C003_bound_04 j
  · exact C003_bound_05 j
  · exact C003_bound_06 j
  · exact C003_bound_07 j
  · exact C003_bound_08 j
  · exact C003_bound_09 j
  · exact C003_bound_10 j
  · exact C003_bound_11 j
  · exact C003_bound_12 j
  · exact C003_bound_13 j

private theorem C003_row_00 : pack 256 (C003_digit 0)=C003_rowCode 0 := by decide +kernel

private theorem C003_row_01 : pack 256 (C003_digit 1)=C003_rowCode 1 := by decide +kernel

private theorem C003_row_02 : pack 256 (C003_digit 2)=C003_rowCode 2 := by decide +kernel

private theorem C003_row_03 : pack 256 (C003_digit 3)=C003_rowCode 3 := by decide +kernel

private theorem C003_row_04 : pack 256 (C003_digit 4)=C003_rowCode 4 := by decide +kernel

private theorem C003_row_05 : pack 256 (C003_digit 5)=C003_rowCode 5 := by decide +kernel

private theorem C003_row_06 : pack 256 (C003_digit 6)=C003_rowCode 6 := by decide +kernel

private theorem C003_row_07 : pack 256 (C003_digit 7)=C003_rowCode 7 := by decide +kernel

private theorem C003_row_08 : pack 256 (C003_digit 8)=C003_rowCode 8 := by decide +kernel

private theorem C003_row_09 : pack 256 (C003_digit 9)=C003_rowCode 9 := by decide +kernel

private theorem C003_row_10 : pack 256 (C003_digit 10)=C003_rowCode 10 := by decide +kernel

private theorem C003_row_11 : pack 256 (C003_digit 11)=C003_rowCode 11 := by decide +kernel

private theorem C003_row_12 : pack 256 (C003_digit 12)=C003_rowCode 12 := by decide +kernel

private theorem C003_row_13 : pack 256 (C003_digit 13)=C003_rowCode 13 := by decide +kernel

theorem C003_row_binding : ∀ i : Fin 14, pack 256 (C003_digit i)=C003_rowCode i := by
  intro i
  fin_cases i
  · exact C003_row_00
  · exact C003_row_01
  · exact C003_row_02
  · exact C003_row_03
  · exact C003_row_04
  · exact C003_row_05
  · exact C003_row_06
  · exact C003_row_07
  · exact C003_row_08
  · exact C003_row_09
  · exact C003_row_10
  · exact C003_row_11
  · exact C003_row_12
  · exact C003_row_13

private theorem C003_column_00 : reversePack 256 (fun j : Fin 14 => C003_digit j 0)=C003_columnCode 0 := by decide +kernel

private theorem C003_column_01 : reversePack 256 (fun j : Fin 14 => C003_digit j 1)=C003_columnCode 1 := by decide +kernel

private theorem C003_column_02 : reversePack 256 (fun j : Fin 14 => C003_digit j 2)=C003_columnCode 2 := by decide +kernel

private theorem C003_column_03 : reversePack 256 (fun j : Fin 14 => C003_digit j 3)=C003_columnCode 3 := by decide +kernel

private theorem C003_column_04 : reversePack 256 (fun j : Fin 14 => C003_digit j 4)=C003_columnCode 4 := by decide +kernel

private theorem C003_column_05 : reversePack 256 (fun j : Fin 14 => C003_digit j 5)=C003_columnCode 5 := by decide +kernel

private theorem C003_column_06 : reversePack 256 (fun j : Fin 14 => C003_digit j 6)=C003_columnCode 6 := by decide +kernel

private theorem C003_column_07 : reversePack 256 (fun j : Fin 14 => C003_digit j 7)=C003_columnCode 7 := by decide +kernel

private theorem C003_column_08 : reversePack 256 (fun j : Fin 14 => C003_digit j 8)=C003_columnCode 8 := by decide +kernel

private theorem C003_column_09 : reversePack 256 (fun j : Fin 14 => C003_digit j 9)=C003_columnCode 9 := by decide +kernel

private theorem C003_column_10 : reversePack 256 (fun j : Fin 14 => C003_digit j 10)=C003_columnCode 10 := by decide +kernel

private theorem C003_column_11 : reversePack 256 (fun j : Fin 14 => C003_digit j 11)=C003_columnCode 11 := by decide +kernel

private theorem C003_column_12 : reversePack 256 (fun j : Fin 14 => C003_digit j 12)=C003_columnCode 12 := by decide +kernel

private theorem C003_column_13 : reversePack 256 (fun j : Fin 14 => C003_digit j 13)=C003_columnCode 13 := by decide +kernel

theorem C003_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C003_digit j i)=C003_columnCode i := by
  intro i
  fin_cases i
  · exact C003_column_00
  · exact C003_column_01
  · exact C003_column_02
  · exact C003_column_03
  · exact C003_column_04
  · exact C003_column_05
  · exact C003_column_06
  · exact C003_column_07
  · exact C003_column_08
  · exact C003_column_09
  · exact C003_column_10
  · exact C003_column_11
  · exact C003_column_12
  · exact C003_column_13

def C003_data : PackedData 14 5 256 where
  raw := C003_digit
  digit_lt := C003_bound
  rowCode := C003_rowCode
  columnCode := C003_columnCode
  row_binding := C003_row_binding
  column_binding := C003_column_binding

def C004_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 1237135131172
  | 1 => 2405366235361
  | 2 => 2199493017817
  | 3 => 1374423122176
  | 4 => 2336495763712
  | 5 => 206160527360
  | 6 => 1100048498688
  | 7 => 1099578736640
  | 8 => 1305670062080
  | 9 => 627065225216
  | 10 => 137439215616
  | 11 => 68719476736
  | 12 => 549755813888
  | 13 => 2474974904320
  | _ => 0

def C004_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 65796
  | 1 => 197636
  | 2 => 17247175424
  | 3 => 1
  | 4 => 18446744073709551616
  | 5 => 16777216
  | 6 => 1208925819614629174706176
  | 7 => 1099511627776
  | 8 => 288230384775463683
  | 9 => 1125899907039489
  | 10 => 20282409603651670423947251286016
  | 11 => 4722366482869645213696
  | 12 => 81129950322245848988514045133570
  | 13 => 81208866581880350682554856375298
  | _ => 0

def C004_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 81446552273589558664095185502722
  | 1 => 20600250708738191812830431281924
  | 2 => 20521022546223927476344988893188
  | 3 => 1237940057732126547631932418
  | 4 => 1237940039285382473922380292
  | 5 => 281474976711424
  | 6 => 17179869186
  | 7 => 4398046511106
  | 8 => 4722366482869645214466
  | 9 => 65793
  | 10 => 72057594037928448
  | 11 => 256
  | 12 => 1
  | 13 => 16778244
  | _ => 0

def C004_digit (i j : Fin 14) : ℕ := packedDigit 3 (C004_lowColumnCode j) i.val

private theorem C004_bound_00 : ∀ j : Fin 14, C004_digit 0 j < 5 := by decide +kernel

private theorem C004_bound_01 : ∀ j : Fin 14, C004_digit 1 j < 5 := by decide +kernel

private theorem C004_bound_02 : ∀ j : Fin 14, C004_digit 2 j < 5 := by decide +kernel

private theorem C004_bound_03 : ∀ j : Fin 14, C004_digit 3 j < 5 := by decide +kernel

private theorem C004_bound_04 : ∀ j : Fin 14, C004_digit 4 j < 5 := by decide +kernel

private theorem C004_bound_05 : ∀ j : Fin 14, C004_digit 5 j < 5 := by decide +kernel

private theorem C004_bound_06 : ∀ j : Fin 14, C004_digit 6 j < 5 := by decide +kernel

private theorem C004_bound_07 : ∀ j : Fin 14, C004_digit 7 j < 5 := by decide +kernel

private theorem C004_bound_08 : ∀ j : Fin 14, C004_digit 8 j < 5 := by decide +kernel

private theorem C004_bound_09 : ∀ j : Fin 14, C004_digit 9 j < 5 := by decide +kernel

private theorem C004_bound_10 : ∀ j : Fin 14, C004_digit 10 j < 5 := by decide +kernel

private theorem C004_bound_11 : ∀ j : Fin 14, C004_digit 11 j < 5 := by decide +kernel

private theorem C004_bound_12 : ∀ j : Fin 14, C004_digit 12 j < 5 := by decide +kernel

private theorem C004_bound_13 : ∀ j : Fin 14, C004_digit 13 j < 5 := by decide +kernel

theorem C004_bound : ∀ i j : Fin 14, C004_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C004_bound_00 j
  · exact C004_bound_01 j
  · exact C004_bound_02 j
  · exact C004_bound_03 j
  · exact C004_bound_04 j
  · exact C004_bound_05 j
  · exact C004_bound_06 j
  · exact C004_bound_07 j
  · exact C004_bound_08 j
  · exact C004_bound_09 j
  · exact C004_bound_10 j
  · exact C004_bound_11 j
  · exact C004_bound_12 j
  · exact C004_bound_13 j

private theorem C004_row_00 : pack 256 (C004_digit 0)=C004_rowCode 0 := by decide +kernel

private theorem C004_row_01 : pack 256 (C004_digit 1)=C004_rowCode 1 := by decide +kernel

private theorem C004_row_02 : pack 256 (C004_digit 2)=C004_rowCode 2 := by decide +kernel

private theorem C004_row_03 : pack 256 (C004_digit 3)=C004_rowCode 3 := by decide +kernel

private theorem C004_row_04 : pack 256 (C004_digit 4)=C004_rowCode 4 := by decide +kernel

private theorem C004_row_05 : pack 256 (C004_digit 5)=C004_rowCode 5 := by decide +kernel

private theorem C004_row_06 : pack 256 (C004_digit 6)=C004_rowCode 6 := by decide +kernel

private theorem C004_row_07 : pack 256 (C004_digit 7)=C004_rowCode 7 := by decide +kernel

private theorem C004_row_08 : pack 256 (C004_digit 8)=C004_rowCode 8 := by decide +kernel

private theorem C004_row_09 : pack 256 (C004_digit 9)=C004_rowCode 9 := by decide +kernel

private theorem C004_row_10 : pack 256 (C004_digit 10)=C004_rowCode 10 := by decide +kernel

private theorem C004_row_11 : pack 256 (C004_digit 11)=C004_rowCode 11 := by decide +kernel

private theorem C004_row_12 : pack 256 (C004_digit 12)=C004_rowCode 12 := by decide +kernel

private theorem C004_row_13 : pack 256 (C004_digit 13)=C004_rowCode 13 := by decide +kernel

theorem C004_row_binding : ∀ i : Fin 14, pack 256 (C004_digit i)=C004_rowCode i := by
  intro i
  fin_cases i
  · exact C004_row_00
  · exact C004_row_01
  · exact C004_row_02
  · exact C004_row_03
  · exact C004_row_04
  · exact C004_row_05
  · exact C004_row_06
  · exact C004_row_07
  · exact C004_row_08
  · exact C004_row_09
  · exact C004_row_10
  · exact C004_row_11
  · exact C004_row_12
  · exact C004_row_13

private theorem C004_column_00 : reversePack 256 (fun j : Fin 14 => C004_digit j 0)=C004_columnCode 0 := by decide +kernel

private theorem C004_column_01 : reversePack 256 (fun j : Fin 14 => C004_digit j 1)=C004_columnCode 1 := by decide +kernel

private theorem C004_column_02 : reversePack 256 (fun j : Fin 14 => C004_digit j 2)=C004_columnCode 2 := by decide +kernel

private theorem C004_column_03 : reversePack 256 (fun j : Fin 14 => C004_digit j 3)=C004_columnCode 3 := by decide +kernel

private theorem C004_column_04 : reversePack 256 (fun j : Fin 14 => C004_digit j 4)=C004_columnCode 4 := by decide +kernel

private theorem C004_column_05 : reversePack 256 (fun j : Fin 14 => C004_digit j 5)=C004_columnCode 5 := by decide +kernel

private theorem C004_column_06 : reversePack 256 (fun j : Fin 14 => C004_digit j 6)=C004_columnCode 6 := by decide +kernel

private theorem C004_column_07 : reversePack 256 (fun j : Fin 14 => C004_digit j 7)=C004_columnCode 7 := by decide +kernel

private theorem C004_column_08 : reversePack 256 (fun j : Fin 14 => C004_digit j 8)=C004_columnCode 8 := by decide +kernel

private theorem C004_column_09 : reversePack 256 (fun j : Fin 14 => C004_digit j 9)=C004_columnCode 9 := by decide +kernel

private theorem C004_column_10 : reversePack 256 (fun j : Fin 14 => C004_digit j 10)=C004_columnCode 10 := by decide +kernel

private theorem C004_column_11 : reversePack 256 (fun j : Fin 14 => C004_digit j 11)=C004_columnCode 11 := by decide +kernel

private theorem C004_column_12 : reversePack 256 (fun j : Fin 14 => C004_digit j 12)=C004_columnCode 12 := by decide +kernel

private theorem C004_column_13 : reversePack 256 (fun j : Fin 14 => C004_digit j 13)=C004_columnCode 13 := by decide +kernel

theorem C004_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C004_digit j i)=C004_columnCode i := by
  intro i
  fin_cases i
  · exact C004_column_00
  · exact C004_column_01
  · exact C004_column_02
  · exact C004_column_03
  · exact C004_column_04
  · exact C004_column_05
  · exact C004_column_06
  · exact C004_column_07
  · exact C004_column_08
  · exact C004_column_09
  · exact C004_column_10
  · exact C004_column_11
  · exact C004_column_12
  · exact C004_column_13

def C004_data : PackedData 14 5 256 where
  raw := C004_digit
  digit_lt := C004_bound
  rowCode := C004_rowCode
  columnCode := C004_columnCode
  row_binding := C004_row_binding
  column_binding := C004_column_binding

def C005_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 2270450451458
  | 1 => 141086197787
  | 2 => 275289833497
  | 3 => 1310002840610
  | 4 => 1239270097954
  | 5 => 1867237031936
  | 6 => 1048576
  | 7 => 274886295552
  | 8 => 3271688256
  | 9 => 1073741824
  | 10 => 70866964480
  | 11 => 2474974904320
  | 12 => 68719476736
  | 13 => 1653629517824
  | _ => 0

def C005_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 8623555330
  | 1 => 17247175424
  | 2 => 18446744073709551616
  | 3 => 8623490050
  | 4 => 1208925819614629174706176
  | 5 => 73786976303461892353
  | 6 => 1125899907039489
  | 7 => 288230384775463683
  | 8 => 81129638414662021928018757288193
  | 9 => 4295164676
  | 10 => 81129950322245848988514045133570
  | 11 => 1099511627776
  | 12 => 80467311479657566180944904705
  | 13 => 60848466750994296655423811354628
  | _ => 0

def C005_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 40564821625173499724362254647556
  | 1 => 61084918134219602390344209007104
  | 2 => 20520094091250020967643917321216
  | 3 => 40881734275248931480823490675458
  | 4 => 40881734275248931480827752088066
  | 5 => 50397955
  | 6 => 288230376151711744
  | 7 => 1125899906843648
  | 8 => 309485083608324662148202496
  | 9 => 16777216
  | 10 => 4722366482869678768384
  | 11 => 16778244
  | 12 => 256
  | 13 => 4398113619971
  | _ => 0

def C005_digit (i j : Fin 14) : ℕ := packedDigit 3 (C005_lowColumnCode j) i.val

private theorem C005_bound_00 : ∀ j : Fin 14, C005_digit 0 j < 5 := by decide +kernel

private theorem C005_bound_01 : ∀ j : Fin 14, C005_digit 1 j < 5 := by decide +kernel

private theorem C005_bound_02 : ∀ j : Fin 14, C005_digit 2 j < 5 := by decide +kernel

private theorem C005_bound_03 : ∀ j : Fin 14, C005_digit 3 j < 5 := by decide +kernel

private theorem C005_bound_04 : ∀ j : Fin 14, C005_digit 4 j < 5 := by decide +kernel

private theorem C005_bound_05 : ∀ j : Fin 14, C005_digit 5 j < 5 := by decide +kernel

private theorem C005_bound_06 : ∀ j : Fin 14, C005_digit 6 j < 5 := by decide +kernel

private theorem C005_bound_07 : ∀ j : Fin 14, C005_digit 7 j < 5 := by decide +kernel

private theorem C005_bound_08 : ∀ j : Fin 14, C005_digit 8 j < 5 := by decide +kernel

private theorem C005_bound_09 : ∀ j : Fin 14, C005_digit 9 j < 5 := by decide +kernel

private theorem C005_bound_10 : ∀ j : Fin 14, C005_digit 10 j < 5 := by decide +kernel

private theorem C005_bound_11 : ∀ j : Fin 14, C005_digit 11 j < 5 := by decide +kernel

private theorem C005_bound_12 : ∀ j : Fin 14, C005_digit 12 j < 5 := by decide +kernel

private theorem C005_bound_13 : ∀ j : Fin 14, C005_digit 13 j < 5 := by decide +kernel

theorem C005_bound : ∀ i j : Fin 14, C005_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C005_bound_00 j
  · exact C005_bound_01 j
  · exact C005_bound_02 j
  · exact C005_bound_03 j
  · exact C005_bound_04 j
  · exact C005_bound_05 j
  · exact C005_bound_06 j
  · exact C005_bound_07 j
  · exact C005_bound_08 j
  · exact C005_bound_09 j
  · exact C005_bound_10 j
  · exact C005_bound_11 j
  · exact C005_bound_12 j
  · exact C005_bound_13 j

private theorem C005_row_00 : pack 256 (C005_digit 0)=C005_rowCode 0 := by decide +kernel

private theorem C005_row_01 : pack 256 (C005_digit 1)=C005_rowCode 1 := by decide +kernel

private theorem C005_row_02 : pack 256 (C005_digit 2)=C005_rowCode 2 := by decide +kernel

private theorem C005_row_03 : pack 256 (C005_digit 3)=C005_rowCode 3 := by decide +kernel

private theorem C005_row_04 : pack 256 (C005_digit 4)=C005_rowCode 4 := by decide +kernel

private theorem C005_row_05 : pack 256 (C005_digit 5)=C005_rowCode 5 := by decide +kernel

private theorem C005_row_06 : pack 256 (C005_digit 6)=C005_rowCode 6 := by decide +kernel

private theorem C005_row_07 : pack 256 (C005_digit 7)=C005_rowCode 7 := by decide +kernel

private theorem C005_row_08 : pack 256 (C005_digit 8)=C005_rowCode 8 := by decide +kernel

private theorem C005_row_09 : pack 256 (C005_digit 9)=C005_rowCode 9 := by decide +kernel

private theorem C005_row_10 : pack 256 (C005_digit 10)=C005_rowCode 10 := by decide +kernel

private theorem C005_row_11 : pack 256 (C005_digit 11)=C005_rowCode 11 := by decide +kernel

private theorem C005_row_12 : pack 256 (C005_digit 12)=C005_rowCode 12 := by decide +kernel

private theorem C005_row_13 : pack 256 (C005_digit 13)=C005_rowCode 13 := by decide +kernel

theorem C005_row_binding : ∀ i : Fin 14, pack 256 (C005_digit i)=C005_rowCode i := by
  intro i
  fin_cases i
  · exact C005_row_00
  · exact C005_row_01
  · exact C005_row_02
  · exact C005_row_03
  · exact C005_row_04
  · exact C005_row_05
  · exact C005_row_06
  · exact C005_row_07
  · exact C005_row_08
  · exact C005_row_09
  · exact C005_row_10
  · exact C005_row_11
  · exact C005_row_12
  · exact C005_row_13

private theorem C005_column_00 : reversePack 256 (fun j : Fin 14 => C005_digit j 0)=C005_columnCode 0 := by decide +kernel

private theorem C005_column_01 : reversePack 256 (fun j : Fin 14 => C005_digit j 1)=C005_columnCode 1 := by decide +kernel

private theorem C005_column_02 : reversePack 256 (fun j : Fin 14 => C005_digit j 2)=C005_columnCode 2 := by decide +kernel

private theorem C005_column_03 : reversePack 256 (fun j : Fin 14 => C005_digit j 3)=C005_columnCode 3 := by decide +kernel

private theorem C005_column_04 : reversePack 256 (fun j : Fin 14 => C005_digit j 4)=C005_columnCode 4 := by decide +kernel

private theorem C005_column_05 : reversePack 256 (fun j : Fin 14 => C005_digit j 5)=C005_columnCode 5 := by decide +kernel

private theorem C005_column_06 : reversePack 256 (fun j : Fin 14 => C005_digit j 6)=C005_columnCode 6 := by decide +kernel

private theorem C005_column_07 : reversePack 256 (fun j : Fin 14 => C005_digit j 7)=C005_columnCode 7 := by decide +kernel

private theorem C005_column_08 : reversePack 256 (fun j : Fin 14 => C005_digit j 8)=C005_columnCode 8 := by decide +kernel

private theorem C005_column_09 : reversePack 256 (fun j : Fin 14 => C005_digit j 9)=C005_columnCode 9 := by decide +kernel

private theorem C005_column_10 : reversePack 256 (fun j : Fin 14 => C005_digit j 10)=C005_columnCode 10 := by decide +kernel

private theorem C005_column_11 : reversePack 256 (fun j : Fin 14 => C005_digit j 11)=C005_columnCode 11 := by decide +kernel

private theorem C005_column_12 : reversePack 256 (fun j : Fin 14 => C005_digit j 12)=C005_columnCode 12 := by decide +kernel

private theorem C005_column_13 : reversePack 256 (fun j : Fin 14 => C005_digit j 13)=C005_columnCode 13 := by decide +kernel

theorem C005_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C005_digit j i)=C005_columnCode i := by
  intro i
  fin_cases i
  · exact C005_column_00
  · exact C005_column_01
  · exact C005_column_02
  · exact C005_column_03
  · exact C005_column_04
  · exact C005_column_05
  · exact C005_column_06
  · exact C005_column_07
  · exact C005_column_08
  · exact C005_column_09
  · exact C005_column_10
  · exact C005_column_11
  · exact C005_column_12
  · exact C005_column_13

def C005_data : PackedData 14 5 256 where
  raw := C005_digit
  digit_lt := C005_bound
  rowCode := C005_rowCode
  columnCode := C005_columnCode
  row_binding := C005_row_binding
  column_binding := C005_column_binding

def C006_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 95767598594
  | 1 => 1402645256196
  | 2 => 2512976228866
  | 3 => 1669689509888
  | 4 => 225540573184
  | 5 => 2202278035456
  | 6 => 1786706411520
  | 7 => 38654705664
  | 8 => 6391307
  | 9 => 1099578736640
  | 10 => 550846464064
  | 11 => 1653629517824
  | 12 => 2474974904320
  | 13 => 1649292607488
  | _ => 0

def C006_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 55340232221128786946
  | 1 => 18446744073709551616
  | 2 => 1208925819614629174706176
  | 3 => 55340232238375699459
  | 4 => 1125899907039489
  | 5 => 4835758618690737827741699
  | 6 => 4295164676
  | 7 => 81129638414662021928018757288193
  | 8 => 20283648771506241352541830972420
  | 9 => 197121
  | 10 => 80467311479657566180944904705
  | 11 => 288230384775463683
  | 12 => 316912650057057913337014387713
  | 13 => 61165071134412086086613596373504
  | _ => 0

def C006_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 40564822838858794923126287433984
  | 1 => 81129643255032543095839109874690
  | 2 => 40564820430470263061322028811268
  | 3 => 4835703279022566214336515
  | 4 => 4835703351082359258743552
  | 5 => 2199073587204
  | 6 => 18889465931478580855299
  | 7 => 67371008
  | 8 => 60926460600302075529968880713728
  | 9 => 4398046511106
  | 10 => 309485083608322463091392513
  | 11 => 4398113619971
  | 12 => 16778244
  | 13 => 1126999418470403
  | _ => 0

def C006_digit (i j : Fin 14) : ℕ := packedDigit 3 (C006_lowColumnCode j) i.val

private theorem C006_bound_00 : ∀ j : Fin 14, C006_digit 0 j < 5 := by decide +kernel

private theorem C006_bound_01 : ∀ j : Fin 14, C006_digit 1 j < 5 := by decide +kernel

private theorem C006_bound_02 : ∀ j : Fin 14, C006_digit 2 j < 5 := by decide +kernel

private theorem C006_bound_03 : ∀ j : Fin 14, C006_digit 3 j < 5 := by decide +kernel

private theorem C006_bound_04 : ∀ j : Fin 14, C006_digit 4 j < 5 := by decide +kernel

private theorem C006_bound_05 : ∀ j : Fin 14, C006_digit 5 j < 5 := by decide +kernel

private theorem C006_bound_06 : ∀ j : Fin 14, C006_digit 6 j < 5 := by decide +kernel

private theorem C006_bound_07 : ∀ j : Fin 14, C006_digit 7 j < 5 := by decide +kernel

private theorem C006_bound_08 : ∀ j : Fin 14, C006_digit 8 j < 5 := by decide +kernel

private theorem C006_bound_09 : ∀ j : Fin 14, C006_digit 9 j < 5 := by decide +kernel

private theorem C006_bound_10 : ∀ j : Fin 14, C006_digit 10 j < 5 := by decide +kernel

private theorem C006_bound_11 : ∀ j : Fin 14, C006_digit 11 j < 5 := by decide +kernel

private theorem C006_bound_12 : ∀ j : Fin 14, C006_digit 12 j < 5 := by decide +kernel

private theorem C006_bound_13 : ∀ j : Fin 14, C006_digit 13 j < 5 := by decide +kernel

theorem C006_bound : ∀ i j : Fin 14, C006_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C006_bound_00 j
  · exact C006_bound_01 j
  · exact C006_bound_02 j
  · exact C006_bound_03 j
  · exact C006_bound_04 j
  · exact C006_bound_05 j
  · exact C006_bound_06 j
  · exact C006_bound_07 j
  · exact C006_bound_08 j
  · exact C006_bound_09 j
  · exact C006_bound_10 j
  · exact C006_bound_11 j
  · exact C006_bound_12 j
  · exact C006_bound_13 j

private theorem C006_row_00 : pack 256 (C006_digit 0)=C006_rowCode 0 := by decide +kernel

private theorem C006_row_01 : pack 256 (C006_digit 1)=C006_rowCode 1 := by decide +kernel

private theorem C006_row_02 : pack 256 (C006_digit 2)=C006_rowCode 2 := by decide +kernel

private theorem C006_row_03 : pack 256 (C006_digit 3)=C006_rowCode 3 := by decide +kernel

private theorem C006_row_04 : pack 256 (C006_digit 4)=C006_rowCode 4 := by decide +kernel

private theorem C006_row_05 : pack 256 (C006_digit 5)=C006_rowCode 5 := by decide +kernel

private theorem C006_row_06 : pack 256 (C006_digit 6)=C006_rowCode 6 := by decide +kernel

private theorem C006_row_07 : pack 256 (C006_digit 7)=C006_rowCode 7 := by decide +kernel

private theorem C006_row_08 : pack 256 (C006_digit 8)=C006_rowCode 8 := by decide +kernel

private theorem C006_row_09 : pack 256 (C006_digit 9)=C006_rowCode 9 := by decide +kernel

private theorem C006_row_10 : pack 256 (C006_digit 10)=C006_rowCode 10 := by decide +kernel

private theorem C006_row_11 : pack 256 (C006_digit 11)=C006_rowCode 11 := by decide +kernel

private theorem C006_row_12 : pack 256 (C006_digit 12)=C006_rowCode 12 := by decide +kernel

private theorem C006_row_13 : pack 256 (C006_digit 13)=C006_rowCode 13 := by decide +kernel

theorem C006_row_binding : ∀ i : Fin 14, pack 256 (C006_digit i)=C006_rowCode i := by
  intro i
  fin_cases i
  · exact C006_row_00
  · exact C006_row_01
  · exact C006_row_02
  · exact C006_row_03
  · exact C006_row_04
  · exact C006_row_05
  · exact C006_row_06
  · exact C006_row_07
  · exact C006_row_08
  · exact C006_row_09
  · exact C006_row_10
  · exact C006_row_11
  · exact C006_row_12
  · exact C006_row_13

private theorem C006_column_00 : reversePack 256 (fun j : Fin 14 => C006_digit j 0)=C006_columnCode 0 := by decide +kernel

private theorem C006_column_01 : reversePack 256 (fun j : Fin 14 => C006_digit j 1)=C006_columnCode 1 := by decide +kernel

private theorem C006_column_02 : reversePack 256 (fun j : Fin 14 => C006_digit j 2)=C006_columnCode 2 := by decide +kernel

private theorem C006_column_03 : reversePack 256 (fun j : Fin 14 => C006_digit j 3)=C006_columnCode 3 := by decide +kernel

private theorem C006_column_04 : reversePack 256 (fun j : Fin 14 => C006_digit j 4)=C006_columnCode 4 := by decide +kernel

private theorem C006_column_05 : reversePack 256 (fun j : Fin 14 => C006_digit j 5)=C006_columnCode 5 := by decide +kernel

private theorem C006_column_06 : reversePack 256 (fun j : Fin 14 => C006_digit j 6)=C006_columnCode 6 := by decide +kernel

private theorem C006_column_07 : reversePack 256 (fun j : Fin 14 => C006_digit j 7)=C006_columnCode 7 := by decide +kernel

private theorem C006_column_08 : reversePack 256 (fun j : Fin 14 => C006_digit j 8)=C006_columnCode 8 := by decide +kernel

private theorem C006_column_09 : reversePack 256 (fun j : Fin 14 => C006_digit j 9)=C006_columnCode 9 := by decide +kernel

private theorem C006_column_10 : reversePack 256 (fun j : Fin 14 => C006_digit j 10)=C006_columnCode 10 := by decide +kernel

private theorem C006_column_11 : reversePack 256 (fun j : Fin 14 => C006_digit j 11)=C006_columnCode 11 := by decide +kernel

private theorem C006_column_12 : reversePack 256 (fun j : Fin 14 => C006_digit j 12)=C006_columnCode 12 := by decide +kernel

private theorem C006_column_13 : reversePack 256 (fun j : Fin 14 => C006_digit j 13)=C006_columnCode 13 := by decide +kernel

theorem C006_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C006_digit j i)=C006_columnCode i := by
  intro i
  fin_cases i
  · exact C006_column_00
  · exact C006_column_01
  · exact C006_column_02
  · exact C006_column_03
  · exact C006_column_04
  · exact C006_column_05
  · exact C006_column_06
  · exact C006_column_07
  · exact C006_column_08
  · exact C006_column_09
  · exact C006_column_10
  · exact C006_column_11
  · exact C006_column_12
  · exact C006_column_13

def C006_data : PackedData 14 5 256 where
  raw := C006_digit
  digit_lt := C006_bound
  rowCode := C006_rowCode
  columnCode := C006_columnCode
  row_binding := C006_row_binding
  column_binding := C006_column_binding

def C007_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 1179375642203
  | 1 => 1727824769603
  | 2 => 1747454396449
  | 3 => 2355857049728
  | 4 => 2495443478656
  | 5 => 1653595975680
  | 6 => 262144
  | 7 => 2097152
  | 8 => 1411375706329
  | 9 => 70866964480
  | 10 => 1100757410850
  | 11 => 1102749634560
  | 12 => 68719476736
  | 13 => 2476115804416
  | _ => 0

def C007_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 2417870085973332059030275
  | 1 => 4835758618690737827741699
  | 2 => 81129638414662021928018757288193
  | 3 => 2417851639229275596652803
  | 4 => 81129950322245848988514045133570
  | 5 => 20282412021503309653218536194816
  | 6 => 55340513700417175553
  | 7 => 2417925498263147225744130
  | 8 => 81129950317541929248627188040192
  | 9 => 1208981159846850303557891
  | 10 => 40565748880740250956031821283586
  | 11 => 73786976303461892353
  | 12 => 81208866581917099492564246003969
  | 13 => 81130259802514857106648005280514
  | _ => 0

def C007_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 61085226419729890059874834907394
  | 1 => 60847539519113092758997982839043
  | 2 => 20599327089485866115562914119939
  | 3 => 623824667799374345976021508
  | 4 => 623815223066408606719149060
  | 5 => 14167099450808026005507
  | 6 => 72057594037927936
  | 7 => 281474976710656
  | 8 => 20521022560391244223635978978306
  | 9 => 4722366482869678768384
  | 10 => 40881734284693664446567025737730
  | 11 => 4722366483969207173122
  | 12 => 256
  | 13 => 1237958947198060225269597188
  | _ => 0

def C007_digit (i j : Fin 14) : ℕ := packedDigit 3 (C007_lowColumnCode j) i.val

private theorem C007_bound_00 : ∀ j : Fin 14, C007_digit 0 j < 5 := by decide +kernel

private theorem C007_bound_01 : ∀ j : Fin 14, C007_digit 1 j < 5 := by decide +kernel

private theorem C007_bound_02 : ∀ j : Fin 14, C007_digit 2 j < 5 := by decide +kernel

private theorem C007_bound_03 : ∀ j : Fin 14, C007_digit 3 j < 5 := by decide +kernel

private theorem C007_bound_04 : ∀ j : Fin 14, C007_digit 4 j < 5 := by decide +kernel

private theorem C007_bound_05 : ∀ j : Fin 14, C007_digit 5 j < 5 := by decide +kernel

private theorem C007_bound_06 : ∀ j : Fin 14, C007_digit 6 j < 5 := by decide +kernel

private theorem C007_bound_07 : ∀ j : Fin 14, C007_digit 7 j < 5 := by decide +kernel

private theorem C007_bound_08 : ∀ j : Fin 14, C007_digit 8 j < 5 := by decide +kernel

private theorem C007_bound_09 : ∀ j : Fin 14, C007_digit 9 j < 5 := by decide +kernel

private theorem C007_bound_10 : ∀ j : Fin 14, C007_digit 10 j < 5 := by decide +kernel

private theorem C007_bound_11 : ∀ j : Fin 14, C007_digit 11 j < 5 := by decide +kernel

private theorem C007_bound_12 : ∀ j : Fin 14, C007_digit 12 j < 5 := by decide +kernel

private theorem C007_bound_13 : ∀ j : Fin 14, C007_digit 13 j < 5 := by decide +kernel

theorem C007_bound : ∀ i j : Fin 14, C007_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C007_bound_00 j
  · exact C007_bound_01 j
  · exact C007_bound_02 j
  · exact C007_bound_03 j
  · exact C007_bound_04 j
  · exact C007_bound_05 j
  · exact C007_bound_06 j
  · exact C007_bound_07 j
  · exact C007_bound_08 j
  · exact C007_bound_09 j
  · exact C007_bound_10 j
  · exact C007_bound_11 j
  · exact C007_bound_12 j
  · exact C007_bound_13 j

private theorem C007_row_00 : pack 256 (C007_digit 0)=C007_rowCode 0 := by decide +kernel

private theorem C007_row_01 : pack 256 (C007_digit 1)=C007_rowCode 1 := by decide +kernel

private theorem C007_row_02 : pack 256 (C007_digit 2)=C007_rowCode 2 := by decide +kernel

private theorem C007_row_03 : pack 256 (C007_digit 3)=C007_rowCode 3 := by decide +kernel

private theorem C007_row_04 : pack 256 (C007_digit 4)=C007_rowCode 4 := by decide +kernel

private theorem C007_row_05 : pack 256 (C007_digit 5)=C007_rowCode 5 := by decide +kernel

private theorem C007_row_06 : pack 256 (C007_digit 6)=C007_rowCode 6 := by decide +kernel

private theorem C007_row_07 : pack 256 (C007_digit 7)=C007_rowCode 7 := by decide +kernel

private theorem C007_row_08 : pack 256 (C007_digit 8)=C007_rowCode 8 := by decide +kernel

private theorem C007_row_09 : pack 256 (C007_digit 9)=C007_rowCode 9 := by decide +kernel

private theorem C007_row_10 : pack 256 (C007_digit 10)=C007_rowCode 10 := by decide +kernel

private theorem C007_row_11 : pack 256 (C007_digit 11)=C007_rowCode 11 := by decide +kernel

private theorem C007_row_12 : pack 256 (C007_digit 12)=C007_rowCode 12 := by decide +kernel

private theorem C007_row_13 : pack 256 (C007_digit 13)=C007_rowCode 13 := by decide +kernel

theorem C007_row_binding : ∀ i : Fin 14, pack 256 (C007_digit i)=C007_rowCode i := by
  intro i
  fin_cases i
  · exact C007_row_00
  · exact C007_row_01
  · exact C007_row_02
  · exact C007_row_03
  · exact C007_row_04
  · exact C007_row_05
  · exact C007_row_06
  · exact C007_row_07
  · exact C007_row_08
  · exact C007_row_09
  · exact C007_row_10
  · exact C007_row_11
  · exact C007_row_12
  · exact C007_row_13

private theorem C007_column_00 : reversePack 256 (fun j : Fin 14 => C007_digit j 0)=C007_columnCode 0 := by decide +kernel

private theorem C007_column_01 : reversePack 256 (fun j : Fin 14 => C007_digit j 1)=C007_columnCode 1 := by decide +kernel

private theorem C007_column_02 : reversePack 256 (fun j : Fin 14 => C007_digit j 2)=C007_columnCode 2 := by decide +kernel

private theorem C007_column_03 : reversePack 256 (fun j : Fin 14 => C007_digit j 3)=C007_columnCode 3 := by decide +kernel

private theorem C007_column_04 : reversePack 256 (fun j : Fin 14 => C007_digit j 4)=C007_columnCode 4 := by decide +kernel

private theorem C007_column_05 : reversePack 256 (fun j : Fin 14 => C007_digit j 5)=C007_columnCode 5 := by decide +kernel

private theorem C007_column_06 : reversePack 256 (fun j : Fin 14 => C007_digit j 6)=C007_columnCode 6 := by decide +kernel

private theorem C007_column_07 : reversePack 256 (fun j : Fin 14 => C007_digit j 7)=C007_columnCode 7 := by decide +kernel

private theorem C007_column_08 : reversePack 256 (fun j : Fin 14 => C007_digit j 8)=C007_columnCode 8 := by decide +kernel

private theorem C007_column_09 : reversePack 256 (fun j : Fin 14 => C007_digit j 9)=C007_columnCode 9 := by decide +kernel

private theorem C007_column_10 : reversePack 256 (fun j : Fin 14 => C007_digit j 10)=C007_columnCode 10 := by decide +kernel

private theorem C007_column_11 : reversePack 256 (fun j : Fin 14 => C007_digit j 11)=C007_columnCode 11 := by decide +kernel

private theorem C007_column_12 : reversePack 256 (fun j : Fin 14 => C007_digit j 12)=C007_columnCode 12 := by decide +kernel

private theorem C007_column_13 : reversePack 256 (fun j : Fin 14 => C007_digit j 13)=C007_columnCode 13 := by decide +kernel

theorem C007_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C007_digit j i)=C007_columnCode i := by
  intro i
  fin_cases i
  · exact C007_column_00
  · exact C007_column_01
  · exact C007_column_02
  · exact C007_column_03
  · exact C007_column_04
  · exact C007_column_05
  · exact C007_column_06
  · exact C007_column_07
  · exact C007_column_08
  · exact C007_column_09
  · exact C007_column_10
  · exact C007_column_11
  · exact C007_column_12
  · exact C007_column_13

def C007_data : PackedData 14 5 256 where
  raw := C007_digit
  digit_lt := C007_bound
  rowCode := C007_rowCode
  columnCode := C007_columnCode
  row_binding := C007_row_binding
  column_binding := C007_column_binding

def C008_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 837796497425
  | 1 => 1961247130658
  | 2 => 87528940760
  | 3 => 68736319680
  | 4 => 1719345952860
  | 5 => 1788904284352
  | 6 => 1119946541056
  | 7 => 549755846912
  | 8 => 206160527360
  | 9 => 137439215616
  | 10 => 835709370388
  | 11 => 2476115804416
  | 12 => 1653751198818
  | 13 => 68719476736
  | _ => 0

def C008_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 158461160731807133720966595073
  | 1 => 316915067908696579645410313218
  | 2 => 80466102553837951547475165184
  | 3 => 158456325028529801104174744068
  | 4 => 238922427582078395267439264768
  | 5 => 79540065375796971722303012864
  | 6 => 2422574005993602971337732
  | 7 => 158457533972795033889972224772
  | 8 => 238927263285357417825029915392
  | 9 => 79230580365903566860483560450
  | 10 => 317534037928340116398223196676
  | 11 => 1208925820177579128259585
  | 12 => 20283652388894307462902603383812
  | 13 => 238923636507970631540116816641
  | _ => 0

def C008_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 20440870764383766913935753675777
  | 1 => 40881734294101792437122439054339
  | 2 => 238615369923969757797259804928
  | 3 => 928455066357524453105074432
  | 4 => 81367637237066567450019533684995
  | 5 => 928464511090492391452312067
  | 6 => 4835703350518309810470914
  | 7 => 1237940057732124348608675841
  | 8 => 281474976711424
  | 9 => 72057594037928448
  | 10 => 81288094739672248260193234781185
  | 11 => 1237958947198060225269597188
  | 12 => 40882043774407405531531248140291
  | 13 => 256
  | _ => 0

def C008_digit (i j : Fin 14) : ℕ := packedDigit 3 (C008_lowColumnCode j) i.val

private theorem C008_bound_00 : ∀ j : Fin 14, C008_digit 0 j < 5 := by decide +kernel

private theorem C008_bound_01 : ∀ j : Fin 14, C008_digit 1 j < 5 := by decide +kernel

private theorem C008_bound_02 : ∀ j : Fin 14, C008_digit 2 j < 5 := by decide +kernel

private theorem C008_bound_03 : ∀ j : Fin 14, C008_digit 3 j < 5 := by decide +kernel

private theorem C008_bound_04 : ∀ j : Fin 14, C008_digit 4 j < 5 := by decide +kernel

private theorem C008_bound_05 : ∀ j : Fin 14, C008_digit 5 j < 5 := by decide +kernel

private theorem C008_bound_06 : ∀ j : Fin 14, C008_digit 6 j < 5 := by decide +kernel

private theorem C008_bound_07 : ∀ j : Fin 14, C008_digit 7 j < 5 := by decide +kernel

private theorem C008_bound_08 : ∀ j : Fin 14, C008_digit 8 j < 5 := by decide +kernel

private theorem C008_bound_09 : ∀ j : Fin 14, C008_digit 9 j < 5 := by decide +kernel

private theorem C008_bound_10 : ∀ j : Fin 14, C008_digit 10 j < 5 := by decide +kernel

private theorem C008_bound_11 : ∀ j : Fin 14, C008_digit 11 j < 5 := by decide +kernel

private theorem C008_bound_12 : ∀ j : Fin 14, C008_digit 12 j < 5 := by decide +kernel

private theorem C008_bound_13 : ∀ j : Fin 14, C008_digit 13 j < 5 := by decide +kernel

theorem C008_bound : ∀ i j : Fin 14, C008_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C008_bound_00 j
  · exact C008_bound_01 j
  · exact C008_bound_02 j
  · exact C008_bound_03 j
  · exact C008_bound_04 j
  · exact C008_bound_05 j
  · exact C008_bound_06 j
  · exact C008_bound_07 j
  · exact C008_bound_08 j
  · exact C008_bound_09 j
  · exact C008_bound_10 j
  · exact C008_bound_11 j
  · exact C008_bound_12 j
  · exact C008_bound_13 j

private theorem C008_row_00 : pack 256 (C008_digit 0)=C008_rowCode 0 := by decide +kernel

private theorem C008_row_01 : pack 256 (C008_digit 1)=C008_rowCode 1 := by decide +kernel

private theorem C008_row_02 : pack 256 (C008_digit 2)=C008_rowCode 2 := by decide +kernel

private theorem C008_row_03 : pack 256 (C008_digit 3)=C008_rowCode 3 := by decide +kernel

private theorem C008_row_04 : pack 256 (C008_digit 4)=C008_rowCode 4 := by decide +kernel

private theorem C008_row_05 : pack 256 (C008_digit 5)=C008_rowCode 5 := by decide +kernel

private theorem C008_row_06 : pack 256 (C008_digit 6)=C008_rowCode 6 := by decide +kernel

private theorem C008_row_07 : pack 256 (C008_digit 7)=C008_rowCode 7 := by decide +kernel

private theorem C008_row_08 : pack 256 (C008_digit 8)=C008_rowCode 8 := by decide +kernel

private theorem C008_row_09 : pack 256 (C008_digit 9)=C008_rowCode 9 := by decide +kernel

private theorem C008_row_10 : pack 256 (C008_digit 10)=C008_rowCode 10 := by decide +kernel

private theorem C008_row_11 : pack 256 (C008_digit 11)=C008_rowCode 11 := by decide +kernel

private theorem C008_row_12 : pack 256 (C008_digit 12)=C008_rowCode 12 := by decide +kernel

private theorem C008_row_13 : pack 256 (C008_digit 13)=C008_rowCode 13 := by decide +kernel

theorem C008_row_binding : ∀ i : Fin 14, pack 256 (C008_digit i)=C008_rowCode i := by
  intro i
  fin_cases i
  · exact C008_row_00
  · exact C008_row_01
  · exact C008_row_02
  · exact C008_row_03
  · exact C008_row_04
  · exact C008_row_05
  · exact C008_row_06
  · exact C008_row_07
  · exact C008_row_08
  · exact C008_row_09
  · exact C008_row_10
  · exact C008_row_11
  · exact C008_row_12
  · exact C008_row_13

private theorem C008_column_00 : reversePack 256 (fun j : Fin 14 => C008_digit j 0)=C008_columnCode 0 := by decide +kernel

private theorem C008_column_01 : reversePack 256 (fun j : Fin 14 => C008_digit j 1)=C008_columnCode 1 := by decide +kernel

private theorem C008_column_02 : reversePack 256 (fun j : Fin 14 => C008_digit j 2)=C008_columnCode 2 := by decide +kernel

private theorem C008_column_03 : reversePack 256 (fun j : Fin 14 => C008_digit j 3)=C008_columnCode 3 := by decide +kernel

private theorem C008_column_04 : reversePack 256 (fun j : Fin 14 => C008_digit j 4)=C008_columnCode 4 := by decide +kernel

private theorem C008_column_05 : reversePack 256 (fun j : Fin 14 => C008_digit j 5)=C008_columnCode 5 := by decide +kernel

private theorem C008_column_06 : reversePack 256 (fun j : Fin 14 => C008_digit j 6)=C008_columnCode 6 := by decide +kernel

private theorem C008_column_07 : reversePack 256 (fun j : Fin 14 => C008_digit j 7)=C008_columnCode 7 := by decide +kernel

private theorem C008_column_08 : reversePack 256 (fun j : Fin 14 => C008_digit j 8)=C008_columnCode 8 := by decide +kernel

private theorem C008_column_09 : reversePack 256 (fun j : Fin 14 => C008_digit j 9)=C008_columnCode 9 := by decide +kernel

private theorem C008_column_10 : reversePack 256 (fun j : Fin 14 => C008_digit j 10)=C008_columnCode 10 := by decide +kernel

private theorem C008_column_11 : reversePack 256 (fun j : Fin 14 => C008_digit j 11)=C008_columnCode 11 := by decide +kernel

private theorem C008_column_12 : reversePack 256 (fun j : Fin 14 => C008_digit j 12)=C008_columnCode 12 := by decide +kernel

private theorem C008_column_13 : reversePack 256 (fun j : Fin 14 => C008_digit j 13)=C008_columnCode 13 := by decide +kernel

theorem C008_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C008_digit j i)=C008_columnCode i := by
  intro i
  fin_cases i
  · exact C008_column_00
  · exact C008_column_01
  · exact C008_column_02
  · exact C008_column_03
  · exact C008_column_04
  · exact C008_column_05
  · exact C008_column_06
  · exact C008_column_07
  · exact C008_column_08
  · exact C008_column_09
  · exact C008_column_10
  · exact C008_column_11
  · exact C008_column_12
  · exact C008_column_13

def C008_data : PackedData 14 5 256 where
  raw := C008_digit
  digit_lt := C008_bound
  rowCode := C008_rowCode
  columnCode := C008_columnCode
  row_binding := C008_row_binding
  column_binding := C008_column_binding

end SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedCaches00
