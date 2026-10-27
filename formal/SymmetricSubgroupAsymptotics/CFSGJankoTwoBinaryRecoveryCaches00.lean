import SymmetricSubgroupAsymptotics.MatrixKroneckerProductReflection
import Mathlib.Tactic.FinCases

/-! Literal14/F5 selected caches; digit bounds and both pack bindings are independently kernel checked. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryCaches00
open MatrixKroneckerProductReflection MatrixKroneckerDotReflection
open MatrixNaturalRowDotReflection SmallNaturalMatrixProductReflection

def C003_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 100
  | 1 => 1548
  | 2 => 1547
  | 3 => 6144
  | 4 => 2048
  | 5 => 262144
  | 6 => 16777216
  | 7 => 134217728
  | 8 => 32768
  | 9 => 1073741824
  | 10 => 2097152
  | 11 => 68719476736
  | 12 => 549755813888
  | 13 => 8589934592
  | _ => 0

def C003_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 197636
  | 1 => 65796
  | 2 => 1
  | 3 => 17247175424
  | 4 => 16777216
  | 5 => 18446744073709551616
  | 6 => 1099511627776
  | 7 => 1208925819614629174706176
  | 8 => 281474976710656
  | 9 => 72057594037927936
  | 10 => 4722366482869645213696
  | 11 => 20282409603651670423947251286016
  | 12 => 309485009821345068724781056
  | 13 => 79228162514264337593543950336
  | _ => 0

def C003_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 81446860549673560391231905726464
  | 1 => 81208870203898404877270073212928
  | 2 => 60926460600246734453322821926912
  | 3 => 4840425644941386344038400
  | 4 => 4835703278458516698824704
  | 5 => 72057594037927936
  | 6 => 1099511627776
  | 7 => 4294967296
  | 8 => 18446744073709551616
  | 9 => 16777216
  | 10 => 281474976710656
  | 11 => 256
  | 12 => 1
  | 13 => 65536
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
  | 0 => 1652488799756
  | 1 => 1112396628068
  | 2 => 1128502663168
  | 3 => 1657857476107
  | 4 => 1125281693696
  | 5 => 1666447312896
  | 6 => 1649401659392
  | 7 => 1099528404992
  | 8 => 21474836480
  | 9 => 17180000256
  | 10 => 627065225216
  | 11 => 2233385091072
  | 12 => 549755813888
  | 13 => 8589934592
  | _ => 0

def C004_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 50332676
  | 1 => 16778241
  | 2 => 256
  | 3 => 4398097104899
  | 4 => 65536
  | 5 => 18889465931478631187204
  | 6 => 4294967296
  | 7 => 309485009821345068724781056
  | 8 => 72057594037927936
  | 9 => 281474976710656
  | 10 => 73786976294838404099
  | 11 => 20283648762098401874949959778560
  | 12 => 1208925819614629174706176
  | 13 => 80467311479514295417799049731
  | _ => 0

def C004_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 81208870203972191853564961751043
  | 1 => 81446860549728900623453101555714
  | 2 => 4840425644941386394566658
  | 3 => 60926460600302074685543950647299
  | 4 => 72057594038124546
  | 5 => 4835703278458516698955779
  | 6 => 4294967299
  | 7 => 1099511627778
  | 8 => 67239936
  | 9 => 73786976294838337536
  | 10 => 65793
  | 11 => 281474976972804
  | 12 => 1
  | 13 => 65536
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
  | 0 => 26843660900
  | 1 => 1675038081691
  | 2 => 562641613017
  | 3 => 1666448359424
  | 4 => 575526766091
  | 5 => 21474836480
  | 6 => 1666447312896
  | 7 => 627065225216
  | 8 => 1649401659392
  | 9 => 1099528404992
  | 10 => 17180000256
  | 11 => 8589934592
  | 12 => 2233385091072
  | 13 => 549755813888
  | _ => 0

def C005_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 12884968196
  | 1 => 4295164676
  | 2 => 197121
  | 3 => 1125912791744769
  | 4 => 197636
  | 5 => 4835703278458529583923459
  | 6 => 17247175424
  | 7 => 79228162514264337593543950336
  | 8 => 4722366482869645213696
  | 9 => 18446744073709551616
  | 10 => 4398046773249
  | 11 => 317224552918590547457183122179
  | 12 => 72057594037927936
  | 13 => 20599322263208873874305159594752
  | _ => 0

def C005_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 81446861777544186169560806916096
  | 1 => 61085533496351395437723414364163
  | 2 => 20521022560446583325546302734337
  | 3 => 288230376151842819
  | 4 => 60926460600302362915920102490113
  | 5 => 67239936
  | 6 => 4835703278458516698955779
  | 7 => 65793
  | 8 => 4294967299
  | 9 => 1099511627778
  | 10 => 73786976294838337536
  | 11 => 65536
  | 12 => 281474976972804
  | 13 => 1
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
  | 0 => 2210985554532
  | 1 => 2477464360027
  | 2 => 723221853707
  | 3 => 551911686144
  | 4 => 1859125260505
  | 5 => 1273457803264
  | 6 => 2181038336
  | 7 => 1073741824
  | 8 => 67108864
  | 9 => 2199560126464
  | 10 => 551903313920
  | 11 => 2474974904320
  | 12 => 210453659648
  | 13 => 549755813888
  | _ => 0

def C006_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 4295164676
  | 1 => 12884968196
  | 2 => 1125912791744769
  | 3 => 197121
  | 4 => 4835703278458529583923459
  | 5 => 197636
  | 6 => 79228162514264337593543950336
  | 7 => 17247175424
  | 8 => 73787539261971694593
  | 9 => 18889465931491466019329
  | 10 => 317224552918590547457183122179
  | 11 => 4398046773249
  | 12 => 238922427582078395267439264768
  | 13 => 20283648771506241352541830972420
  | _ => 0

def C006_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 81446861772840266431868711272452
  | 1 => 61085225206155419166945560232964
  | 2 => 60926460614469174981893548147201
  | 3 => 1125899940397057
  | 4 => 20521022560391028050853881709315
  | 5 => 33817090
  | 6 => 1237940039285382473955934208
  | 7 => 16777216
  | 8 => 4398046511104
  | 9 => 17179869188
  | 10 => 18889465931478614409217
  | 11 => 16778244
  | 12 => 72057594105037568
  | 13 => 1
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

end SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryCaches00
