import SymmetricSubgroupAsymptotics.MatrixKroneckerProductReflection
import Mathlib.Tactic.FinCases

/-! Literal14/F5 selected caches; digit bounds and both pack bindings are independently kernel checked. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedCaches07
open MatrixKroneckerProductReflection MatrixKroneckerDotReflection
open MatrixNaturalRowDotReflection SmallNaturalMatrixProductReflection

def C064_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 1401290004481
  | 1 => 764691940866
  | 2 => 717326794752
  | 3 => 1309998841856
  | 4 => 1127502316032
  | 5 => 1786706411520
  | 6 => 6391307
  | 7 => 1099578736640
  | 8 => 2202278035456
  | 9 => 550846464064
  | 10 => 38654705664
  | 11 => 2474974904320
  | 12 => 1649292607488
  | 13 => 1653629517824
  | _ => 0

def C064_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 844424930132481
  | 1 => 281474976710656
  | 2 => 4722366482869645213696
  | 3 => 844429225100036
  | 4 => 4398046773249
  | 5 => 18889466775903511249409
  | 6 => 16778241
  | 7 => 316912650057058194811990835459
  | 8 => 81208866581880494234792978809603
  | 9 => 256
  | 10 => 81129952740097488214473859923969
  | 11 => 4835703278458529583923459
  | 12 => 1237940039285382473972843268
  | 13 => 61086151243333387242557002547458
  | _ => 0

def C064_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 20282414444095835014724824794114
  | 1 => 40564822834117981695083404133121
  | 2 => 18963252912171532878337
  | 3 => 72059793128293122
  | 4 => 1208925820463452185100290
  | 5 => 18889465931478580855299
  | 6 => 60926460600302075529968880713728
  | 7 => 4398046511106
  | 8 => 2199073587204
  | 9 => 309485083608322463091392513
  | 10 => 67371008
  | 11 => 16778244
  | 12 => 1126999418470403
  | 13 => 4398113619971
  | _ => 0

def C064_digit (i j : Fin 14) : ℕ := packedDigit 3 (C064_lowColumnCode j) i.val

private theorem C064_bound_00 : ∀ j : Fin 14, C064_digit 0 j < 5 := by decide +kernel

private theorem C064_bound_01 : ∀ j : Fin 14, C064_digit 1 j < 5 := by decide +kernel

private theorem C064_bound_02 : ∀ j : Fin 14, C064_digit 2 j < 5 := by decide +kernel

private theorem C064_bound_03 : ∀ j : Fin 14, C064_digit 3 j < 5 := by decide +kernel

private theorem C064_bound_04 : ∀ j : Fin 14, C064_digit 4 j < 5 := by decide +kernel

private theorem C064_bound_05 : ∀ j : Fin 14, C064_digit 5 j < 5 := by decide +kernel

private theorem C064_bound_06 : ∀ j : Fin 14, C064_digit 6 j < 5 := by decide +kernel

private theorem C064_bound_07 : ∀ j : Fin 14, C064_digit 7 j < 5 := by decide +kernel

private theorem C064_bound_08 : ∀ j : Fin 14, C064_digit 8 j < 5 := by decide +kernel

private theorem C064_bound_09 : ∀ j : Fin 14, C064_digit 9 j < 5 := by decide +kernel

private theorem C064_bound_10 : ∀ j : Fin 14, C064_digit 10 j < 5 := by decide +kernel

private theorem C064_bound_11 : ∀ j : Fin 14, C064_digit 11 j < 5 := by decide +kernel

private theorem C064_bound_12 : ∀ j : Fin 14, C064_digit 12 j < 5 := by decide +kernel

private theorem C064_bound_13 : ∀ j : Fin 14, C064_digit 13 j < 5 := by decide +kernel

theorem C064_bound : ∀ i j : Fin 14, C064_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C064_bound_00 j
  · exact C064_bound_01 j
  · exact C064_bound_02 j
  · exact C064_bound_03 j
  · exact C064_bound_04 j
  · exact C064_bound_05 j
  · exact C064_bound_06 j
  · exact C064_bound_07 j
  · exact C064_bound_08 j
  · exact C064_bound_09 j
  · exact C064_bound_10 j
  · exact C064_bound_11 j
  · exact C064_bound_12 j
  · exact C064_bound_13 j

private theorem C064_row_00 : pack 256 (C064_digit 0)=C064_rowCode 0 := by decide +kernel

private theorem C064_row_01 : pack 256 (C064_digit 1)=C064_rowCode 1 := by decide +kernel

private theorem C064_row_02 : pack 256 (C064_digit 2)=C064_rowCode 2 := by decide +kernel

private theorem C064_row_03 : pack 256 (C064_digit 3)=C064_rowCode 3 := by decide +kernel

private theorem C064_row_04 : pack 256 (C064_digit 4)=C064_rowCode 4 := by decide +kernel

private theorem C064_row_05 : pack 256 (C064_digit 5)=C064_rowCode 5 := by decide +kernel

private theorem C064_row_06 : pack 256 (C064_digit 6)=C064_rowCode 6 := by decide +kernel

private theorem C064_row_07 : pack 256 (C064_digit 7)=C064_rowCode 7 := by decide +kernel

private theorem C064_row_08 : pack 256 (C064_digit 8)=C064_rowCode 8 := by decide +kernel

private theorem C064_row_09 : pack 256 (C064_digit 9)=C064_rowCode 9 := by decide +kernel

private theorem C064_row_10 : pack 256 (C064_digit 10)=C064_rowCode 10 := by decide +kernel

private theorem C064_row_11 : pack 256 (C064_digit 11)=C064_rowCode 11 := by decide +kernel

private theorem C064_row_12 : pack 256 (C064_digit 12)=C064_rowCode 12 := by decide +kernel

private theorem C064_row_13 : pack 256 (C064_digit 13)=C064_rowCode 13 := by decide +kernel

theorem C064_row_binding : ∀ i : Fin 14, pack 256 (C064_digit i)=C064_rowCode i := by
  intro i
  fin_cases i
  · exact C064_row_00
  · exact C064_row_01
  · exact C064_row_02
  · exact C064_row_03
  · exact C064_row_04
  · exact C064_row_05
  · exact C064_row_06
  · exact C064_row_07
  · exact C064_row_08
  · exact C064_row_09
  · exact C064_row_10
  · exact C064_row_11
  · exact C064_row_12
  · exact C064_row_13

private theorem C064_column_00 : reversePack 256 (fun j : Fin 14 => C064_digit j 0)=C064_columnCode 0 := by decide +kernel

private theorem C064_column_01 : reversePack 256 (fun j : Fin 14 => C064_digit j 1)=C064_columnCode 1 := by decide +kernel

private theorem C064_column_02 : reversePack 256 (fun j : Fin 14 => C064_digit j 2)=C064_columnCode 2 := by decide +kernel

private theorem C064_column_03 : reversePack 256 (fun j : Fin 14 => C064_digit j 3)=C064_columnCode 3 := by decide +kernel

private theorem C064_column_04 : reversePack 256 (fun j : Fin 14 => C064_digit j 4)=C064_columnCode 4 := by decide +kernel

private theorem C064_column_05 : reversePack 256 (fun j : Fin 14 => C064_digit j 5)=C064_columnCode 5 := by decide +kernel

private theorem C064_column_06 : reversePack 256 (fun j : Fin 14 => C064_digit j 6)=C064_columnCode 6 := by decide +kernel

private theorem C064_column_07 : reversePack 256 (fun j : Fin 14 => C064_digit j 7)=C064_columnCode 7 := by decide +kernel

private theorem C064_column_08 : reversePack 256 (fun j : Fin 14 => C064_digit j 8)=C064_columnCode 8 := by decide +kernel

private theorem C064_column_09 : reversePack 256 (fun j : Fin 14 => C064_digit j 9)=C064_columnCode 9 := by decide +kernel

private theorem C064_column_10 : reversePack 256 (fun j : Fin 14 => C064_digit j 10)=C064_columnCode 10 := by decide +kernel

private theorem C064_column_11 : reversePack 256 (fun j : Fin 14 => C064_digit j 11)=C064_columnCode 11 := by decide +kernel

private theorem C064_column_12 : reversePack 256 (fun j : Fin 14 => C064_digit j 12)=C064_columnCode 12 := by decide +kernel

private theorem C064_column_13 : reversePack 256 (fun j : Fin 14 => C064_digit j 13)=C064_columnCode 13 := by decide +kernel

theorem C064_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C064_digit j i)=C064_columnCode i := by
  intro i
  fin_cases i
  · exact C064_column_00
  · exact C064_column_01
  · exact C064_column_02
  · exact C064_column_03
  · exact C064_column_04
  · exact C064_column_05
  · exact C064_column_06
  · exact C064_column_07
  · exact C064_column_08
  · exact C064_column_09
  · exact C064_column_10
  · exact C064_column_11
  · exact C064_column_12
  · exact C064_column_13

def C064_data : PackedData 14 5 256 where
  raw := C064_digit
  digit_lt := C064_bound
  rowCode := C064_rowCode
  columnCode := C064_columnCode
  row_binding := C064_row_binding
  column_binding := C064_column_binding

def C065_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 1198302173249
  | 1 => 1729821492738
  | 2 => 2201363710208
  | 3 => 1308912259072
  | 4 => 1125340282880
  | 5 => 2181071104
  | 6 => 1125281432064
  | 7 => 274886295552
  | 8 => 549793562624
  | 9 => 549791565323
  | 10 => 1099528404992
  | 11 => 1653629517824
  | 12 => 2233385091072
  | 13 => 1649292607488
  | _ => 0

def C065_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 14167099448608935641601
  | 1 => 4722366482869645213696
  | 2 => 4398046773249
  | 3 => 14167099730083912352516
  | 4 => 16778241
  | 5 => 14167099449725627204096
  | 6 => 256
  | 7 => 81208866581880494234792978809603
  | 8 => 20283648762098401874949959778560
  | 9 => 65536
  | 10 => 1237940039285382473972843268
  | 11 => 316912650057058194811990835459
  | 12 => 288230376202043649
  | 13 => 61165072338633985676582385353474
  | _ => 0

def C065_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 20282723929087137554827317543170
  | 1 => 40564822853007232014526556733699
  | 2 => 1237940057733253551378923524
  | 3 => 4722367046919160595202
  | 4 => 73788105493280129026
  | 5 => 1237940057732126547665485824
  | 6 => 1208925819614629174902786
  | 7 => 1125899906843648
  | 8 => 565148976676865
  | 9 => 60926460600302074969217950547969
  | 10 => 1099511627778
  | 11 => 4398113619971
  | 12 => 281474976972804
  | 13 => 1126999418470403
  | _ => 0

def C065_digit (i j : Fin 14) : ℕ := packedDigit 3 (C065_lowColumnCode j) i.val

private theorem C065_bound_00 : ∀ j : Fin 14, C065_digit 0 j < 5 := by decide +kernel

private theorem C065_bound_01 : ∀ j : Fin 14, C065_digit 1 j < 5 := by decide +kernel

private theorem C065_bound_02 : ∀ j : Fin 14, C065_digit 2 j < 5 := by decide +kernel

private theorem C065_bound_03 : ∀ j : Fin 14, C065_digit 3 j < 5 := by decide +kernel

private theorem C065_bound_04 : ∀ j : Fin 14, C065_digit 4 j < 5 := by decide +kernel

private theorem C065_bound_05 : ∀ j : Fin 14, C065_digit 5 j < 5 := by decide +kernel

private theorem C065_bound_06 : ∀ j : Fin 14, C065_digit 6 j < 5 := by decide +kernel

private theorem C065_bound_07 : ∀ j : Fin 14, C065_digit 7 j < 5 := by decide +kernel

private theorem C065_bound_08 : ∀ j : Fin 14, C065_digit 8 j < 5 := by decide +kernel

private theorem C065_bound_09 : ∀ j : Fin 14, C065_digit 9 j < 5 := by decide +kernel

private theorem C065_bound_10 : ∀ j : Fin 14, C065_digit 10 j < 5 := by decide +kernel

private theorem C065_bound_11 : ∀ j : Fin 14, C065_digit 11 j < 5 := by decide +kernel

private theorem C065_bound_12 : ∀ j : Fin 14, C065_digit 12 j < 5 := by decide +kernel

private theorem C065_bound_13 : ∀ j : Fin 14, C065_digit 13 j < 5 := by decide +kernel

theorem C065_bound : ∀ i j : Fin 14, C065_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C065_bound_00 j
  · exact C065_bound_01 j
  · exact C065_bound_02 j
  · exact C065_bound_03 j
  · exact C065_bound_04 j
  · exact C065_bound_05 j
  · exact C065_bound_06 j
  · exact C065_bound_07 j
  · exact C065_bound_08 j
  · exact C065_bound_09 j
  · exact C065_bound_10 j
  · exact C065_bound_11 j
  · exact C065_bound_12 j
  · exact C065_bound_13 j

private theorem C065_row_00 : pack 256 (C065_digit 0)=C065_rowCode 0 := by decide +kernel

private theorem C065_row_01 : pack 256 (C065_digit 1)=C065_rowCode 1 := by decide +kernel

private theorem C065_row_02 : pack 256 (C065_digit 2)=C065_rowCode 2 := by decide +kernel

private theorem C065_row_03 : pack 256 (C065_digit 3)=C065_rowCode 3 := by decide +kernel

private theorem C065_row_04 : pack 256 (C065_digit 4)=C065_rowCode 4 := by decide +kernel

private theorem C065_row_05 : pack 256 (C065_digit 5)=C065_rowCode 5 := by decide +kernel

private theorem C065_row_06 : pack 256 (C065_digit 6)=C065_rowCode 6 := by decide +kernel

private theorem C065_row_07 : pack 256 (C065_digit 7)=C065_rowCode 7 := by decide +kernel

private theorem C065_row_08 : pack 256 (C065_digit 8)=C065_rowCode 8 := by decide +kernel

private theorem C065_row_09 : pack 256 (C065_digit 9)=C065_rowCode 9 := by decide +kernel

private theorem C065_row_10 : pack 256 (C065_digit 10)=C065_rowCode 10 := by decide +kernel

private theorem C065_row_11 : pack 256 (C065_digit 11)=C065_rowCode 11 := by decide +kernel

private theorem C065_row_12 : pack 256 (C065_digit 12)=C065_rowCode 12 := by decide +kernel

private theorem C065_row_13 : pack 256 (C065_digit 13)=C065_rowCode 13 := by decide +kernel

theorem C065_row_binding : ∀ i : Fin 14, pack 256 (C065_digit i)=C065_rowCode i := by
  intro i
  fin_cases i
  · exact C065_row_00
  · exact C065_row_01
  · exact C065_row_02
  · exact C065_row_03
  · exact C065_row_04
  · exact C065_row_05
  · exact C065_row_06
  · exact C065_row_07
  · exact C065_row_08
  · exact C065_row_09
  · exact C065_row_10
  · exact C065_row_11
  · exact C065_row_12
  · exact C065_row_13

private theorem C065_column_00 : reversePack 256 (fun j : Fin 14 => C065_digit j 0)=C065_columnCode 0 := by decide +kernel

private theorem C065_column_01 : reversePack 256 (fun j : Fin 14 => C065_digit j 1)=C065_columnCode 1 := by decide +kernel

private theorem C065_column_02 : reversePack 256 (fun j : Fin 14 => C065_digit j 2)=C065_columnCode 2 := by decide +kernel

private theorem C065_column_03 : reversePack 256 (fun j : Fin 14 => C065_digit j 3)=C065_columnCode 3 := by decide +kernel

private theorem C065_column_04 : reversePack 256 (fun j : Fin 14 => C065_digit j 4)=C065_columnCode 4 := by decide +kernel

private theorem C065_column_05 : reversePack 256 (fun j : Fin 14 => C065_digit j 5)=C065_columnCode 5 := by decide +kernel

private theorem C065_column_06 : reversePack 256 (fun j : Fin 14 => C065_digit j 6)=C065_columnCode 6 := by decide +kernel

private theorem C065_column_07 : reversePack 256 (fun j : Fin 14 => C065_digit j 7)=C065_columnCode 7 := by decide +kernel

private theorem C065_column_08 : reversePack 256 (fun j : Fin 14 => C065_digit j 8)=C065_columnCode 8 := by decide +kernel

private theorem C065_column_09 : reversePack 256 (fun j : Fin 14 => C065_digit j 9)=C065_columnCode 9 := by decide +kernel

private theorem C065_column_10 : reversePack 256 (fun j : Fin 14 => C065_digit j 10)=C065_columnCode 10 := by decide +kernel

private theorem C065_column_11 : reversePack 256 (fun j : Fin 14 => C065_digit j 11)=C065_columnCode 11 := by decide +kernel

private theorem C065_column_12 : reversePack 256 (fun j : Fin 14 => C065_digit j 12)=C065_columnCode 12 := by decide +kernel

private theorem C065_column_13 : reversePack 256 (fun j : Fin 14 => C065_digit j 13)=C065_columnCode 13 := by decide +kernel

theorem C065_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C065_digit j i)=C065_columnCode i := by
  intro i
  fin_cases i
  · exact C065_column_00
  · exact C065_column_01
  · exact C065_column_02
  · exact C065_column_03
  · exact C065_column_04
  · exact C065_column_05
  · exact C065_column_06
  · exact C065_column_07
  · exact C065_column_08
  · exact C065_column_09
  · exact C065_column_10
  · exact C065_column_11
  · exact C065_column_12
  · exact C065_column_13

def C065_data : PackedData 14 5 256 where
  raw := C065_digit
  digit_lt := C065_bound
  rowCode := C065_rowCode
  columnCode := C065_columnCode
  row_binding := C065_row_binding
  column_binding := C065_column_binding

def C069_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 1881380241633
  | 1 => 1959763391012
  | 2 => 2502925779200
  | 3 => 1307213574361
  | 4 => 2202246578176
  | 5 => 2181038336
  | 6 => 67108864
  | 7 => 2199560126464
  | 8 => 1273457803264
  | 9 => 551903313920
  | 10 => 1073741824
  | 11 => 210453659648
  | 12 => 549755813888
  | 13 => 2474974904320
  | _ => 0

def C069_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 16778241
  | 1 => 50332676
  | 2 => 4398097104899
  | 3 => 256
  | 4 => 18889465931478631187204
  | 5 => 65536
  | 6 => 309485009821345068724781056
  | 7 => 4294967296
  | 8 => 1128098997338883
  | 9 => 288230376202043649
  | 10 => 20283648762098401874949959778560
  | 11 => 73786976294838404099
  | 12 => 81130566869673039219142649185283
  | 13 => 81208866581880494234792978809603
  | _ => 0

def C069_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 20600250727627657744309012333315
  | 1 => 81446552287756658112704138183683
  | 2 => 1237940057732126547682460676
  | 3 => 20521022560391026924953941312258
  | 4 => 281475027042308
  | 5 => 1237940039285382473955934208
  | 6 => 4398046511104
  | 7 => 17179869188
  | 8 => 33817090
  | 9 => 18889465931478614409217
  | 10 => 16777216
  | 11 => 72057594105037568
  | 12 => 1
  | 13 => 16778244
  | _ => 0

def C069_digit (i j : Fin 14) : ℕ := packedDigit 3 (C069_lowColumnCode j) i.val

private theorem C069_bound_00 : ∀ j : Fin 14, C069_digit 0 j < 5 := by decide +kernel

private theorem C069_bound_01 : ∀ j : Fin 14, C069_digit 1 j < 5 := by decide +kernel

private theorem C069_bound_02 : ∀ j : Fin 14, C069_digit 2 j < 5 := by decide +kernel

private theorem C069_bound_03 : ∀ j : Fin 14, C069_digit 3 j < 5 := by decide +kernel

private theorem C069_bound_04 : ∀ j : Fin 14, C069_digit 4 j < 5 := by decide +kernel

private theorem C069_bound_05 : ∀ j : Fin 14, C069_digit 5 j < 5 := by decide +kernel

private theorem C069_bound_06 : ∀ j : Fin 14, C069_digit 6 j < 5 := by decide +kernel

private theorem C069_bound_07 : ∀ j : Fin 14, C069_digit 7 j < 5 := by decide +kernel

private theorem C069_bound_08 : ∀ j : Fin 14, C069_digit 8 j < 5 := by decide +kernel

private theorem C069_bound_09 : ∀ j : Fin 14, C069_digit 9 j < 5 := by decide +kernel

private theorem C069_bound_10 : ∀ j : Fin 14, C069_digit 10 j < 5 := by decide +kernel

private theorem C069_bound_11 : ∀ j : Fin 14, C069_digit 11 j < 5 := by decide +kernel

private theorem C069_bound_12 : ∀ j : Fin 14, C069_digit 12 j < 5 := by decide +kernel

private theorem C069_bound_13 : ∀ j : Fin 14, C069_digit 13 j < 5 := by decide +kernel

theorem C069_bound : ∀ i j : Fin 14, C069_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C069_bound_00 j
  · exact C069_bound_01 j
  · exact C069_bound_02 j
  · exact C069_bound_03 j
  · exact C069_bound_04 j
  · exact C069_bound_05 j
  · exact C069_bound_06 j
  · exact C069_bound_07 j
  · exact C069_bound_08 j
  · exact C069_bound_09 j
  · exact C069_bound_10 j
  · exact C069_bound_11 j
  · exact C069_bound_12 j
  · exact C069_bound_13 j

private theorem C069_row_00 : pack 256 (C069_digit 0)=C069_rowCode 0 := by decide +kernel

private theorem C069_row_01 : pack 256 (C069_digit 1)=C069_rowCode 1 := by decide +kernel

private theorem C069_row_02 : pack 256 (C069_digit 2)=C069_rowCode 2 := by decide +kernel

private theorem C069_row_03 : pack 256 (C069_digit 3)=C069_rowCode 3 := by decide +kernel

private theorem C069_row_04 : pack 256 (C069_digit 4)=C069_rowCode 4 := by decide +kernel

private theorem C069_row_05 : pack 256 (C069_digit 5)=C069_rowCode 5 := by decide +kernel

private theorem C069_row_06 : pack 256 (C069_digit 6)=C069_rowCode 6 := by decide +kernel

private theorem C069_row_07 : pack 256 (C069_digit 7)=C069_rowCode 7 := by decide +kernel

private theorem C069_row_08 : pack 256 (C069_digit 8)=C069_rowCode 8 := by decide +kernel

private theorem C069_row_09 : pack 256 (C069_digit 9)=C069_rowCode 9 := by decide +kernel

private theorem C069_row_10 : pack 256 (C069_digit 10)=C069_rowCode 10 := by decide +kernel

private theorem C069_row_11 : pack 256 (C069_digit 11)=C069_rowCode 11 := by decide +kernel

private theorem C069_row_12 : pack 256 (C069_digit 12)=C069_rowCode 12 := by decide +kernel

private theorem C069_row_13 : pack 256 (C069_digit 13)=C069_rowCode 13 := by decide +kernel

theorem C069_row_binding : ∀ i : Fin 14, pack 256 (C069_digit i)=C069_rowCode i := by
  intro i
  fin_cases i
  · exact C069_row_00
  · exact C069_row_01
  · exact C069_row_02
  · exact C069_row_03
  · exact C069_row_04
  · exact C069_row_05
  · exact C069_row_06
  · exact C069_row_07
  · exact C069_row_08
  · exact C069_row_09
  · exact C069_row_10
  · exact C069_row_11
  · exact C069_row_12
  · exact C069_row_13

private theorem C069_column_00 : reversePack 256 (fun j : Fin 14 => C069_digit j 0)=C069_columnCode 0 := by decide +kernel

private theorem C069_column_01 : reversePack 256 (fun j : Fin 14 => C069_digit j 1)=C069_columnCode 1 := by decide +kernel

private theorem C069_column_02 : reversePack 256 (fun j : Fin 14 => C069_digit j 2)=C069_columnCode 2 := by decide +kernel

private theorem C069_column_03 : reversePack 256 (fun j : Fin 14 => C069_digit j 3)=C069_columnCode 3 := by decide +kernel

private theorem C069_column_04 : reversePack 256 (fun j : Fin 14 => C069_digit j 4)=C069_columnCode 4 := by decide +kernel

private theorem C069_column_05 : reversePack 256 (fun j : Fin 14 => C069_digit j 5)=C069_columnCode 5 := by decide +kernel

private theorem C069_column_06 : reversePack 256 (fun j : Fin 14 => C069_digit j 6)=C069_columnCode 6 := by decide +kernel

private theorem C069_column_07 : reversePack 256 (fun j : Fin 14 => C069_digit j 7)=C069_columnCode 7 := by decide +kernel

private theorem C069_column_08 : reversePack 256 (fun j : Fin 14 => C069_digit j 8)=C069_columnCode 8 := by decide +kernel

private theorem C069_column_09 : reversePack 256 (fun j : Fin 14 => C069_digit j 9)=C069_columnCode 9 := by decide +kernel

private theorem C069_column_10 : reversePack 256 (fun j : Fin 14 => C069_digit j 10)=C069_columnCode 10 := by decide +kernel

private theorem C069_column_11 : reversePack 256 (fun j : Fin 14 => C069_digit j 11)=C069_columnCode 11 := by decide +kernel

private theorem C069_column_12 : reversePack 256 (fun j : Fin 14 => C069_digit j 12)=C069_columnCode 12 := by decide +kernel

private theorem C069_column_13 : reversePack 256 (fun j : Fin 14 => C069_digit j 13)=C069_columnCode 13 := by decide +kernel

theorem C069_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C069_digit j i)=C069_columnCode i := by
  intro i
  fin_cases i
  · exact C069_column_00
  · exact C069_column_01
  · exact C069_column_02
  · exact C069_column_03
  · exact C069_column_04
  · exact C069_column_05
  · exact C069_column_06
  · exact C069_column_07
  · exact C069_column_08
  · exact C069_column_09
  · exact C069_column_10
  · exact C069_column_11
  · exact C069_column_12
  · exact C069_column_13

def C069_data : PackedData 14 5 256 where
  raw := C069_digit
  digit_lt := C069_bound
  rowCode := C069_rowCode
  columnCode := C069_columnCode
  row_binding := C069_row_binding
  column_binding := C069_column_binding

def C070_lowColumnCode (i : Fin 14) : ℕ :=
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

def C070_rowCode (i : Fin 14) : ℕ :=
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

def C070_columnCode (i : Fin 14) : ℕ :=
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

def C070_digit (i j : Fin 14) : ℕ := packedDigit 3 (C070_lowColumnCode j) i.val

private theorem C070_bound_00 : ∀ j : Fin 14, C070_digit 0 j < 5 := by decide +kernel

private theorem C070_bound_01 : ∀ j : Fin 14, C070_digit 1 j < 5 := by decide +kernel

private theorem C070_bound_02 : ∀ j : Fin 14, C070_digit 2 j < 5 := by decide +kernel

private theorem C070_bound_03 : ∀ j : Fin 14, C070_digit 3 j < 5 := by decide +kernel

private theorem C070_bound_04 : ∀ j : Fin 14, C070_digit 4 j < 5 := by decide +kernel

private theorem C070_bound_05 : ∀ j : Fin 14, C070_digit 5 j < 5 := by decide +kernel

private theorem C070_bound_06 : ∀ j : Fin 14, C070_digit 6 j < 5 := by decide +kernel

private theorem C070_bound_07 : ∀ j : Fin 14, C070_digit 7 j < 5 := by decide +kernel

private theorem C070_bound_08 : ∀ j : Fin 14, C070_digit 8 j < 5 := by decide +kernel

private theorem C070_bound_09 : ∀ j : Fin 14, C070_digit 9 j < 5 := by decide +kernel

private theorem C070_bound_10 : ∀ j : Fin 14, C070_digit 10 j < 5 := by decide +kernel

private theorem C070_bound_11 : ∀ j : Fin 14, C070_digit 11 j < 5 := by decide +kernel

private theorem C070_bound_12 : ∀ j : Fin 14, C070_digit 12 j < 5 := by decide +kernel

private theorem C070_bound_13 : ∀ j : Fin 14, C070_digit 13 j < 5 := by decide +kernel

theorem C070_bound : ∀ i j : Fin 14, C070_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C070_bound_00 j
  · exact C070_bound_01 j
  · exact C070_bound_02 j
  · exact C070_bound_03 j
  · exact C070_bound_04 j
  · exact C070_bound_05 j
  · exact C070_bound_06 j
  · exact C070_bound_07 j
  · exact C070_bound_08 j
  · exact C070_bound_09 j
  · exact C070_bound_10 j
  · exact C070_bound_11 j
  · exact C070_bound_12 j
  · exact C070_bound_13 j

private theorem C070_row_00 : pack 256 (C070_digit 0)=C070_rowCode 0 := by decide +kernel

private theorem C070_row_01 : pack 256 (C070_digit 1)=C070_rowCode 1 := by decide +kernel

private theorem C070_row_02 : pack 256 (C070_digit 2)=C070_rowCode 2 := by decide +kernel

private theorem C070_row_03 : pack 256 (C070_digit 3)=C070_rowCode 3 := by decide +kernel

private theorem C070_row_04 : pack 256 (C070_digit 4)=C070_rowCode 4 := by decide +kernel

private theorem C070_row_05 : pack 256 (C070_digit 5)=C070_rowCode 5 := by decide +kernel

private theorem C070_row_06 : pack 256 (C070_digit 6)=C070_rowCode 6 := by decide +kernel

private theorem C070_row_07 : pack 256 (C070_digit 7)=C070_rowCode 7 := by decide +kernel

private theorem C070_row_08 : pack 256 (C070_digit 8)=C070_rowCode 8 := by decide +kernel

private theorem C070_row_09 : pack 256 (C070_digit 9)=C070_rowCode 9 := by decide +kernel

private theorem C070_row_10 : pack 256 (C070_digit 10)=C070_rowCode 10 := by decide +kernel

private theorem C070_row_11 : pack 256 (C070_digit 11)=C070_rowCode 11 := by decide +kernel

private theorem C070_row_12 : pack 256 (C070_digit 12)=C070_rowCode 12 := by decide +kernel

private theorem C070_row_13 : pack 256 (C070_digit 13)=C070_rowCode 13 := by decide +kernel

theorem C070_row_binding : ∀ i : Fin 14, pack 256 (C070_digit i)=C070_rowCode i := by
  intro i
  fin_cases i
  · exact C070_row_00
  · exact C070_row_01
  · exact C070_row_02
  · exact C070_row_03
  · exact C070_row_04
  · exact C070_row_05
  · exact C070_row_06
  · exact C070_row_07
  · exact C070_row_08
  · exact C070_row_09
  · exact C070_row_10
  · exact C070_row_11
  · exact C070_row_12
  · exact C070_row_13

private theorem C070_column_00 : reversePack 256 (fun j : Fin 14 => C070_digit j 0)=C070_columnCode 0 := by decide +kernel

private theorem C070_column_01 : reversePack 256 (fun j : Fin 14 => C070_digit j 1)=C070_columnCode 1 := by decide +kernel

private theorem C070_column_02 : reversePack 256 (fun j : Fin 14 => C070_digit j 2)=C070_columnCode 2 := by decide +kernel

private theorem C070_column_03 : reversePack 256 (fun j : Fin 14 => C070_digit j 3)=C070_columnCode 3 := by decide +kernel

private theorem C070_column_04 : reversePack 256 (fun j : Fin 14 => C070_digit j 4)=C070_columnCode 4 := by decide +kernel

private theorem C070_column_05 : reversePack 256 (fun j : Fin 14 => C070_digit j 5)=C070_columnCode 5 := by decide +kernel

private theorem C070_column_06 : reversePack 256 (fun j : Fin 14 => C070_digit j 6)=C070_columnCode 6 := by decide +kernel

private theorem C070_column_07 : reversePack 256 (fun j : Fin 14 => C070_digit j 7)=C070_columnCode 7 := by decide +kernel

private theorem C070_column_08 : reversePack 256 (fun j : Fin 14 => C070_digit j 8)=C070_columnCode 8 := by decide +kernel

private theorem C070_column_09 : reversePack 256 (fun j : Fin 14 => C070_digit j 9)=C070_columnCode 9 := by decide +kernel

private theorem C070_column_10 : reversePack 256 (fun j : Fin 14 => C070_digit j 10)=C070_columnCode 10 := by decide +kernel

private theorem C070_column_11 : reversePack 256 (fun j : Fin 14 => C070_digit j 11)=C070_columnCode 11 := by decide +kernel

private theorem C070_column_12 : reversePack 256 (fun j : Fin 14 => C070_digit j 12)=C070_columnCode 12 := by decide +kernel

private theorem C070_column_13 : reversePack 256 (fun j : Fin 14 => C070_digit j 13)=C070_columnCode 13 := by decide +kernel

theorem C070_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C070_digit j i)=C070_columnCode i := by
  intro i
  fin_cases i
  · exact C070_column_00
  · exact C070_column_01
  · exact C070_column_02
  · exact C070_column_03
  · exact C070_column_04
  · exact C070_column_05
  · exact C070_column_06
  · exact C070_column_07
  · exact C070_column_08
  · exact C070_column_09
  · exact C070_column_10
  · exact C070_column_11
  · exact C070_column_12
  · exact C070_column_13

def C070_data : PackedData 14 5 256 where
  raw := C070_digit
  digit_lt := C070_bound
  rowCode := C070_rowCode
  columnCode := C070_columnCode
  row_binding := C070_row_binding
  column_binding := C070_column_binding

def C073_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 209405708290
  | 1 => 620814665729
  | 2 => 2148401152
  | 3 => 1859240691211
  | 4 => 71403831296
  | 5 => 3271688256
  | 6 => 1867237031936
  | 7 => 70866964480
  | 8 => 1048576
  | 9 => 274886295552
  | 10 => 1073741824
  | 11 => 1653629517824
  | 12 => 2474974904320
  | 13 => 68719476736
  | _ => 0

def C073_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 50331906
  | 1 => 16777216
  | 2 => 1099511627776
  | 3 => 50332676
  | 4 => 72057594037927936
  | 5 => 4398097104899
  | 6 => 73786976294838404099
  | 7 => 18889465931478631187204
  | 8 => 1237940039285383573484339969
  | 9 => 17246978304
  | 10 => 80467311479514295417799049731
  | 11 => 281474976710656
  | 12 => 20599322272598266607823321301251
  | 13 => 317841105086522230005330608384
  | _ => 0

def C073_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 40564824043062176838413912638208
  | 1 => 20282414439355237960567895359745
  | 2 => 74003149076985544704
  | 3 => 60926460600302075533284645798659
  | 4 => 17213423872
  | 5 => 309485083608324662148202496
  | 6 => 50397955
  | 7 => 4722366482869678768384
  | 8 => 288230376151711744
  | 9 => 1125899906843648
  | 10 => 16777216
  | 11 => 4398113619971
  | 12 => 16778244
  | 13 => 256
  | _ => 0

def C073_digit (i j : Fin 14) : ℕ := packedDigit 3 (C073_lowColumnCode j) i.val

private theorem C073_bound_00 : ∀ j : Fin 14, C073_digit 0 j < 5 := by decide +kernel

private theorem C073_bound_01 : ∀ j : Fin 14, C073_digit 1 j < 5 := by decide +kernel

private theorem C073_bound_02 : ∀ j : Fin 14, C073_digit 2 j < 5 := by decide +kernel

private theorem C073_bound_03 : ∀ j : Fin 14, C073_digit 3 j < 5 := by decide +kernel

private theorem C073_bound_04 : ∀ j : Fin 14, C073_digit 4 j < 5 := by decide +kernel

private theorem C073_bound_05 : ∀ j : Fin 14, C073_digit 5 j < 5 := by decide +kernel

private theorem C073_bound_06 : ∀ j : Fin 14, C073_digit 6 j < 5 := by decide +kernel

private theorem C073_bound_07 : ∀ j : Fin 14, C073_digit 7 j < 5 := by decide +kernel

private theorem C073_bound_08 : ∀ j : Fin 14, C073_digit 8 j < 5 := by decide +kernel

private theorem C073_bound_09 : ∀ j : Fin 14, C073_digit 9 j < 5 := by decide +kernel

private theorem C073_bound_10 : ∀ j : Fin 14, C073_digit 10 j < 5 := by decide +kernel

private theorem C073_bound_11 : ∀ j : Fin 14, C073_digit 11 j < 5 := by decide +kernel

private theorem C073_bound_12 : ∀ j : Fin 14, C073_digit 12 j < 5 := by decide +kernel

private theorem C073_bound_13 : ∀ j : Fin 14, C073_digit 13 j < 5 := by decide +kernel

theorem C073_bound : ∀ i j : Fin 14, C073_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C073_bound_00 j
  · exact C073_bound_01 j
  · exact C073_bound_02 j
  · exact C073_bound_03 j
  · exact C073_bound_04 j
  · exact C073_bound_05 j
  · exact C073_bound_06 j
  · exact C073_bound_07 j
  · exact C073_bound_08 j
  · exact C073_bound_09 j
  · exact C073_bound_10 j
  · exact C073_bound_11 j
  · exact C073_bound_12 j
  · exact C073_bound_13 j

private theorem C073_row_00 : pack 256 (C073_digit 0)=C073_rowCode 0 := by decide +kernel

private theorem C073_row_01 : pack 256 (C073_digit 1)=C073_rowCode 1 := by decide +kernel

private theorem C073_row_02 : pack 256 (C073_digit 2)=C073_rowCode 2 := by decide +kernel

private theorem C073_row_03 : pack 256 (C073_digit 3)=C073_rowCode 3 := by decide +kernel

private theorem C073_row_04 : pack 256 (C073_digit 4)=C073_rowCode 4 := by decide +kernel

private theorem C073_row_05 : pack 256 (C073_digit 5)=C073_rowCode 5 := by decide +kernel

private theorem C073_row_06 : pack 256 (C073_digit 6)=C073_rowCode 6 := by decide +kernel

private theorem C073_row_07 : pack 256 (C073_digit 7)=C073_rowCode 7 := by decide +kernel

private theorem C073_row_08 : pack 256 (C073_digit 8)=C073_rowCode 8 := by decide +kernel

private theorem C073_row_09 : pack 256 (C073_digit 9)=C073_rowCode 9 := by decide +kernel

private theorem C073_row_10 : pack 256 (C073_digit 10)=C073_rowCode 10 := by decide +kernel

private theorem C073_row_11 : pack 256 (C073_digit 11)=C073_rowCode 11 := by decide +kernel

private theorem C073_row_12 : pack 256 (C073_digit 12)=C073_rowCode 12 := by decide +kernel

private theorem C073_row_13 : pack 256 (C073_digit 13)=C073_rowCode 13 := by decide +kernel

theorem C073_row_binding : ∀ i : Fin 14, pack 256 (C073_digit i)=C073_rowCode i := by
  intro i
  fin_cases i
  · exact C073_row_00
  · exact C073_row_01
  · exact C073_row_02
  · exact C073_row_03
  · exact C073_row_04
  · exact C073_row_05
  · exact C073_row_06
  · exact C073_row_07
  · exact C073_row_08
  · exact C073_row_09
  · exact C073_row_10
  · exact C073_row_11
  · exact C073_row_12
  · exact C073_row_13

private theorem C073_column_00 : reversePack 256 (fun j : Fin 14 => C073_digit j 0)=C073_columnCode 0 := by decide +kernel

private theorem C073_column_01 : reversePack 256 (fun j : Fin 14 => C073_digit j 1)=C073_columnCode 1 := by decide +kernel

private theorem C073_column_02 : reversePack 256 (fun j : Fin 14 => C073_digit j 2)=C073_columnCode 2 := by decide +kernel

private theorem C073_column_03 : reversePack 256 (fun j : Fin 14 => C073_digit j 3)=C073_columnCode 3 := by decide +kernel

private theorem C073_column_04 : reversePack 256 (fun j : Fin 14 => C073_digit j 4)=C073_columnCode 4 := by decide +kernel

private theorem C073_column_05 : reversePack 256 (fun j : Fin 14 => C073_digit j 5)=C073_columnCode 5 := by decide +kernel

private theorem C073_column_06 : reversePack 256 (fun j : Fin 14 => C073_digit j 6)=C073_columnCode 6 := by decide +kernel

private theorem C073_column_07 : reversePack 256 (fun j : Fin 14 => C073_digit j 7)=C073_columnCode 7 := by decide +kernel

private theorem C073_column_08 : reversePack 256 (fun j : Fin 14 => C073_digit j 8)=C073_columnCode 8 := by decide +kernel

private theorem C073_column_09 : reversePack 256 (fun j : Fin 14 => C073_digit j 9)=C073_columnCode 9 := by decide +kernel

private theorem C073_column_10 : reversePack 256 (fun j : Fin 14 => C073_digit j 10)=C073_columnCode 10 := by decide +kernel

private theorem C073_column_11 : reversePack 256 (fun j : Fin 14 => C073_digit j 11)=C073_columnCode 11 := by decide +kernel

private theorem C073_column_12 : reversePack 256 (fun j : Fin 14 => C073_digit j 12)=C073_columnCode 12 := by decide +kernel

private theorem C073_column_13 : reversePack 256 (fun j : Fin 14 => C073_digit j 13)=C073_columnCode 13 := by decide +kernel

theorem C073_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C073_digit j i)=C073_columnCode i := by
  intro i
  fin_cases i
  · exact C073_column_00
  · exact C073_column_01
  · exact C073_column_02
  · exact C073_column_03
  · exact C073_column_04
  · exact C073_column_05
  · exact C073_column_06
  · exact C073_column_07
  · exact C073_column_08
  · exact C073_column_09
  · exact C073_column_10
  · exact C073_column_11
  · exact C073_column_12
  · exact C073_column_13

def C073_data : PackedData 14 5 256 where
  raw := C073_digit
  digit_lt := C073_bound
  rowCode := C073_rowCode
  columnCode := C073_columnCode
  row_binding := C073_row_binding
  column_binding := C073_column_binding

def C075_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 1687437751810
  | 1 => 233159575553
  | 2 => 1924329910272
  | 3 => 166470877696
  | 4 => 1787831517184
  | 5 => 6391307
  | 6 => 2202278035456
  | 7 => 550846464064
  | 8 => 1786706411520
  | 9 => 38654705664
  | 10 => 1099578736640
  | 11 => 1649292607488
  | 12 => 1653629517824
  | 13 => 2474974904320
  | _ => 0

def C075_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 3298534883586
  | 1 => 1099511627776
  | 2 => 72057594037927936
  | 3 => 3298551661571
  | 4 => 73786976294838404099
  | 5 => 288233674686595329
  | 6 => 17246978304
  | 7 => 1237940039285383573484339969
  | 8 => 317226970770229774516509409539
  | 9 => 65796
  | 10 => 20599322272598266607823321301251
  | 11 => 18889465931478631187204
  | 12 => 81129638414643575183945047999232
  | 13 => 81368253775085991388762119274499
  | _ => 0

def C075_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 40564822848266346169255413940227
  | 1 => 20282414458262934461139032146688
  | 2 => 14167099451911765492739
  | 3 => 1208926108691629330334208
  | 4 => 288233674703372803
  | 5 => 60926460600302075529968880713728
  | 6 => 2199073587204
  | 7 => 309485083608322463091392513
  | 8 => 18889465931478580855299
  | 9 => 67371008
  | 10 => 4398046511106
  | 11 => 1126999418470403
  | 12 => 4398113619971
  | 13 => 16778244
  | _ => 0

def C075_digit (i j : Fin 14) : ℕ := packedDigit 3 (C075_lowColumnCode j) i.val

private theorem C075_bound_00 : ∀ j : Fin 14, C075_digit 0 j < 5 := by decide +kernel

private theorem C075_bound_01 : ∀ j : Fin 14, C075_digit 1 j < 5 := by decide +kernel

private theorem C075_bound_02 : ∀ j : Fin 14, C075_digit 2 j < 5 := by decide +kernel

private theorem C075_bound_03 : ∀ j : Fin 14, C075_digit 3 j < 5 := by decide +kernel

private theorem C075_bound_04 : ∀ j : Fin 14, C075_digit 4 j < 5 := by decide +kernel

private theorem C075_bound_05 : ∀ j : Fin 14, C075_digit 5 j < 5 := by decide +kernel

private theorem C075_bound_06 : ∀ j : Fin 14, C075_digit 6 j < 5 := by decide +kernel

private theorem C075_bound_07 : ∀ j : Fin 14, C075_digit 7 j < 5 := by decide +kernel

private theorem C075_bound_08 : ∀ j : Fin 14, C075_digit 8 j < 5 := by decide +kernel

private theorem C075_bound_09 : ∀ j : Fin 14, C075_digit 9 j < 5 := by decide +kernel

private theorem C075_bound_10 : ∀ j : Fin 14, C075_digit 10 j < 5 := by decide +kernel

private theorem C075_bound_11 : ∀ j : Fin 14, C075_digit 11 j < 5 := by decide +kernel

private theorem C075_bound_12 : ∀ j : Fin 14, C075_digit 12 j < 5 := by decide +kernel

private theorem C075_bound_13 : ∀ j : Fin 14, C075_digit 13 j < 5 := by decide +kernel

theorem C075_bound : ∀ i j : Fin 14, C075_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C075_bound_00 j
  · exact C075_bound_01 j
  · exact C075_bound_02 j
  · exact C075_bound_03 j
  · exact C075_bound_04 j
  · exact C075_bound_05 j
  · exact C075_bound_06 j
  · exact C075_bound_07 j
  · exact C075_bound_08 j
  · exact C075_bound_09 j
  · exact C075_bound_10 j
  · exact C075_bound_11 j
  · exact C075_bound_12 j
  · exact C075_bound_13 j

private theorem C075_row_00 : pack 256 (C075_digit 0)=C075_rowCode 0 := by decide +kernel

private theorem C075_row_01 : pack 256 (C075_digit 1)=C075_rowCode 1 := by decide +kernel

private theorem C075_row_02 : pack 256 (C075_digit 2)=C075_rowCode 2 := by decide +kernel

private theorem C075_row_03 : pack 256 (C075_digit 3)=C075_rowCode 3 := by decide +kernel

private theorem C075_row_04 : pack 256 (C075_digit 4)=C075_rowCode 4 := by decide +kernel

private theorem C075_row_05 : pack 256 (C075_digit 5)=C075_rowCode 5 := by decide +kernel

private theorem C075_row_06 : pack 256 (C075_digit 6)=C075_rowCode 6 := by decide +kernel

private theorem C075_row_07 : pack 256 (C075_digit 7)=C075_rowCode 7 := by decide +kernel

private theorem C075_row_08 : pack 256 (C075_digit 8)=C075_rowCode 8 := by decide +kernel

private theorem C075_row_09 : pack 256 (C075_digit 9)=C075_rowCode 9 := by decide +kernel

private theorem C075_row_10 : pack 256 (C075_digit 10)=C075_rowCode 10 := by decide +kernel

private theorem C075_row_11 : pack 256 (C075_digit 11)=C075_rowCode 11 := by decide +kernel

private theorem C075_row_12 : pack 256 (C075_digit 12)=C075_rowCode 12 := by decide +kernel

private theorem C075_row_13 : pack 256 (C075_digit 13)=C075_rowCode 13 := by decide +kernel

theorem C075_row_binding : ∀ i : Fin 14, pack 256 (C075_digit i)=C075_rowCode i := by
  intro i
  fin_cases i
  · exact C075_row_00
  · exact C075_row_01
  · exact C075_row_02
  · exact C075_row_03
  · exact C075_row_04
  · exact C075_row_05
  · exact C075_row_06
  · exact C075_row_07
  · exact C075_row_08
  · exact C075_row_09
  · exact C075_row_10
  · exact C075_row_11
  · exact C075_row_12
  · exact C075_row_13

private theorem C075_column_00 : reversePack 256 (fun j : Fin 14 => C075_digit j 0)=C075_columnCode 0 := by decide +kernel

private theorem C075_column_01 : reversePack 256 (fun j : Fin 14 => C075_digit j 1)=C075_columnCode 1 := by decide +kernel

private theorem C075_column_02 : reversePack 256 (fun j : Fin 14 => C075_digit j 2)=C075_columnCode 2 := by decide +kernel

private theorem C075_column_03 : reversePack 256 (fun j : Fin 14 => C075_digit j 3)=C075_columnCode 3 := by decide +kernel

private theorem C075_column_04 : reversePack 256 (fun j : Fin 14 => C075_digit j 4)=C075_columnCode 4 := by decide +kernel

private theorem C075_column_05 : reversePack 256 (fun j : Fin 14 => C075_digit j 5)=C075_columnCode 5 := by decide +kernel

private theorem C075_column_06 : reversePack 256 (fun j : Fin 14 => C075_digit j 6)=C075_columnCode 6 := by decide +kernel

private theorem C075_column_07 : reversePack 256 (fun j : Fin 14 => C075_digit j 7)=C075_columnCode 7 := by decide +kernel

private theorem C075_column_08 : reversePack 256 (fun j : Fin 14 => C075_digit j 8)=C075_columnCode 8 := by decide +kernel

private theorem C075_column_09 : reversePack 256 (fun j : Fin 14 => C075_digit j 9)=C075_columnCode 9 := by decide +kernel

private theorem C075_column_10 : reversePack 256 (fun j : Fin 14 => C075_digit j 10)=C075_columnCode 10 := by decide +kernel

private theorem C075_column_11 : reversePack 256 (fun j : Fin 14 => C075_digit j 11)=C075_columnCode 11 := by decide +kernel

private theorem C075_column_12 : reversePack 256 (fun j : Fin 14 => C075_digit j 12)=C075_columnCode 12 := by decide +kernel

private theorem C075_column_13 : reversePack 256 (fun j : Fin 14 => C075_digit j 13)=C075_columnCode 13 := by decide +kernel

theorem C075_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C075_digit j i)=C075_columnCode i := by
  intro i
  fin_cases i
  · exact C075_column_00
  · exact C075_column_01
  · exact C075_column_02
  · exact C075_column_03
  · exact C075_column_04
  · exact C075_column_05
  · exact C075_column_06
  · exact C075_column_07
  · exact C075_column_08
  · exact C075_column_09
  · exact C075_column_10
  · exact C075_column_11
  · exact C075_column_12
  · exact C075_column_13

def C075_data : PackedData 14 5 256 where
  raw := C075_digit
  digit_lt := C075_bound
  rowCode := C075_rowCode
  columnCode := C075_columnCode
  row_binding := C075_row_binding
  column_binding := C075_column_binding

end SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedCaches07
