import SymmetricSubgroupAsymptotics.MatrixKroneckerProductReflection
import Mathlib.Tactic.FinCases

/-! Literal14/F5 selected caches; digit bounds and both pack bindings are independently kernel checked. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryCaches02
open MatrixKroneckerProductReflection MatrixKroneckerDotReflection
open MatrixNaturalRowDotReflection SmallNaturalMatrixProductReflection

def C011_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 2375187272283
  | 1 => 277065834650
  | 2 => 827201259616
  | 3 => 2203586725568
  | 4 => 2345344845324
  | 5 => 4603281628
  | 6 => 1670797951499
  | 7 => 1101795460352
  | 8 => 131072
  | 9 => 38654705664
  | 10 => 1791305532625
  | 11 => 1651591217931
  | 12 => 1748259840736
  | 13 => 8589934592
  | _ => 0

def C011_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 929663955284498675505562115
  | 1 => 317224552918518209479056818947
  | 2 => 238926054359825470617792086529
  | 3 => 79540065375869308596606205953
  | 4 => 158461160731807133720966595073
  | 5 => 1240357964784488963780051459
  | 6 => 158456325028529801104174744068
  | 7 => 238923636507970631540116816641
  | 8 => 317534037928340116398223196676
  | 9 => 79540065375796971722303012864
  | 10 => 317536474669589675993001492996
  | 11 => 20520094110083929931160712380420
  | 12 => 79230580365903566860483560450
  | 13 => 238616569349860851504583344132
  | _ => 0

def C011_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 61085223997211440475660301369860
  | 1 => 40803122674347547966511356314624
  | 2 => 317226970825641502481234002945
  | 3 => 932081843816367249774608388
  | 4 => 81208870222861946860952675746308
  | 5 => 81368251357197386334482131320832
  | 6 => 60926458182450724252910308425731
  | 7 => 1240357909371635086263320578
  | 8 => 73786976294838206464
  | 9 => 67371008
  | 10 => 20441796820487662066907519910403
  | 11 => 60927696122508168708737468465155
  | 12 => 317842323457218929964230050051
  | 13 => 65536
  | _ => 0

def C011_digit (i j : Fin 14) : ℕ := packedDigit 3 (C011_lowColumnCode j) i.val

private theorem C011_bound_00 : ∀ j : Fin 14, C011_digit 0 j < 5 := by decide +kernel

private theorem C011_bound_01 : ∀ j : Fin 14, C011_digit 1 j < 5 := by decide +kernel

private theorem C011_bound_02 : ∀ j : Fin 14, C011_digit 2 j < 5 := by decide +kernel

private theorem C011_bound_03 : ∀ j : Fin 14, C011_digit 3 j < 5 := by decide +kernel

private theorem C011_bound_04 : ∀ j : Fin 14, C011_digit 4 j < 5 := by decide +kernel

private theorem C011_bound_05 : ∀ j : Fin 14, C011_digit 5 j < 5 := by decide +kernel

private theorem C011_bound_06 : ∀ j : Fin 14, C011_digit 6 j < 5 := by decide +kernel

private theorem C011_bound_07 : ∀ j : Fin 14, C011_digit 7 j < 5 := by decide +kernel

private theorem C011_bound_08 : ∀ j : Fin 14, C011_digit 8 j < 5 := by decide +kernel

private theorem C011_bound_09 : ∀ j : Fin 14, C011_digit 9 j < 5 := by decide +kernel

private theorem C011_bound_10 : ∀ j : Fin 14, C011_digit 10 j < 5 := by decide +kernel

private theorem C011_bound_11 : ∀ j : Fin 14, C011_digit 11 j < 5 := by decide +kernel

private theorem C011_bound_12 : ∀ j : Fin 14, C011_digit 12 j < 5 := by decide +kernel

private theorem C011_bound_13 : ∀ j : Fin 14, C011_digit 13 j < 5 := by decide +kernel

theorem C011_bound : ∀ i j : Fin 14, C011_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C011_bound_00 j
  · exact C011_bound_01 j
  · exact C011_bound_02 j
  · exact C011_bound_03 j
  · exact C011_bound_04 j
  · exact C011_bound_05 j
  · exact C011_bound_06 j
  · exact C011_bound_07 j
  · exact C011_bound_08 j
  · exact C011_bound_09 j
  · exact C011_bound_10 j
  · exact C011_bound_11 j
  · exact C011_bound_12 j
  · exact C011_bound_13 j

private theorem C011_row_00 : pack 256 (C011_digit 0)=C011_rowCode 0 := by decide +kernel

private theorem C011_row_01 : pack 256 (C011_digit 1)=C011_rowCode 1 := by decide +kernel

private theorem C011_row_02 : pack 256 (C011_digit 2)=C011_rowCode 2 := by decide +kernel

private theorem C011_row_03 : pack 256 (C011_digit 3)=C011_rowCode 3 := by decide +kernel

private theorem C011_row_04 : pack 256 (C011_digit 4)=C011_rowCode 4 := by decide +kernel

private theorem C011_row_05 : pack 256 (C011_digit 5)=C011_rowCode 5 := by decide +kernel

private theorem C011_row_06 : pack 256 (C011_digit 6)=C011_rowCode 6 := by decide +kernel

private theorem C011_row_07 : pack 256 (C011_digit 7)=C011_rowCode 7 := by decide +kernel

private theorem C011_row_08 : pack 256 (C011_digit 8)=C011_rowCode 8 := by decide +kernel

private theorem C011_row_09 : pack 256 (C011_digit 9)=C011_rowCode 9 := by decide +kernel

private theorem C011_row_10 : pack 256 (C011_digit 10)=C011_rowCode 10 := by decide +kernel

private theorem C011_row_11 : pack 256 (C011_digit 11)=C011_rowCode 11 := by decide +kernel

private theorem C011_row_12 : pack 256 (C011_digit 12)=C011_rowCode 12 := by decide +kernel

private theorem C011_row_13 : pack 256 (C011_digit 13)=C011_rowCode 13 := by decide +kernel

theorem C011_row_binding : ∀ i : Fin 14, pack 256 (C011_digit i)=C011_rowCode i := by
  intro i
  fin_cases i
  · exact C011_row_00
  · exact C011_row_01
  · exact C011_row_02
  · exact C011_row_03
  · exact C011_row_04
  · exact C011_row_05
  · exact C011_row_06
  · exact C011_row_07
  · exact C011_row_08
  · exact C011_row_09
  · exact C011_row_10
  · exact C011_row_11
  · exact C011_row_12
  · exact C011_row_13

private theorem C011_column_00 : reversePack 256 (fun j : Fin 14 => C011_digit j 0)=C011_columnCode 0 := by decide +kernel

private theorem C011_column_01 : reversePack 256 (fun j : Fin 14 => C011_digit j 1)=C011_columnCode 1 := by decide +kernel

private theorem C011_column_02 : reversePack 256 (fun j : Fin 14 => C011_digit j 2)=C011_columnCode 2 := by decide +kernel

private theorem C011_column_03 : reversePack 256 (fun j : Fin 14 => C011_digit j 3)=C011_columnCode 3 := by decide +kernel

private theorem C011_column_04 : reversePack 256 (fun j : Fin 14 => C011_digit j 4)=C011_columnCode 4 := by decide +kernel

private theorem C011_column_05 : reversePack 256 (fun j : Fin 14 => C011_digit j 5)=C011_columnCode 5 := by decide +kernel

private theorem C011_column_06 : reversePack 256 (fun j : Fin 14 => C011_digit j 6)=C011_columnCode 6 := by decide +kernel

private theorem C011_column_07 : reversePack 256 (fun j : Fin 14 => C011_digit j 7)=C011_columnCode 7 := by decide +kernel

private theorem C011_column_08 : reversePack 256 (fun j : Fin 14 => C011_digit j 8)=C011_columnCode 8 := by decide +kernel

private theorem C011_column_09 : reversePack 256 (fun j : Fin 14 => C011_digit j 9)=C011_columnCode 9 := by decide +kernel

private theorem C011_column_10 : reversePack 256 (fun j : Fin 14 => C011_digit j 10)=C011_columnCode 10 := by decide +kernel

private theorem C011_column_11 : reversePack 256 (fun j : Fin 14 => C011_digit j 11)=C011_columnCode 11 := by decide +kernel

private theorem C011_column_12 : reversePack 256 (fun j : Fin 14 => C011_digit j 12)=C011_columnCode 12 := by decide +kernel

private theorem C011_column_13 : reversePack 256 (fun j : Fin 14 => C011_digit j 13)=C011_columnCode 13 := by decide +kernel

theorem C011_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C011_digit j i)=C011_columnCode i := by
  intro i
  fin_cases i
  · exact C011_column_00
  · exact C011_column_01
  · exact C011_column_02
  · exact C011_column_03
  · exact C011_column_04
  · exact C011_column_05
  · exact C011_column_06
  · exact C011_column_07
  · exact C011_column_08
  · exact C011_column_09
  · exact C011_column_10
  · exact C011_column_11
  · exact C011_column_12
  · exact C011_column_13

def C011_data : PackedData 14 5 256 where
  raw := C011_digit
  digit_lt := C011_bound
  rowCode := C011_rowCode
  columnCode := C011_columnCode
  row_binding := C011_row_binding
  column_binding := C011_column_binding

def C012_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 2199314899554
  | 1 => 578093682881
  | 2 => 2354741789713
  | 3 => 790748238881
  | 4 => 244884803809
  | 5 => 131072
  | 6 => 4603281628
  | 7 => 1791305532625
  | 8 => 1670797951499
  | 9 => 1101795460352
  | 10 => 38654705664
  | 11 => 8589934592
  | 12 => 1651591217931
  | 13 => 1748259840736
  | _ => 0

def C012_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 237684487598206428500017086722
  | 1 => 81208866577139537737086511742980
  | 2 => 61164141479901751570914439332609
  | 3 => 20361637775629258586541904756737
  | 4 => 40564819207303629078274966290690
  | 5 => 316912654834908466538950427396
  | 6 => 40564819207377127824193652720640
  | 7 => 61164141465771401495260585787395
  | 8 => 81288094739690695281352498020609
  | 9 => 20361637770888445922548520059650
  | 10 => 81288099584857298127820158992896
  | 11 => 60847543131705004563591843676928
  | 12 => 20282409603651814539148262506496
  | 13 => 61084913307998093655364935614724
  | _ => 0

def C012_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 40882042560814559945533738188804
  | 1 => 20283338063459129405732781490177
  | 2 => 20440868365421521559652818616836
  | 3 => 20599324676301252855478054290177
  | 4 => 20600250713515971149560480531200
  | 5 => 73786976294838206464
  | 6 => 81368251357197386334482131320832
  | 7 => 20441796820487662066907519910403
  | 8 => 60926458182450724252910308425731
  | 9 => 1240357909371635086263320578
  | 10 => 67371008
  | 11 => 65536
  | 12 => 60927696122508168708737468465155
  | 13 => 317842323457218929964230050051
  | _ => 0

def C012_digit (i j : Fin 14) : ℕ := packedDigit 3 (C012_lowColumnCode j) i.val

private theorem C012_bound_00 : ∀ j : Fin 14, C012_digit 0 j < 5 := by decide +kernel

private theorem C012_bound_01 : ∀ j : Fin 14, C012_digit 1 j < 5 := by decide +kernel

private theorem C012_bound_02 : ∀ j : Fin 14, C012_digit 2 j < 5 := by decide +kernel

private theorem C012_bound_03 : ∀ j : Fin 14, C012_digit 3 j < 5 := by decide +kernel

private theorem C012_bound_04 : ∀ j : Fin 14, C012_digit 4 j < 5 := by decide +kernel

private theorem C012_bound_05 : ∀ j : Fin 14, C012_digit 5 j < 5 := by decide +kernel

private theorem C012_bound_06 : ∀ j : Fin 14, C012_digit 6 j < 5 := by decide +kernel

private theorem C012_bound_07 : ∀ j : Fin 14, C012_digit 7 j < 5 := by decide +kernel

private theorem C012_bound_08 : ∀ j : Fin 14, C012_digit 8 j < 5 := by decide +kernel

private theorem C012_bound_09 : ∀ j : Fin 14, C012_digit 9 j < 5 := by decide +kernel

private theorem C012_bound_10 : ∀ j : Fin 14, C012_digit 10 j < 5 := by decide +kernel

private theorem C012_bound_11 : ∀ j : Fin 14, C012_digit 11 j < 5 := by decide +kernel

private theorem C012_bound_12 : ∀ j : Fin 14, C012_digit 12 j < 5 := by decide +kernel

private theorem C012_bound_13 : ∀ j : Fin 14, C012_digit 13 j < 5 := by decide +kernel

theorem C012_bound : ∀ i j : Fin 14, C012_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C012_bound_00 j
  · exact C012_bound_01 j
  · exact C012_bound_02 j
  · exact C012_bound_03 j
  · exact C012_bound_04 j
  · exact C012_bound_05 j
  · exact C012_bound_06 j
  · exact C012_bound_07 j
  · exact C012_bound_08 j
  · exact C012_bound_09 j
  · exact C012_bound_10 j
  · exact C012_bound_11 j
  · exact C012_bound_12 j
  · exact C012_bound_13 j

private theorem C012_row_00 : pack 256 (C012_digit 0)=C012_rowCode 0 := by decide +kernel

private theorem C012_row_01 : pack 256 (C012_digit 1)=C012_rowCode 1 := by decide +kernel

private theorem C012_row_02 : pack 256 (C012_digit 2)=C012_rowCode 2 := by decide +kernel

private theorem C012_row_03 : pack 256 (C012_digit 3)=C012_rowCode 3 := by decide +kernel

private theorem C012_row_04 : pack 256 (C012_digit 4)=C012_rowCode 4 := by decide +kernel

private theorem C012_row_05 : pack 256 (C012_digit 5)=C012_rowCode 5 := by decide +kernel

private theorem C012_row_06 : pack 256 (C012_digit 6)=C012_rowCode 6 := by decide +kernel

private theorem C012_row_07 : pack 256 (C012_digit 7)=C012_rowCode 7 := by decide +kernel

private theorem C012_row_08 : pack 256 (C012_digit 8)=C012_rowCode 8 := by decide +kernel

private theorem C012_row_09 : pack 256 (C012_digit 9)=C012_rowCode 9 := by decide +kernel

private theorem C012_row_10 : pack 256 (C012_digit 10)=C012_rowCode 10 := by decide +kernel

private theorem C012_row_11 : pack 256 (C012_digit 11)=C012_rowCode 11 := by decide +kernel

private theorem C012_row_12 : pack 256 (C012_digit 12)=C012_rowCode 12 := by decide +kernel

private theorem C012_row_13 : pack 256 (C012_digit 13)=C012_rowCode 13 := by decide +kernel

theorem C012_row_binding : ∀ i : Fin 14, pack 256 (C012_digit i)=C012_rowCode i := by
  intro i
  fin_cases i
  · exact C012_row_00
  · exact C012_row_01
  · exact C012_row_02
  · exact C012_row_03
  · exact C012_row_04
  · exact C012_row_05
  · exact C012_row_06
  · exact C012_row_07
  · exact C012_row_08
  · exact C012_row_09
  · exact C012_row_10
  · exact C012_row_11
  · exact C012_row_12
  · exact C012_row_13

private theorem C012_column_00 : reversePack 256 (fun j : Fin 14 => C012_digit j 0)=C012_columnCode 0 := by decide +kernel

private theorem C012_column_01 : reversePack 256 (fun j : Fin 14 => C012_digit j 1)=C012_columnCode 1 := by decide +kernel

private theorem C012_column_02 : reversePack 256 (fun j : Fin 14 => C012_digit j 2)=C012_columnCode 2 := by decide +kernel

private theorem C012_column_03 : reversePack 256 (fun j : Fin 14 => C012_digit j 3)=C012_columnCode 3 := by decide +kernel

private theorem C012_column_04 : reversePack 256 (fun j : Fin 14 => C012_digit j 4)=C012_columnCode 4 := by decide +kernel

private theorem C012_column_05 : reversePack 256 (fun j : Fin 14 => C012_digit j 5)=C012_columnCode 5 := by decide +kernel

private theorem C012_column_06 : reversePack 256 (fun j : Fin 14 => C012_digit j 6)=C012_columnCode 6 := by decide +kernel

private theorem C012_column_07 : reversePack 256 (fun j : Fin 14 => C012_digit j 7)=C012_columnCode 7 := by decide +kernel

private theorem C012_column_08 : reversePack 256 (fun j : Fin 14 => C012_digit j 8)=C012_columnCode 8 := by decide +kernel

private theorem C012_column_09 : reversePack 256 (fun j : Fin 14 => C012_digit j 9)=C012_columnCode 9 := by decide +kernel

private theorem C012_column_10 : reversePack 256 (fun j : Fin 14 => C012_digit j 10)=C012_columnCode 10 := by decide +kernel

private theorem C012_column_11 : reversePack 256 (fun j : Fin 14 => C012_digit j 11)=C012_columnCode 11 := by decide +kernel

private theorem C012_column_12 : reversePack 256 (fun j : Fin 14 => C012_digit j 12)=C012_columnCode 12 := by decide +kernel

private theorem C012_column_13 : reversePack 256 (fun j : Fin 14 => C012_digit j 13)=C012_columnCode 13 := by decide +kernel

theorem C012_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C012_digit j i)=C012_columnCode i := by
  intro i
  fin_cases i
  · exact C012_column_00
  · exact C012_column_01
  · exact C012_column_02
  · exact C012_column_03
  · exact C012_column_04
  · exact C012_column_05
  · exact C012_column_06
  · exact C012_column_07
  · exact C012_column_08
  · exact C012_column_09
  · exact C012_column_10
  · exact C012_column_11
  · exact C012_column_12
  · exact C012_column_13

def C012_data : PackedData 14 5 256 where
  raw := C012_digit
  digit_lt := C012_bound
  rowCode := C012_rowCode
  columnCode := C012_columnCode
  row_binding := C012_row_binding
  column_binding := C012_column_binding

def C013_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 72143209219
  | 1 => 1658449174600
  | 2 => 551433846816
  | 3 => 860470462113
  | 4 => 1306094216858
  | 5 => 32768
  | 6 => 141774914563
  | 7 => 1925691484305
  | 8 => 1650627190992
  | 9 => 2406430414538
  | 10 => 1073741824
  | 11 => 8589934592
  | 12 => 2347787163210
  | 13 => 1385135482897
  | _ => 0

def C013_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 20440865938125004966901204385795
  | 1 => 40644047374577009271706138968320
  | 2 => 79228176736848133620307591428
  | 3 => 81367322916316862950517613002753
  | 4 => 40644047374577009271701844001280
  | 5 => 81288094758524677147979149280260
  | 6 => 79228176736849259520214499588
  | 7 => 81129638428773854046425498780160
  | 8 => 237684497006261515924032193284
  | 9 => 316912654816533494186289398785
  | 10 => 40723276745998575548148081557507
  | 11 => 20361947251175756106609587126528
  | 12 => 81288094753802598612924085829633
  | 13 => 40881731876305420534759108444928
  | _ => 0

def C013_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 60848467959994191477819209416960
  | 1 => 79537657042678248556103532547
  | 2 => 316912668965042087935747293185
  | 3 => 20599944869432332843173378524161
  | 4 => 40803126301088113039689824338690
  | 5 => 18446744073709551616
  | 6 => 60847231228862279810321404133888
  | 7 => 20441489743847997614601778758659
  | 8 => 159384789502941850022784794627
  | 9 => 40644979456420898543156607320836
  | 10 => 16777216
  | 11 => 65536
  | 12 => 40644360486364217406371146039812
  | 13 => 20440870773901998625585107108866
  | _ => 0

def C013_digit (i j : Fin 14) : ℕ := packedDigit 3 (C013_lowColumnCode j) i.val

private theorem C013_bound_00 : ∀ j : Fin 14, C013_digit 0 j < 5 := by decide +kernel

private theorem C013_bound_01 : ∀ j : Fin 14, C013_digit 1 j < 5 := by decide +kernel

private theorem C013_bound_02 : ∀ j : Fin 14, C013_digit 2 j < 5 := by decide +kernel

private theorem C013_bound_03 : ∀ j : Fin 14, C013_digit 3 j < 5 := by decide +kernel

private theorem C013_bound_04 : ∀ j : Fin 14, C013_digit 4 j < 5 := by decide +kernel

private theorem C013_bound_05 : ∀ j : Fin 14, C013_digit 5 j < 5 := by decide +kernel

private theorem C013_bound_06 : ∀ j : Fin 14, C013_digit 6 j < 5 := by decide +kernel

private theorem C013_bound_07 : ∀ j : Fin 14, C013_digit 7 j < 5 := by decide +kernel

private theorem C013_bound_08 : ∀ j : Fin 14, C013_digit 8 j < 5 := by decide +kernel

private theorem C013_bound_09 : ∀ j : Fin 14, C013_digit 9 j < 5 := by decide +kernel

private theorem C013_bound_10 : ∀ j : Fin 14, C013_digit 10 j < 5 := by decide +kernel

private theorem C013_bound_11 : ∀ j : Fin 14, C013_digit 11 j < 5 := by decide +kernel

private theorem C013_bound_12 : ∀ j : Fin 14, C013_digit 12 j < 5 := by decide +kernel

private theorem C013_bound_13 : ∀ j : Fin 14, C013_digit 13 j < 5 := by decide +kernel

theorem C013_bound : ∀ i j : Fin 14, C013_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C013_bound_00 j
  · exact C013_bound_01 j
  · exact C013_bound_02 j
  · exact C013_bound_03 j
  · exact C013_bound_04 j
  · exact C013_bound_05 j
  · exact C013_bound_06 j
  · exact C013_bound_07 j
  · exact C013_bound_08 j
  · exact C013_bound_09 j
  · exact C013_bound_10 j
  · exact C013_bound_11 j
  · exact C013_bound_12 j
  · exact C013_bound_13 j

private theorem C013_row_00 : pack 256 (C013_digit 0)=C013_rowCode 0 := by decide +kernel

private theorem C013_row_01 : pack 256 (C013_digit 1)=C013_rowCode 1 := by decide +kernel

private theorem C013_row_02 : pack 256 (C013_digit 2)=C013_rowCode 2 := by decide +kernel

private theorem C013_row_03 : pack 256 (C013_digit 3)=C013_rowCode 3 := by decide +kernel

private theorem C013_row_04 : pack 256 (C013_digit 4)=C013_rowCode 4 := by decide +kernel

private theorem C013_row_05 : pack 256 (C013_digit 5)=C013_rowCode 5 := by decide +kernel

private theorem C013_row_06 : pack 256 (C013_digit 6)=C013_rowCode 6 := by decide +kernel

private theorem C013_row_07 : pack 256 (C013_digit 7)=C013_rowCode 7 := by decide +kernel

private theorem C013_row_08 : pack 256 (C013_digit 8)=C013_rowCode 8 := by decide +kernel

private theorem C013_row_09 : pack 256 (C013_digit 9)=C013_rowCode 9 := by decide +kernel

private theorem C013_row_10 : pack 256 (C013_digit 10)=C013_rowCode 10 := by decide +kernel

private theorem C013_row_11 : pack 256 (C013_digit 11)=C013_rowCode 11 := by decide +kernel

private theorem C013_row_12 : pack 256 (C013_digit 12)=C013_rowCode 12 := by decide +kernel

private theorem C013_row_13 : pack 256 (C013_digit 13)=C013_rowCode 13 := by decide +kernel

theorem C013_row_binding : ∀ i : Fin 14, pack 256 (C013_digit i)=C013_rowCode i := by
  intro i
  fin_cases i
  · exact C013_row_00
  · exact C013_row_01
  · exact C013_row_02
  · exact C013_row_03
  · exact C013_row_04
  · exact C013_row_05
  · exact C013_row_06
  · exact C013_row_07
  · exact C013_row_08
  · exact C013_row_09
  · exact C013_row_10
  · exact C013_row_11
  · exact C013_row_12
  · exact C013_row_13

private theorem C013_column_00 : reversePack 256 (fun j : Fin 14 => C013_digit j 0)=C013_columnCode 0 := by decide +kernel

private theorem C013_column_01 : reversePack 256 (fun j : Fin 14 => C013_digit j 1)=C013_columnCode 1 := by decide +kernel

private theorem C013_column_02 : reversePack 256 (fun j : Fin 14 => C013_digit j 2)=C013_columnCode 2 := by decide +kernel

private theorem C013_column_03 : reversePack 256 (fun j : Fin 14 => C013_digit j 3)=C013_columnCode 3 := by decide +kernel

private theorem C013_column_04 : reversePack 256 (fun j : Fin 14 => C013_digit j 4)=C013_columnCode 4 := by decide +kernel

private theorem C013_column_05 : reversePack 256 (fun j : Fin 14 => C013_digit j 5)=C013_columnCode 5 := by decide +kernel

private theorem C013_column_06 : reversePack 256 (fun j : Fin 14 => C013_digit j 6)=C013_columnCode 6 := by decide +kernel

private theorem C013_column_07 : reversePack 256 (fun j : Fin 14 => C013_digit j 7)=C013_columnCode 7 := by decide +kernel

private theorem C013_column_08 : reversePack 256 (fun j : Fin 14 => C013_digit j 8)=C013_columnCode 8 := by decide +kernel

private theorem C013_column_09 : reversePack 256 (fun j : Fin 14 => C013_digit j 9)=C013_columnCode 9 := by decide +kernel

private theorem C013_column_10 : reversePack 256 (fun j : Fin 14 => C013_digit j 10)=C013_columnCode 10 := by decide +kernel

private theorem C013_column_11 : reversePack 256 (fun j : Fin 14 => C013_digit j 11)=C013_columnCode 11 := by decide +kernel

private theorem C013_column_12 : reversePack 256 (fun j : Fin 14 => C013_digit j 12)=C013_columnCode 12 := by decide +kernel

private theorem C013_column_13 : reversePack 256 (fun j : Fin 14 => C013_digit j 13)=C013_columnCode 13 := by decide +kernel

theorem C013_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C013_digit j i)=C013_columnCode i := by
  intro i
  fin_cases i
  · exact C013_column_00
  · exact C013_column_01
  · exact C013_column_02
  · exact C013_column_03
  · exact C013_column_04
  · exact C013_column_05
  · exact C013_column_06
  · exact C013_column_07
  · exact C013_column_08
  · exact C013_column_09
  · exact C013_column_10
  · exact C013_column_11
  · exact C013_column_12
  · exact C013_column_13

def C013_data : PackedData 14 5 256 where
  raw := C013_digit
  digit_lt := C013_bound
  rowCode := C013_rowCode
  columnCode := C013_columnCode
  row_binding := C013_row_binding
  column_binding := C013_column_binding

def C014_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 638395101386
  | 1 => 1134043959508
  | 2 => 1332029949524
  | 3 => 69816562816
  | 4 => 1109611783969
  | 5 => 131072
  | 6 => 164685153428
  | 7 => 139756844288
  | 8 => 1416636618
  | 9 => 1310137815818
  | 10 => 38654705664
  | 11 => 8589934592
  | 12 => 786400875652
  | 13 => 208862447257
  | _ => 0

def C014_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 20599322263190355354112338691074
  | 1 => 60847228815695825061752242045441
  | 2 => 40723275551276964480124618605315
  | 3 => 61005685140779838084344273108992
  | 4 => 79228167273740481401362317571
  | 5 => 158456329750895162454779626240
  | 6 => 60926456987710306149531459453444
  | 7 => 20361637775666080017095302644226
  | 8 => 20361637775684598818771606635011
  | 9 => 81367322906908807581618554536196
  | 10 => 40881736711971733729005031915522
  | 11 => 237998808255893660795280753666
  | 12 => 61084913312665048411369367601153
  | 13 => 79228171958997303341424443905
  | _ => 0

def C014_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 40644975839014457465945010077953
  | 1 => 81289023199442525801614389018626
  | 2 => 81288407851422707017505147388674
  | 3 => 621402038454271123231080704
  | 4 => 20600563829970277024029103685634
  | 5 => 73786976294838206464
  | 6 => 81288716127506492290384793895424
  | 7 => 1240372058168457008588521984
  | 8 => 40644980669995369724157945184256
  | 9 => 40645286523523740145270927655682
  | 10 => 67371008
  | 11 => 65536
  | 12 => 81130259807237295926383346909953
  | 13 => 20520716687991781426126672364288
  | _ => 0

def C014_digit (i j : Fin 14) : ℕ := packedDigit 3 (C014_lowColumnCode j) i.val

private theorem C014_bound_00 : ∀ j : Fin 14, C014_digit 0 j < 5 := by decide +kernel

private theorem C014_bound_01 : ∀ j : Fin 14, C014_digit 1 j < 5 := by decide +kernel

private theorem C014_bound_02 : ∀ j : Fin 14, C014_digit 2 j < 5 := by decide +kernel

private theorem C014_bound_03 : ∀ j : Fin 14, C014_digit 3 j < 5 := by decide +kernel

private theorem C014_bound_04 : ∀ j : Fin 14, C014_digit 4 j < 5 := by decide +kernel

private theorem C014_bound_05 : ∀ j : Fin 14, C014_digit 5 j < 5 := by decide +kernel

private theorem C014_bound_06 : ∀ j : Fin 14, C014_digit 6 j < 5 := by decide +kernel

private theorem C014_bound_07 : ∀ j : Fin 14, C014_digit 7 j < 5 := by decide +kernel

private theorem C014_bound_08 : ∀ j : Fin 14, C014_digit 8 j < 5 := by decide +kernel

private theorem C014_bound_09 : ∀ j : Fin 14, C014_digit 9 j < 5 := by decide +kernel

private theorem C014_bound_10 : ∀ j : Fin 14, C014_digit 10 j < 5 := by decide +kernel

private theorem C014_bound_11 : ∀ j : Fin 14, C014_digit 11 j < 5 := by decide +kernel

private theorem C014_bound_12 : ∀ j : Fin 14, C014_digit 12 j < 5 := by decide +kernel

private theorem C014_bound_13 : ∀ j : Fin 14, C014_digit 13 j < 5 := by decide +kernel

theorem C014_bound : ∀ i j : Fin 14, C014_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C014_bound_00 j
  · exact C014_bound_01 j
  · exact C014_bound_02 j
  · exact C014_bound_03 j
  · exact C014_bound_04 j
  · exact C014_bound_05 j
  · exact C014_bound_06 j
  · exact C014_bound_07 j
  · exact C014_bound_08 j
  · exact C014_bound_09 j
  · exact C014_bound_10 j
  · exact C014_bound_11 j
  · exact C014_bound_12 j
  · exact C014_bound_13 j

private theorem C014_row_00 : pack 256 (C014_digit 0)=C014_rowCode 0 := by decide +kernel

private theorem C014_row_01 : pack 256 (C014_digit 1)=C014_rowCode 1 := by decide +kernel

private theorem C014_row_02 : pack 256 (C014_digit 2)=C014_rowCode 2 := by decide +kernel

private theorem C014_row_03 : pack 256 (C014_digit 3)=C014_rowCode 3 := by decide +kernel

private theorem C014_row_04 : pack 256 (C014_digit 4)=C014_rowCode 4 := by decide +kernel

private theorem C014_row_05 : pack 256 (C014_digit 5)=C014_rowCode 5 := by decide +kernel

private theorem C014_row_06 : pack 256 (C014_digit 6)=C014_rowCode 6 := by decide +kernel

private theorem C014_row_07 : pack 256 (C014_digit 7)=C014_rowCode 7 := by decide +kernel

private theorem C014_row_08 : pack 256 (C014_digit 8)=C014_rowCode 8 := by decide +kernel

private theorem C014_row_09 : pack 256 (C014_digit 9)=C014_rowCode 9 := by decide +kernel

private theorem C014_row_10 : pack 256 (C014_digit 10)=C014_rowCode 10 := by decide +kernel

private theorem C014_row_11 : pack 256 (C014_digit 11)=C014_rowCode 11 := by decide +kernel

private theorem C014_row_12 : pack 256 (C014_digit 12)=C014_rowCode 12 := by decide +kernel

private theorem C014_row_13 : pack 256 (C014_digit 13)=C014_rowCode 13 := by decide +kernel

theorem C014_row_binding : ∀ i : Fin 14, pack 256 (C014_digit i)=C014_rowCode i := by
  intro i
  fin_cases i
  · exact C014_row_00
  · exact C014_row_01
  · exact C014_row_02
  · exact C014_row_03
  · exact C014_row_04
  · exact C014_row_05
  · exact C014_row_06
  · exact C014_row_07
  · exact C014_row_08
  · exact C014_row_09
  · exact C014_row_10
  · exact C014_row_11
  · exact C014_row_12
  · exact C014_row_13

private theorem C014_column_00 : reversePack 256 (fun j : Fin 14 => C014_digit j 0)=C014_columnCode 0 := by decide +kernel

private theorem C014_column_01 : reversePack 256 (fun j : Fin 14 => C014_digit j 1)=C014_columnCode 1 := by decide +kernel

private theorem C014_column_02 : reversePack 256 (fun j : Fin 14 => C014_digit j 2)=C014_columnCode 2 := by decide +kernel

private theorem C014_column_03 : reversePack 256 (fun j : Fin 14 => C014_digit j 3)=C014_columnCode 3 := by decide +kernel

private theorem C014_column_04 : reversePack 256 (fun j : Fin 14 => C014_digit j 4)=C014_columnCode 4 := by decide +kernel

private theorem C014_column_05 : reversePack 256 (fun j : Fin 14 => C014_digit j 5)=C014_columnCode 5 := by decide +kernel

private theorem C014_column_06 : reversePack 256 (fun j : Fin 14 => C014_digit j 6)=C014_columnCode 6 := by decide +kernel

private theorem C014_column_07 : reversePack 256 (fun j : Fin 14 => C014_digit j 7)=C014_columnCode 7 := by decide +kernel

private theorem C014_column_08 : reversePack 256 (fun j : Fin 14 => C014_digit j 8)=C014_columnCode 8 := by decide +kernel

private theorem C014_column_09 : reversePack 256 (fun j : Fin 14 => C014_digit j 9)=C014_columnCode 9 := by decide +kernel

private theorem C014_column_10 : reversePack 256 (fun j : Fin 14 => C014_digit j 10)=C014_columnCode 10 := by decide +kernel

private theorem C014_column_11 : reversePack 256 (fun j : Fin 14 => C014_digit j 11)=C014_columnCode 11 := by decide +kernel

private theorem C014_column_12 : reversePack 256 (fun j : Fin 14 => C014_digit j 12)=C014_columnCode 12 := by decide +kernel

private theorem C014_column_13 : reversePack 256 (fun j : Fin 14 => C014_digit j 13)=C014_columnCode 13 := by decide +kernel

theorem C014_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C014_digit j i)=C014_columnCode i := by
  intro i
  fin_cases i
  · exact C014_column_00
  · exact C014_column_01
  · exact C014_column_02
  · exact C014_column_03
  · exact C014_column_04
  · exact C014_column_05
  · exact C014_column_06
  · exact C014_column_07
  · exact C014_column_08
  · exact C014_column_09
  · exact C014_column_10
  · exact C014_column_11
  · exact C014_column_12
  · exact C014_column_13

def C014_data : PackedData 14 5 256 where
  raw := C014_digit
  digit_lt := C014_bound
  rowCode := C014_rowCode
  columnCode := C014_columnCode
  row_binding := C014_row_binding
  column_binding := C014_column_binding

end SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryCaches02
