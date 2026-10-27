import SymmetricSubgroupAsymptotics.MatrixKroneckerProductReflection
import Mathlib.Tactic.FinCases

/-! Literal14/F5 selected caches; digit bounds and both pack bindings are independently kernel checked. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedCaches11
open MatrixKroneckerProductReflection MatrixKroneckerDotReflection
open MatrixNaturalRowDotReflection SmallNaturalMatrixProductReflection

def C095_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 860673278108
  | 1 => 1817367872768
  | 2 => 1718008459491
  | 3 => 1652488679424
  | 4 => 645319627456
  | 5 => 138513231872
  | 6 => 767863882786
  | 7 => 551903313920
  | 8 => 16777216
  | 9 => 134217728
  | 10 => 138800005268
  | 11 => 140661243904
  | 12 => 2476082991360
  | 13 => 549755813888
  | _ => 0

def C095_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 4835703279021466652442628
  | 1 => 2417851640355158256517123
  | 2 => 316915067908696579645410313218
  | 3 => 562954248389120
  | 4 => 80466102553837951547475165184
  | 5 => 562949953487360
  | 6 => 238922427582078395267439264768
  | 7 => 1208925820177579128259585
  | 8 => 158457533972795033889972224772
  | 9 => 2422574005993602971337732
  | 10 => 159385988983957285739299865601
  | 11 => 281487861613316
  | 12 => 317534037928340116398223196676
  | 13 => 20599322253708800113394787222273
  | _ => 0

def C095_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 81367941872169117684597306688513
  | 1 => 1240357928107457272508252675
  | 2 => 61165069930227223529342290100483
  | 3 => 14167099448608985972739
  | 4 => 929668677866305487125020929
  | 5 => 14167243563797028274688
  | 6 => 40881734275248931478628745675521
  | 7 => 18889465931478614409217
  | 8 => 1099511627776
  | 9 => 4294967296
  | 10 => 81288713709654853343696637657600
  | 11 => 18889754161854782898688
  | 12 => 1237944761868038125714932740
  | 13 => 1
  | _ => 0

def C095_digit (i j : Fin 14) : ℕ := packedDigit 3 (C095_lowColumnCode j) i.val

private theorem C095_bound_00 : ∀ j : Fin 14, C095_digit 0 j < 5 := by decide +kernel

private theorem C095_bound_01 : ∀ j : Fin 14, C095_digit 1 j < 5 := by decide +kernel

private theorem C095_bound_02 : ∀ j : Fin 14, C095_digit 2 j < 5 := by decide +kernel

private theorem C095_bound_03 : ∀ j : Fin 14, C095_digit 3 j < 5 := by decide +kernel

private theorem C095_bound_04 : ∀ j : Fin 14, C095_digit 4 j < 5 := by decide +kernel

private theorem C095_bound_05 : ∀ j : Fin 14, C095_digit 5 j < 5 := by decide +kernel

private theorem C095_bound_06 : ∀ j : Fin 14, C095_digit 6 j < 5 := by decide +kernel

private theorem C095_bound_07 : ∀ j : Fin 14, C095_digit 7 j < 5 := by decide +kernel

private theorem C095_bound_08 : ∀ j : Fin 14, C095_digit 8 j < 5 := by decide +kernel

private theorem C095_bound_09 : ∀ j : Fin 14, C095_digit 9 j < 5 := by decide +kernel

private theorem C095_bound_10 : ∀ j : Fin 14, C095_digit 10 j < 5 := by decide +kernel

private theorem C095_bound_11 : ∀ j : Fin 14, C095_digit 11 j < 5 := by decide +kernel

private theorem C095_bound_12 : ∀ j : Fin 14, C095_digit 12 j < 5 := by decide +kernel

private theorem C095_bound_13 : ∀ j : Fin 14, C095_digit 13 j < 5 := by decide +kernel

theorem C095_bound : ∀ i j : Fin 14, C095_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C095_bound_00 j
  · exact C095_bound_01 j
  · exact C095_bound_02 j
  · exact C095_bound_03 j
  · exact C095_bound_04 j
  · exact C095_bound_05 j
  · exact C095_bound_06 j
  · exact C095_bound_07 j
  · exact C095_bound_08 j
  · exact C095_bound_09 j
  · exact C095_bound_10 j
  · exact C095_bound_11 j
  · exact C095_bound_12 j
  · exact C095_bound_13 j

private theorem C095_row_00 : pack 256 (C095_digit 0)=C095_rowCode 0 := by decide +kernel

private theorem C095_row_01 : pack 256 (C095_digit 1)=C095_rowCode 1 := by decide +kernel

private theorem C095_row_02 : pack 256 (C095_digit 2)=C095_rowCode 2 := by decide +kernel

private theorem C095_row_03 : pack 256 (C095_digit 3)=C095_rowCode 3 := by decide +kernel

private theorem C095_row_04 : pack 256 (C095_digit 4)=C095_rowCode 4 := by decide +kernel

private theorem C095_row_05 : pack 256 (C095_digit 5)=C095_rowCode 5 := by decide +kernel

private theorem C095_row_06 : pack 256 (C095_digit 6)=C095_rowCode 6 := by decide +kernel

private theorem C095_row_07 : pack 256 (C095_digit 7)=C095_rowCode 7 := by decide +kernel

private theorem C095_row_08 : pack 256 (C095_digit 8)=C095_rowCode 8 := by decide +kernel

private theorem C095_row_09 : pack 256 (C095_digit 9)=C095_rowCode 9 := by decide +kernel

private theorem C095_row_10 : pack 256 (C095_digit 10)=C095_rowCode 10 := by decide +kernel

private theorem C095_row_11 : pack 256 (C095_digit 11)=C095_rowCode 11 := by decide +kernel

private theorem C095_row_12 : pack 256 (C095_digit 12)=C095_rowCode 12 := by decide +kernel

private theorem C095_row_13 : pack 256 (C095_digit 13)=C095_rowCode 13 := by decide +kernel

theorem C095_row_binding : ∀ i : Fin 14, pack 256 (C095_digit i)=C095_rowCode i := by
  intro i
  fin_cases i
  · exact C095_row_00
  · exact C095_row_01
  · exact C095_row_02
  · exact C095_row_03
  · exact C095_row_04
  · exact C095_row_05
  · exact C095_row_06
  · exact C095_row_07
  · exact C095_row_08
  · exact C095_row_09
  · exact C095_row_10
  · exact C095_row_11
  · exact C095_row_12
  · exact C095_row_13

private theorem C095_column_00 : reversePack 256 (fun j : Fin 14 => C095_digit j 0)=C095_columnCode 0 := by decide +kernel

private theorem C095_column_01 : reversePack 256 (fun j : Fin 14 => C095_digit j 1)=C095_columnCode 1 := by decide +kernel

private theorem C095_column_02 : reversePack 256 (fun j : Fin 14 => C095_digit j 2)=C095_columnCode 2 := by decide +kernel

private theorem C095_column_03 : reversePack 256 (fun j : Fin 14 => C095_digit j 3)=C095_columnCode 3 := by decide +kernel

private theorem C095_column_04 : reversePack 256 (fun j : Fin 14 => C095_digit j 4)=C095_columnCode 4 := by decide +kernel

private theorem C095_column_05 : reversePack 256 (fun j : Fin 14 => C095_digit j 5)=C095_columnCode 5 := by decide +kernel

private theorem C095_column_06 : reversePack 256 (fun j : Fin 14 => C095_digit j 6)=C095_columnCode 6 := by decide +kernel

private theorem C095_column_07 : reversePack 256 (fun j : Fin 14 => C095_digit j 7)=C095_columnCode 7 := by decide +kernel

private theorem C095_column_08 : reversePack 256 (fun j : Fin 14 => C095_digit j 8)=C095_columnCode 8 := by decide +kernel

private theorem C095_column_09 : reversePack 256 (fun j : Fin 14 => C095_digit j 9)=C095_columnCode 9 := by decide +kernel

private theorem C095_column_10 : reversePack 256 (fun j : Fin 14 => C095_digit j 10)=C095_columnCode 10 := by decide +kernel

private theorem C095_column_11 : reversePack 256 (fun j : Fin 14 => C095_digit j 11)=C095_columnCode 11 := by decide +kernel

private theorem C095_column_12 : reversePack 256 (fun j : Fin 14 => C095_digit j 12)=C095_columnCode 12 := by decide +kernel

private theorem C095_column_13 : reversePack 256 (fun j : Fin 14 => C095_digit j 13)=C095_columnCode 13 := by decide +kernel

theorem C095_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C095_digit j i)=C095_columnCode i := by
  intro i
  fin_cases i
  · exact C095_column_00
  · exact C095_column_01
  · exact C095_column_02
  · exact C095_column_03
  · exact C095_column_04
  · exact C095_column_05
  · exact C095_column_06
  · exact C095_column_07
  · exact C095_column_08
  · exact C095_column_09
  · exact C095_column_10
  · exact C095_column_11
  · exact C095_column_12
  · exact C095_column_13

def C095_data : PackedData 14 5 256 where
  raw := C095_digit
  digit_lt := C095_bound
  rowCode := C095_rowCode
  columnCode := C095_columnCode
  row_binding := C095_row_binding
  column_binding := C095_column_binding

def C096_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 1104346710801
  | 1 => 1271444620993
  | 2 => 1855434539296
  | 3 => 860259104266
  | 4 => 558370002124
  | 5 => 1937567253763
  | 6 => 2351802064
  | 7 => 224987203683
  | 8 => 16777216
  | 9 => 134217728
  | 10 => 159321467025
  | 11 => 561603515472
  | 12 => 833511760913
  | 13 => 549755813888
  | _ => 0

def C096_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 79229371440300128320580747521
  | 1 => 159077712900099387913304014850
  | 2 => 311902861533480756973929220
  | 3 => 159080130751738900849981653761
  | 4 => 158768227890278042844612789248
  | 5 => 929663955284498675505562115
  | 6 => 238616569349860851504583344132
  | 7 => 79540065375869308596606205953
  | 8 => 79847132552499012897031061504
  | 9 => 158459956528642518193448943876
  | 10 => 933290732815118664927805444
  | 11 => 79540065375869028212567704576
  | 12 => 316915067908912756812752814592
  | 13 => 20361947251175756109912366842370
  | _ => 0

def C096_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 20442105077700932838127917072386
  | 1 => 20283341704384952722671244935682
  | 2 => 318150608985881845621600551683
  | 3 => 40644051010762452556088435016705
  | 4 => 81209797454798491832912149807105
  | 5 => 60848469168919722857687087645699
  | 6 => 159388416335741210900670971904
  | 7 => 61164455800614779037634183430912
  | 8 => 1099511627776
  | 9 => 4294967296
  | 10 => 20441489743866516693346506899968
  | 11 => 158768232667912421061100109825
  | 12 => 20440868355976787749497171149825
  | 13 => 1
  | _ => 0

def C096_digit (i j : Fin 14) : ℕ := packedDigit 3 (C096_lowColumnCode j) i.val

private theorem C096_bound_00 : ∀ j : Fin 14, C096_digit 0 j < 5 := by decide +kernel

private theorem C096_bound_01 : ∀ j : Fin 14, C096_digit 1 j < 5 := by decide +kernel

private theorem C096_bound_02 : ∀ j : Fin 14, C096_digit 2 j < 5 := by decide +kernel

private theorem C096_bound_03 : ∀ j : Fin 14, C096_digit 3 j < 5 := by decide +kernel

private theorem C096_bound_04 : ∀ j : Fin 14, C096_digit 4 j < 5 := by decide +kernel

private theorem C096_bound_05 : ∀ j : Fin 14, C096_digit 5 j < 5 := by decide +kernel

private theorem C096_bound_06 : ∀ j : Fin 14, C096_digit 6 j < 5 := by decide +kernel

private theorem C096_bound_07 : ∀ j : Fin 14, C096_digit 7 j < 5 := by decide +kernel

private theorem C096_bound_08 : ∀ j : Fin 14, C096_digit 8 j < 5 := by decide +kernel

private theorem C096_bound_09 : ∀ j : Fin 14, C096_digit 9 j < 5 := by decide +kernel

private theorem C096_bound_10 : ∀ j : Fin 14, C096_digit 10 j < 5 := by decide +kernel

private theorem C096_bound_11 : ∀ j : Fin 14, C096_digit 11 j < 5 := by decide +kernel

private theorem C096_bound_12 : ∀ j : Fin 14, C096_digit 12 j < 5 := by decide +kernel

private theorem C096_bound_13 : ∀ j : Fin 14, C096_digit 13 j < 5 := by decide +kernel

theorem C096_bound : ∀ i j : Fin 14, C096_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C096_bound_00 j
  · exact C096_bound_01 j
  · exact C096_bound_02 j
  · exact C096_bound_03 j
  · exact C096_bound_04 j
  · exact C096_bound_05 j
  · exact C096_bound_06 j
  · exact C096_bound_07 j
  · exact C096_bound_08 j
  · exact C096_bound_09 j
  · exact C096_bound_10 j
  · exact C096_bound_11 j
  · exact C096_bound_12 j
  · exact C096_bound_13 j

private theorem C096_row_00 : pack 256 (C096_digit 0)=C096_rowCode 0 := by decide +kernel

private theorem C096_row_01 : pack 256 (C096_digit 1)=C096_rowCode 1 := by decide +kernel

private theorem C096_row_02 : pack 256 (C096_digit 2)=C096_rowCode 2 := by decide +kernel

private theorem C096_row_03 : pack 256 (C096_digit 3)=C096_rowCode 3 := by decide +kernel

private theorem C096_row_04 : pack 256 (C096_digit 4)=C096_rowCode 4 := by decide +kernel

private theorem C096_row_05 : pack 256 (C096_digit 5)=C096_rowCode 5 := by decide +kernel

private theorem C096_row_06 : pack 256 (C096_digit 6)=C096_rowCode 6 := by decide +kernel

private theorem C096_row_07 : pack 256 (C096_digit 7)=C096_rowCode 7 := by decide +kernel

private theorem C096_row_08 : pack 256 (C096_digit 8)=C096_rowCode 8 := by decide +kernel

private theorem C096_row_09 : pack 256 (C096_digit 9)=C096_rowCode 9 := by decide +kernel

private theorem C096_row_10 : pack 256 (C096_digit 10)=C096_rowCode 10 := by decide +kernel

private theorem C096_row_11 : pack 256 (C096_digit 11)=C096_rowCode 11 := by decide +kernel

private theorem C096_row_12 : pack 256 (C096_digit 12)=C096_rowCode 12 := by decide +kernel

private theorem C096_row_13 : pack 256 (C096_digit 13)=C096_rowCode 13 := by decide +kernel

theorem C096_row_binding : ∀ i : Fin 14, pack 256 (C096_digit i)=C096_rowCode i := by
  intro i
  fin_cases i
  · exact C096_row_00
  · exact C096_row_01
  · exact C096_row_02
  · exact C096_row_03
  · exact C096_row_04
  · exact C096_row_05
  · exact C096_row_06
  · exact C096_row_07
  · exact C096_row_08
  · exact C096_row_09
  · exact C096_row_10
  · exact C096_row_11
  · exact C096_row_12
  · exact C096_row_13

private theorem C096_column_00 : reversePack 256 (fun j : Fin 14 => C096_digit j 0)=C096_columnCode 0 := by decide +kernel

private theorem C096_column_01 : reversePack 256 (fun j : Fin 14 => C096_digit j 1)=C096_columnCode 1 := by decide +kernel

private theorem C096_column_02 : reversePack 256 (fun j : Fin 14 => C096_digit j 2)=C096_columnCode 2 := by decide +kernel

private theorem C096_column_03 : reversePack 256 (fun j : Fin 14 => C096_digit j 3)=C096_columnCode 3 := by decide +kernel

private theorem C096_column_04 : reversePack 256 (fun j : Fin 14 => C096_digit j 4)=C096_columnCode 4 := by decide +kernel

private theorem C096_column_05 : reversePack 256 (fun j : Fin 14 => C096_digit j 5)=C096_columnCode 5 := by decide +kernel

private theorem C096_column_06 : reversePack 256 (fun j : Fin 14 => C096_digit j 6)=C096_columnCode 6 := by decide +kernel

private theorem C096_column_07 : reversePack 256 (fun j : Fin 14 => C096_digit j 7)=C096_columnCode 7 := by decide +kernel

private theorem C096_column_08 : reversePack 256 (fun j : Fin 14 => C096_digit j 8)=C096_columnCode 8 := by decide +kernel

private theorem C096_column_09 : reversePack 256 (fun j : Fin 14 => C096_digit j 9)=C096_columnCode 9 := by decide +kernel

private theorem C096_column_10 : reversePack 256 (fun j : Fin 14 => C096_digit j 10)=C096_columnCode 10 := by decide +kernel

private theorem C096_column_11 : reversePack 256 (fun j : Fin 14 => C096_digit j 11)=C096_columnCode 11 := by decide +kernel

private theorem C096_column_12 : reversePack 256 (fun j : Fin 14 => C096_digit j 12)=C096_columnCode 12 := by decide +kernel

private theorem C096_column_13 : reversePack 256 (fun j : Fin 14 => C096_digit j 13)=C096_columnCode 13 := by decide +kernel

theorem C096_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C096_digit j i)=C096_columnCode i := by
  intro i
  fin_cases i
  · exact C096_column_00
  · exact C096_column_01
  · exact C096_column_02
  · exact C096_column_03
  · exact C096_column_04
  · exact C096_column_05
  · exact C096_column_06
  · exact C096_column_07
  · exact C096_column_08
  · exact C096_column_09
  · exact C096_column_10
  · exact C096_column_11
  · exact C096_column_12
  · exact C096_column_13

def C096_data : PackedData 14 5 256 where
  raw := C096_digit
  digit_lt := C096_bound
  rowCode := C096_rowCode
  columnCode := C096_columnCode
  row_binding := C096_row_binding
  column_binding := C096_column_binding

def C098_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 208734529313
  | 1 => 1273509066777
  | 2 => 284877193376
  | 3 => 621764151384
  | 4 => 862385227844
  | 5 => 4872029906
  | 6 => 1383182893576
  | 7 => 157211735697
  | 8 => 16777216
  | 9 => 134217728
  | 10 => 165912621836
  | 11 => 654177473664
  | 12 => 619622760586
  | 13 => 549755813888
  | _ => 0

def C098_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 158461160731879193514027778305
  | 1 => 79229371440228351084845073156
  | 2 => 159080130751593942332158902276
  | 3 => 620178945678762339496625155
  | 4 => 313111787496366153589064450
  | 5 => 158459951806059578884853203968
  | 6 => 79540065375941085810867045123
  | 7 => 237685696468901142563764830212
  | 8 => 316913859001468952372723319553
  | 9 => 623810445504090183225704451
  | 10 => 79540065375869031519675810306
  | 11 => 1241566816888620842655745024
  | 12 => 79540065375870153025797751299
  | 13 => 20361947251175756669563785183744
  | _ => 0

def C098_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 20600563829970422264017591468800
  | 1 => 20520098941138844496229038293506
  | 2 => 317531620113593533065697756160
  | 3 => 237998808256036935952228155649
  | 4 => 81129952754283178806014269195265
  | 5 => 40724207633065224726036527185920
  | 6 => 79229371440084238100036912130
  | 7 => 20441488539663064126735920529920
  | 8 => 1099511627776
  | 9 => 4294967296
  | 10 => 81210105740308635106896465035776
  | 11 => 621392593720459868089090305
  | 12 => 40644666339874214270189946536193
  | 13 => 1
  | _ => 0

def C098_digit (i j : Fin 14) : ℕ := packedDigit 3 (C098_lowColumnCode j) i.val

private theorem C098_bound_00 : ∀ j : Fin 14, C098_digit 0 j < 5 := by decide +kernel

private theorem C098_bound_01 : ∀ j : Fin 14, C098_digit 1 j < 5 := by decide +kernel

private theorem C098_bound_02 : ∀ j : Fin 14, C098_digit 2 j < 5 := by decide +kernel

private theorem C098_bound_03 : ∀ j : Fin 14, C098_digit 3 j < 5 := by decide +kernel

private theorem C098_bound_04 : ∀ j : Fin 14, C098_digit 4 j < 5 := by decide +kernel

private theorem C098_bound_05 : ∀ j : Fin 14, C098_digit 5 j < 5 := by decide +kernel

private theorem C098_bound_06 : ∀ j : Fin 14, C098_digit 6 j < 5 := by decide +kernel

private theorem C098_bound_07 : ∀ j : Fin 14, C098_digit 7 j < 5 := by decide +kernel

private theorem C098_bound_08 : ∀ j : Fin 14, C098_digit 8 j < 5 := by decide +kernel

private theorem C098_bound_09 : ∀ j : Fin 14, C098_digit 9 j < 5 := by decide +kernel

private theorem C098_bound_10 : ∀ j : Fin 14, C098_digit 10 j < 5 := by decide +kernel

private theorem C098_bound_11 : ∀ j : Fin 14, C098_digit 11 j < 5 := by decide +kernel

private theorem C098_bound_12 : ∀ j : Fin 14, C098_digit 12 j < 5 := by decide +kernel

private theorem C098_bound_13 : ∀ j : Fin 14, C098_digit 13 j < 5 := by decide +kernel

theorem C098_bound : ∀ i j : Fin 14, C098_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C098_bound_00 j
  · exact C098_bound_01 j
  · exact C098_bound_02 j
  · exact C098_bound_03 j
  · exact C098_bound_04 j
  · exact C098_bound_05 j
  · exact C098_bound_06 j
  · exact C098_bound_07 j
  · exact C098_bound_08 j
  · exact C098_bound_09 j
  · exact C098_bound_10 j
  · exact C098_bound_11 j
  · exact C098_bound_12 j
  · exact C098_bound_13 j

private theorem C098_row_00 : pack 256 (C098_digit 0)=C098_rowCode 0 := by decide +kernel

private theorem C098_row_01 : pack 256 (C098_digit 1)=C098_rowCode 1 := by decide +kernel

private theorem C098_row_02 : pack 256 (C098_digit 2)=C098_rowCode 2 := by decide +kernel

private theorem C098_row_03 : pack 256 (C098_digit 3)=C098_rowCode 3 := by decide +kernel

private theorem C098_row_04 : pack 256 (C098_digit 4)=C098_rowCode 4 := by decide +kernel

private theorem C098_row_05 : pack 256 (C098_digit 5)=C098_rowCode 5 := by decide +kernel

private theorem C098_row_06 : pack 256 (C098_digit 6)=C098_rowCode 6 := by decide +kernel

private theorem C098_row_07 : pack 256 (C098_digit 7)=C098_rowCode 7 := by decide +kernel

private theorem C098_row_08 : pack 256 (C098_digit 8)=C098_rowCode 8 := by decide +kernel

private theorem C098_row_09 : pack 256 (C098_digit 9)=C098_rowCode 9 := by decide +kernel

private theorem C098_row_10 : pack 256 (C098_digit 10)=C098_rowCode 10 := by decide +kernel

private theorem C098_row_11 : pack 256 (C098_digit 11)=C098_rowCode 11 := by decide +kernel

private theorem C098_row_12 : pack 256 (C098_digit 12)=C098_rowCode 12 := by decide +kernel

private theorem C098_row_13 : pack 256 (C098_digit 13)=C098_rowCode 13 := by decide +kernel

theorem C098_row_binding : ∀ i : Fin 14, pack 256 (C098_digit i)=C098_rowCode i := by
  intro i
  fin_cases i
  · exact C098_row_00
  · exact C098_row_01
  · exact C098_row_02
  · exact C098_row_03
  · exact C098_row_04
  · exact C098_row_05
  · exact C098_row_06
  · exact C098_row_07
  · exact C098_row_08
  · exact C098_row_09
  · exact C098_row_10
  · exact C098_row_11
  · exact C098_row_12
  · exact C098_row_13

private theorem C098_column_00 : reversePack 256 (fun j : Fin 14 => C098_digit j 0)=C098_columnCode 0 := by decide +kernel

private theorem C098_column_01 : reversePack 256 (fun j : Fin 14 => C098_digit j 1)=C098_columnCode 1 := by decide +kernel

private theorem C098_column_02 : reversePack 256 (fun j : Fin 14 => C098_digit j 2)=C098_columnCode 2 := by decide +kernel

private theorem C098_column_03 : reversePack 256 (fun j : Fin 14 => C098_digit j 3)=C098_columnCode 3 := by decide +kernel

private theorem C098_column_04 : reversePack 256 (fun j : Fin 14 => C098_digit j 4)=C098_columnCode 4 := by decide +kernel

private theorem C098_column_05 : reversePack 256 (fun j : Fin 14 => C098_digit j 5)=C098_columnCode 5 := by decide +kernel

private theorem C098_column_06 : reversePack 256 (fun j : Fin 14 => C098_digit j 6)=C098_columnCode 6 := by decide +kernel

private theorem C098_column_07 : reversePack 256 (fun j : Fin 14 => C098_digit j 7)=C098_columnCode 7 := by decide +kernel

private theorem C098_column_08 : reversePack 256 (fun j : Fin 14 => C098_digit j 8)=C098_columnCode 8 := by decide +kernel

private theorem C098_column_09 : reversePack 256 (fun j : Fin 14 => C098_digit j 9)=C098_columnCode 9 := by decide +kernel

private theorem C098_column_10 : reversePack 256 (fun j : Fin 14 => C098_digit j 10)=C098_columnCode 10 := by decide +kernel

private theorem C098_column_11 : reversePack 256 (fun j : Fin 14 => C098_digit j 11)=C098_columnCode 11 := by decide +kernel

private theorem C098_column_12 : reversePack 256 (fun j : Fin 14 => C098_digit j 12)=C098_columnCode 12 := by decide +kernel

private theorem C098_column_13 : reversePack 256 (fun j : Fin 14 => C098_digit j 13)=C098_columnCode 13 := by decide +kernel

theorem C098_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C098_digit j i)=C098_columnCode i := by
  intro i
  fin_cases i
  · exact C098_column_00
  · exact C098_column_01
  · exact C098_column_02
  · exact C098_column_03
  · exact C098_column_04
  · exact C098_column_05
  · exact C098_column_06
  · exact C098_column_07
  · exact C098_column_08
  · exact C098_column_09
  · exact C098_column_10
  · exact C098_column_11
  · exact C098_column_12
  · exact C098_column_13

def C098_data : PackedData 14 5 256 where
  raw := C098_digit
  digit_lt := C098_bound
  rowCode := C098_rowCode
  columnCode := C098_columnCode
  row_binding := C098_row_binding
  column_binding := C098_column_binding

def C101_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 2503035887684
  | 1 => 1391988885529
  | 2 => 1110283141656
  | 3 => 1342454501459
  | 4 => 623173322444
  | 5 => 163482538264
  | 6 => 69131413196
  | 7 => 73089955905
  | 8 => 1264868657188
  | 9 => 95062078539
  | 10 => 17255993874
  | 11 => 1137114653986
  | 12 => 2491518325384
  | 13 => 640391594532
  | _ => 0

def C101_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 81130259816718923223599752937732
  | 1 => 81210106939808024386858121364224
  | 2 => 159694269790253444761548488705
  | 3 => 20362257954630206083155514950656
  | 4 => 81209486770233724523606884746242
  | 5 => 79541274301545374290504843521
  | 6 => 81447791427332371219614491869188
  | 7 => 40565443017748917837893445091332
  | 8 => 40723589862489990522782456348928
  | 9 => 61084913317387271062737838408449
  | 10 => 81130566869673327449535963856899
  | 11 => 40724515904445233816743505363459
  | 12 => 20599322258468060086610874598404
  | 13 => 20599941223765263952610624406020
  | _ => 0

def C101_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 81129947909079972106951133955076
  | 1 => 20520098945805654571909269029890
  | 2 => 237685715358222676275520143362
  | 3 => 61005994625789587934764618482434
  | 4 => 81209798677891193877856656556289
  | 5 => 238922432360073901481000108544
  | 6 => 81209798668428159409131572166912
  | 7 => 20282723938531870806439630995712
  | 8 => 81446555900367233677462027305474
  | 9 => 60926768890497907973656525603072
  | 10 => 40723276746035541098287568388096
  | 11 => 40882972224714791312040594243586
  | 12 => 79848346200828101891582985220
  | 13 => 81446552292479313387809017037057
  | _ => 0

def C101_digit (i j : Fin 14) : ℕ := packedDigit 3 (C101_lowColumnCode j) i.val

private theorem C101_bound_00 : ∀ j : Fin 14, C101_digit 0 j < 5 := by decide +kernel

private theorem C101_bound_01 : ∀ j : Fin 14, C101_digit 1 j < 5 := by decide +kernel

private theorem C101_bound_02 : ∀ j : Fin 14, C101_digit 2 j < 5 := by decide +kernel

private theorem C101_bound_03 : ∀ j : Fin 14, C101_digit 3 j < 5 := by decide +kernel

private theorem C101_bound_04 : ∀ j : Fin 14, C101_digit 4 j < 5 := by decide +kernel

private theorem C101_bound_05 : ∀ j : Fin 14, C101_digit 5 j < 5 := by decide +kernel

private theorem C101_bound_06 : ∀ j : Fin 14, C101_digit 6 j < 5 := by decide +kernel

private theorem C101_bound_07 : ∀ j : Fin 14, C101_digit 7 j < 5 := by decide +kernel

private theorem C101_bound_08 : ∀ j : Fin 14, C101_digit 8 j < 5 := by decide +kernel

private theorem C101_bound_09 : ∀ j : Fin 14, C101_digit 9 j < 5 := by decide +kernel

private theorem C101_bound_10 : ∀ j : Fin 14, C101_digit 10 j < 5 := by decide +kernel

private theorem C101_bound_11 : ∀ j : Fin 14, C101_digit 11 j < 5 := by decide +kernel

private theorem C101_bound_12 : ∀ j : Fin 14, C101_digit 12 j < 5 := by decide +kernel

private theorem C101_bound_13 : ∀ j : Fin 14, C101_digit 13 j < 5 := by decide +kernel

theorem C101_bound : ∀ i j : Fin 14, C101_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C101_bound_00 j
  · exact C101_bound_01 j
  · exact C101_bound_02 j
  · exact C101_bound_03 j
  · exact C101_bound_04 j
  · exact C101_bound_05 j
  · exact C101_bound_06 j
  · exact C101_bound_07 j
  · exact C101_bound_08 j
  · exact C101_bound_09 j
  · exact C101_bound_10 j
  · exact C101_bound_11 j
  · exact C101_bound_12 j
  · exact C101_bound_13 j

private theorem C101_row_00 : pack 256 (C101_digit 0)=C101_rowCode 0 := by decide +kernel

private theorem C101_row_01 : pack 256 (C101_digit 1)=C101_rowCode 1 := by decide +kernel

private theorem C101_row_02 : pack 256 (C101_digit 2)=C101_rowCode 2 := by decide +kernel

private theorem C101_row_03 : pack 256 (C101_digit 3)=C101_rowCode 3 := by decide +kernel

private theorem C101_row_04 : pack 256 (C101_digit 4)=C101_rowCode 4 := by decide +kernel

private theorem C101_row_05 : pack 256 (C101_digit 5)=C101_rowCode 5 := by decide +kernel

private theorem C101_row_06 : pack 256 (C101_digit 6)=C101_rowCode 6 := by decide +kernel

private theorem C101_row_07 : pack 256 (C101_digit 7)=C101_rowCode 7 := by decide +kernel

private theorem C101_row_08 : pack 256 (C101_digit 8)=C101_rowCode 8 := by decide +kernel

private theorem C101_row_09 : pack 256 (C101_digit 9)=C101_rowCode 9 := by decide +kernel

private theorem C101_row_10 : pack 256 (C101_digit 10)=C101_rowCode 10 := by decide +kernel

private theorem C101_row_11 : pack 256 (C101_digit 11)=C101_rowCode 11 := by decide +kernel

private theorem C101_row_12 : pack 256 (C101_digit 12)=C101_rowCode 12 := by decide +kernel

private theorem C101_row_13 : pack 256 (C101_digit 13)=C101_rowCode 13 := by decide +kernel

theorem C101_row_binding : ∀ i : Fin 14, pack 256 (C101_digit i)=C101_rowCode i := by
  intro i
  fin_cases i
  · exact C101_row_00
  · exact C101_row_01
  · exact C101_row_02
  · exact C101_row_03
  · exact C101_row_04
  · exact C101_row_05
  · exact C101_row_06
  · exact C101_row_07
  · exact C101_row_08
  · exact C101_row_09
  · exact C101_row_10
  · exact C101_row_11
  · exact C101_row_12
  · exact C101_row_13

private theorem C101_column_00 : reversePack 256 (fun j : Fin 14 => C101_digit j 0)=C101_columnCode 0 := by decide +kernel

private theorem C101_column_01 : reversePack 256 (fun j : Fin 14 => C101_digit j 1)=C101_columnCode 1 := by decide +kernel

private theorem C101_column_02 : reversePack 256 (fun j : Fin 14 => C101_digit j 2)=C101_columnCode 2 := by decide +kernel

private theorem C101_column_03 : reversePack 256 (fun j : Fin 14 => C101_digit j 3)=C101_columnCode 3 := by decide +kernel

private theorem C101_column_04 : reversePack 256 (fun j : Fin 14 => C101_digit j 4)=C101_columnCode 4 := by decide +kernel

private theorem C101_column_05 : reversePack 256 (fun j : Fin 14 => C101_digit j 5)=C101_columnCode 5 := by decide +kernel

private theorem C101_column_06 : reversePack 256 (fun j : Fin 14 => C101_digit j 6)=C101_columnCode 6 := by decide +kernel

private theorem C101_column_07 : reversePack 256 (fun j : Fin 14 => C101_digit j 7)=C101_columnCode 7 := by decide +kernel

private theorem C101_column_08 : reversePack 256 (fun j : Fin 14 => C101_digit j 8)=C101_columnCode 8 := by decide +kernel

private theorem C101_column_09 : reversePack 256 (fun j : Fin 14 => C101_digit j 9)=C101_columnCode 9 := by decide +kernel

private theorem C101_column_10 : reversePack 256 (fun j : Fin 14 => C101_digit j 10)=C101_columnCode 10 := by decide +kernel

private theorem C101_column_11 : reversePack 256 (fun j : Fin 14 => C101_digit j 11)=C101_columnCode 11 := by decide +kernel

private theorem C101_column_12 : reversePack 256 (fun j : Fin 14 => C101_digit j 12)=C101_columnCode 12 := by decide +kernel

private theorem C101_column_13 : reversePack 256 (fun j : Fin 14 => C101_digit j 13)=C101_columnCode 13 := by decide +kernel

theorem C101_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C101_digit j i)=C101_columnCode i := by
  intro i
  fin_cases i
  · exact C101_column_00
  · exact C101_column_01
  · exact C101_column_02
  · exact C101_column_03
  · exact C101_column_04
  · exact C101_column_05
  · exact C101_column_06
  · exact C101_column_07
  · exact C101_column_08
  · exact C101_column_09
  · exact C101_column_10
  · exact C101_column_11
  · exact C101_column_12
  · exact C101_column_13

def C101_data : PackedData 14 5 256 where
  raw := C101_digit
  digit_lt := C101_bound
  rowCode := C101_rowCode
  columnCode := C101_columnCode
  row_binding := C101_row_binding
  column_binding := C101_column_binding

end SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedCaches11
