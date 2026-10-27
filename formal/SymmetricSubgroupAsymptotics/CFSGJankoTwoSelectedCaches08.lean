import SymmetricSubgroupAsymptotics.MatrixKroneckerProductReflection
import Mathlib.Tactic.FinCases

/-! Literal14/F5 selected caches; digit bounds and both pack bindings are independently kernel checked. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedCaches08
open MatrixKroneckerProductReflection MatrixKroneckerDotReflection
open MatrixNaturalRowDotReflection SmallNaturalMatrixProductReflection

def C077_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 94781641249
  | 1 => 2503052694553
  | 2 => 773119281152
  | 3 => 2304693350425
  | 4 => 755918438400
  | 5 => 1666447575040
  | 6 => 1273457803264
  | 7 => 551903313920
  | 8 => 2199079878656
  | 9 => 549789434914
  | 10 => 274886295552
  | 11 => 2267744960576
  | 12 => 2474974904320
  | 13 => 1649292607488
  | _ => 0

def C077_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 9444732965739307204865
  | 1 => 18889465931478631187204
  | 2 => 309485009821345068724781056
  | 3 => 9444732970137337201153
  | 4 => 288230376202043649
  | 5 => 1237949484018346014239883778
  | 6 => 1099561960451
  | 7 => 81129952735375121731604197934083
  | 8 => 20282409613151743621907703988481
  | 9 => 50331906
  | 10 => 79228162514409015731606782720
  | 11 => 1128098997338883
  | 12 => 317226970770157716922454705153
  | 13 => 61165379405847580085502200579072
  | _ => 0

def C077_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 20599323467394024378282811785472
  | 1 => 20520096513805651994383212545028
  | 2 => 4835703279585516117426945
  | 3 => 20520094105417120136976933323012
  | 4 => 562949953422081
  | 5 => 4835703350516110736883715
  | 6 => 33817090
  | 7 => 18889465931478614409217
  | 8 => 847723465015300
  | 9 => 40881734275248930917873470144513
  | 10 => 1125899906843648
  | 11 => 309485083608602838539698436
  | 12 => 16778244
  | 13 => 1126999418470403
  | _ => 0

def C077_digit (i j : Fin 14) : ℕ := packedDigit 3 (C077_lowColumnCode j) i.val

private theorem C077_bound_00 : ∀ j : Fin 14, C077_digit 0 j < 5 := by decide +kernel

private theorem C077_bound_01 : ∀ j : Fin 14, C077_digit 1 j < 5 := by decide +kernel

private theorem C077_bound_02 : ∀ j : Fin 14, C077_digit 2 j < 5 := by decide +kernel

private theorem C077_bound_03 : ∀ j : Fin 14, C077_digit 3 j < 5 := by decide +kernel

private theorem C077_bound_04 : ∀ j : Fin 14, C077_digit 4 j < 5 := by decide +kernel

private theorem C077_bound_05 : ∀ j : Fin 14, C077_digit 5 j < 5 := by decide +kernel

private theorem C077_bound_06 : ∀ j : Fin 14, C077_digit 6 j < 5 := by decide +kernel

private theorem C077_bound_07 : ∀ j : Fin 14, C077_digit 7 j < 5 := by decide +kernel

private theorem C077_bound_08 : ∀ j : Fin 14, C077_digit 8 j < 5 := by decide +kernel

private theorem C077_bound_09 : ∀ j : Fin 14, C077_digit 9 j < 5 := by decide +kernel

private theorem C077_bound_10 : ∀ j : Fin 14, C077_digit 10 j < 5 := by decide +kernel

private theorem C077_bound_11 : ∀ j : Fin 14, C077_digit 11 j < 5 := by decide +kernel

private theorem C077_bound_12 : ∀ j : Fin 14, C077_digit 12 j < 5 := by decide +kernel

private theorem C077_bound_13 : ∀ j : Fin 14, C077_digit 13 j < 5 := by decide +kernel

theorem C077_bound : ∀ i j : Fin 14, C077_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C077_bound_00 j
  · exact C077_bound_01 j
  · exact C077_bound_02 j
  · exact C077_bound_03 j
  · exact C077_bound_04 j
  · exact C077_bound_05 j
  · exact C077_bound_06 j
  · exact C077_bound_07 j
  · exact C077_bound_08 j
  · exact C077_bound_09 j
  · exact C077_bound_10 j
  · exact C077_bound_11 j
  · exact C077_bound_12 j
  · exact C077_bound_13 j

private theorem C077_row_00 : pack 256 (C077_digit 0)=C077_rowCode 0 := by decide +kernel

private theorem C077_row_01 : pack 256 (C077_digit 1)=C077_rowCode 1 := by decide +kernel

private theorem C077_row_02 : pack 256 (C077_digit 2)=C077_rowCode 2 := by decide +kernel

private theorem C077_row_03 : pack 256 (C077_digit 3)=C077_rowCode 3 := by decide +kernel

private theorem C077_row_04 : pack 256 (C077_digit 4)=C077_rowCode 4 := by decide +kernel

private theorem C077_row_05 : pack 256 (C077_digit 5)=C077_rowCode 5 := by decide +kernel

private theorem C077_row_06 : pack 256 (C077_digit 6)=C077_rowCode 6 := by decide +kernel

private theorem C077_row_07 : pack 256 (C077_digit 7)=C077_rowCode 7 := by decide +kernel

private theorem C077_row_08 : pack 256 (C077_digit 8)=C077_rowCode 8 := by decide +kernel

private theorem C077_row_09 : pack 256 (C077_digit 9)=C077_rowCode 9 := by decide +kernel

private theorem C077_row_10 : pack 256 (C077_digit 10)=C077_rowCode 10 := by decide +kernel

private theorem C077_row_11 : pack 256 (C077_digit 11)=C077_rowCode 11 := by decide +kernel

private theorem C077_row_12 : pack 256 (C077_digit 12)=C077_rowCode 12 := by decide +kernel

private theorem C077_row_13 : pack 256 (C077_digit 13)=C077_rowCode 13 := by decide +kernel

theorem C077_row_binding : ∀ i : Fin 14, pack 256 (C077_digit i)=C077_rowCode i := by
  intro i
  fin_cases i
  · exact C077_row_00
  · exact C077_row_01
  · exact C077_row_02
  · exact C077_row_03
  · exact C077_row_04
  · exact C077_row_05
  · exact C077_row_06
  · exact C077_row_07
  · exact C077_row_08
  · exact C077_row_09
  · exact C077_row_10
  · exact C077_row_11
  · exact C077_row_12
  · exact C077_row_13

private theorem C077_column_00 : reversePack 256 (fun j : Fin 14 => C077_digit j 0)=C077_columnCode 0 := by decide +kernel

private theorem C077_column_01 : reversePack 256 (fun j : Fin 14 => C077_digit j 1)=C077_columnCode 1 := by decide +kernel

private theorem C077_column_02 : reversePack 256 (fun j : Fin 14 => C077_digit j 2)=C077_columnCode 2 := by decide +kernel

private theorem C077_column_03 : reversePack 256 (fun j : Fin 14 => C077_digit j 3)=C077_columnCode 3 := by decide +kernel

private theorem C077_column_04 : reversePack 256 (fun j : Fin 14 => C077_digit j 4)=C077_columnCode 4 := by decide +kernel

private theorem C077_column_05 : reversePack 256 (fun j : Fin 14 => C077_digit j 5)=C077_columnCode 5 := by decide +kernel

private theorem C077_column_06 : reversePack 256 (fun j : Fin 14 => C077_digit j 6)=C077_columnCode 6 := by decide +kernel

private theorem C077_column_07 : reversePack 256 (fun j : Fin 14 => C077_digit j 7)=C077_columnCode 7 := by decide +kernel

private theorem C077_column_08 : reversePack 256 (fun j : Fin 14 => C077_digit j 8)=C077_columnCode 8 := by decide +kernel

private theorem C077_column_09 : reversePack 256 (fun j : Fin 14 => C077_digit j 9)=C077_columnCode 9 := by decide +kernel

private theorem C077_column_10 : reversePack 256 (fun j : Fin 14 => C077_digit j 10)=C077_columnCode 10 := by decide +kernel

private theorem C077_column_11 : reversePack 256 (fun j : Fin 14 => C077_digit j 11)=C077_columnCode 11 := by decide +kernel

private theorem C077_column_12 : reversePack 256 (fun j : Fin 14 => C077_digit j 12)=C077_columnCode 12 := by decide +kernel

private theorem C077_column_13 : reversePack 256 (fun j : Fin 14 => C077_digit j 13)=C077_columnCode 13 := by decide +kernel

theorem C077_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C077_digit j i)=C077_columnCode i := by
  intro i
  fin_cases i
  · exact C077_column_00
  · exact C077_column_01
  · exact C077_column_02
  · exact C077_column_03
  · exact C077_column_04
  · exact C077_column_05
  · exact C077_column_06
  · exact C077_column_07
  · exact C077_column_08
  · exact C077_column_09
  · exact C077_column_10
  · exact C077_column_11
  · exact C077_column_12
  · exact C077_column_13

def C077_data : PackedData 14 5 256 where
  raw := C077_digit
  digit_lt := C077_bound
  rowCode := C077_rowCode
  columnCode := C077_columnCode
  row_binding := C077_row_binding
  column_binding := C077_column_binding

def C078_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 1729933415961
  | 1 => 310597525514
  | 2 => 1748091652124
  | 3 => 2336468500480
  | 4 => 1892372295705
  | 5 => 2199079878656
  | 6 => 1666447575040
  | 7 => 274886295552
  | 8 => 1273457803264
  | 9 => 551903313920
  | 10 => 549789434914
  | 11 => 1649292607488
  | 12 => 2267744960576
  | 13 => 2474974904320
  | _ => 0

def C078_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 2417851639229262644642305
  | 1 => 4835703278458529583923459
  | 2 => 79228162514264337593543950336
  | 3 => 2417851640355158256517123
  | 4 => 18889465931491466019329
  | 5 => 316915067908696579645410313218
  | 6 => 281487861613316
  | 7 => 80466102553837951547475165184
  | 8 => 311902861460577634199142656
  | 9 => 12884902401
  | 10 => 20282409613133296877842551013635
  | 11 => 73787539261971694593
  | 12 => 81208866577158127751919038432257
  | 13 => 81447480733378283515851523162115
  | _ => 0

def C078_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 20520097722731470482012968648963
  | 1 => 40644047379336341301412407542784
  | 2 => 81367327756797560177410066022659
  | 3 => 844424930132484
  | 4 => 20520094105417119574026979902211
  | 5 => 847723465015300
  | 6 => 4835703350516110736883715
  | 7 => 1125899906843648
  | 8 => 33817090
  | 9 => 18889465931478614409217
  | 10 => 40881734275248930917873470144513
  | 11 => 1126999418470403
  | 12 => 309485083608602838539698436
  | 13 => 16778244
  | _ => 0

def C078_digit (i j : Fin 14) : ℕ := packedDigit 3 (C078_lowColumnCode j) i.val

private theorem C078_bound_00 : ∀ j : Fin 14, C078_digit 0 j < 5 := by decide +kernel

private theorem C078_bound_01 : ∀ j : Fin 14, C078_digit 1 j < 5 := by decide +kernel

private theorem C078_bound_02 : ∀ j : Fin 14, C078_digit 2 j < 5 := by decide +kernel

private theorem C078_bound_03 : ∀ j : Fin 14, C078_digit 3 j < 5 := by decide +kernel

private theorem C078_bound_04 : ∀ j : Fin 14, C078_digit 4 j < 5 := by decide +kernel

private theorem C078_bound_05 : ∀ j : Fin 14, C078_digit 5 j < 5 := by decide +kernel

private theorem C078_bound_06 : ∀ j : Fin 14, C078_digit 6 j < 5 := by decide +kernel

private theorem C078_bound_07 : ∀ j : Fin 14, C078_digit 7 j < 5 := by decide +kernel

private theorem C078_bound_08 : ∀ j : Fin 14, C078_digit 8 j < 5 := by decide +kernel

private theorem C078_bound_09 : ∀ j : Fin 14, C078_digit 9 j < 5 := by decide +kernel

private theorem C078_bound_10 : ∀ j : Fin 14, C078_digit 10 j < 5 := by decide +kernel

private theorem C078_bound_11 : ∀ j : Fin 14, C078_digit 11 j < 5 := by decide +kernel

private theorem C078_bound_12 : ∀ j : Fin 14, C078_digit 12 j < 5 := by decide +kernel

private theorem C078_bound_13 : ∀ j : Fin 14, C078_digit 13 j < 5 := by decide +kernel

theorem C078_bound : ∀ i j : Fin 14, C078_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C078_bound_00 j
  · exact C078_bound_01 j
  · exact C078_bound_02 j
  · exact C078_bound_03 j
  · exact C078_bound_04 j
  · exact C078_bound_05 j
  · exact C078_bound_06 j
  · exact C078_bound_07 j
  · exact C078_bound_08 j
  · exact C078_bound_09 j
  · exact C078_bound_10 j
  · exact C078_bound_11 j
  · exact C078_bound_12 j
  · exact C078_bound_13 j

private theorem C078_row_00 : pack 256 (C078_digit 0)=C078_rowCode 0 := by decide +kernel

private theorem C078_row_01 : pack 256 (C078_digit 1)=C078_rowCode 1 := by decide +kernel

private theorem C078_row_02 : pack 256 (C078_digit 2)=C078_rowCode 2 := by decide +kernel

private theorem C078_row_03 : pack 256 (C078_digit 3)=C078_rowCode 3 := by decide +kernel

private theorem C078_row_04 : pack 256 (C078_digit 4)=C078_rowCode 4 := by decide +kernel

private theorem C078_row_05 : pack 256 (C078_digit 5)=C078_rowCode 5 := by decide +kernel

private theorem C078_row_06 : pack 256 (C078_digit 6)=C078_rowCode 6 := by decide +kernel

private theorem C078_row_07 : pack 256 (C078_digit 7)=C078_rowCode 7 := by decide +kernel

private theorem C078_row_08 : pack 256 (C078_digit 8)=C078_rowCode 8 := by decide +kernel

private theorem C078_row_09 : pack 256 (C078_digit 9)=C078_rowCode 9 := by decide +kernel

private theorem C078_row_10 : pack 256 (C078_digit 10)=C078_rowCode 10 := by decide +kernel

private theorem C078_row_11 : pack 256 (C078_digit 11)=C078_rowCode 11 := by decide +kernel

private theorem C078_row_12 : pack 256 (C078_digit 12)=C078_rowCode 12 := by decide +kernel

private theorem C078_row_13 : pack 256 (C078_digit 13)=C078_rowCode 13 := by decide +kernel

theorem C078_row_binding : ∀ i : Fin 14, pack 256 (C078_digit i)=C078_rowCode i := by
  intro i
  fin_cases i
  · exact C078_row_00
  · exact C078_row_01
  · exact C078_row_02
  · exact C078_row_03
  · exact C078_row_04
  · exact C078_row_05
  · exact C078_row_06
  · exact C078_row_07
  · exact C078_row_08
  · exact C078_row_09
  · exact C078_row_10
  · exact C078_row_11
  · exact C078_row_12
  · exact C078_row_13

private theorem C078_column_00 : reversePack 256 (fun j : Fin 14 => C078_digit j 0)=C078_columnCode 0 := by decide +kernel

private theorem C078_column_01 : reversePack 256 (fun j : Fin 14 => C078_digit j 1)=C078_columnCode 1 := by decide +kernel

private theorem C078_column_02 : reversePack 256 (fun j : Fin 14 => C078_digit j 2)=C078_columnCode 2 := by decide +kernel

private theorem C078_column_03 : reversePack 256 (fun j : Fin 14 => C078_digit j 3)=C078_columnCode 3 := by decide +kernel

private theorem C078_column_04 : reversePack 256 (fun j : Fin 14 => C078_digit j 4)=C078_columnCode 4 := by decide +kernel

private theorem C078_column_05 : reversePack 256 (fun j : Fin 14 => C078_digit j 5)=C078_columnCode 5 := by decide +kernel

private theorem C078_column_06 : reversePack 256 (fun j : Fin 14 => C078_digit j 6)=C078_columnCode 6 := by decide +kernel

private theorem C078_column_07 : reversePack 256 (fun j : Fin 14 => C078_digit j 7)=C078_columnCode 7 := by decide +kernel

private theorem C078_column_08 : reversePack 256 (fun j : Fin 14 => C078_digit j 8)=C078_columnCode 8 := by decide +kernel

private theorem C078_column_09 : reversePack 256 (fun j : Fin 14 => C078_digit j 9)=C078_columnCode 9 := by decide +kernel

private theorem C078_column_10 : reversePack 256 (fun j : Fin 14 => C078_digit j 10)=C078_columnCode 10 := by decide +kernel

private theorem C078_column_11 : reversePack 256 (fun j : Fin 14 => C078_digit j 11)=C078_columnCode 11 := by decide +kernel

private theorem C078_column_12 : reversePack 256 (fun j : Fin 14 => C078_digit j 12)=C078_columnCode 12 := by decide +kernel

private theorem C078_column_13 : reversePack 256 (fun j : Fin 14 => C078_digit j 13)=C078_columnCode 13 := by decide +kernel

theorem C078_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C078_digit j i)=C078_columnCode i := by
  intro i
  fin_cases i
  · exact C078_column_00
  · exact C078_column_01
  · exact C078_column_02
  · exact C078_column_03
  · exact C078_column_04
  · exact C078_column_05
  · exact C078_column_06
  · exact C078_column_07
  · exact C078_column_08
  · exact C078_column_09
  · exact C078_column_10
  · exact C078_column_11
  · exact C078_column_12
  · exact C078_column_13

def C078_data : PackedData 14 5 256 where
  raw := C078_digit
  digit_lt := C078_bound
  rowCode := C078_rowCode
  columnCode := C078_columnCode
  row_binding := C078_row_binding
  column_binding := C078_column_binding

def C079_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 1649559781578
  | 1 => 235288929945
  | 2 => 1172526178432
  | 3 => 275987319004
  | 4 => 2477172818048
  | 5 => 1963245449433
  | 6 => 1236954841280
  | 7 => 704379193472
  | 8 => 1305670062080
  | 9 => 627065225216
  | 10 => 550846464064
  | 11 => 1653604451618
  | 12 => 2267744960576
  | 13 => 2474974904320
  | _ => 0

def C079_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 618970019642691237028299010
  | 1 => 1237940039285383573484339969
  | 2 => 80467311479514295417799049731
  | 3 => 618970019930920513668383488
  | 4 => 18446747372311675396
  | 5 => 317845940790016579842001272833
  | 6 => 72060892572812291
  | 7 => 80466102553694400404535640579
  | 8 => 620178945462306978565980161
  | 9 => 3298534883586
  | 10 => 20283648752616775423262273569536
  | 11 => 4722510602455767581440
  | 12 => 81208866581898797431026645795584
  | 13 => 81447480733378355290875300544515
  | _ => 0

def C079_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 40644975843755198914561656750083
  | 1 => 20520716697436586729822597874432
  | 2 => 618979519715888097935753474
  | 3 => 81368256211771683417445107762176
  | 4 => 618970074982925657163432964
  | 5 => 20521022560391244221436989277187
  | 6 => 928455066358086303546868226
  | 7 => 623805778334001419268522497
  | 8 => 4722366482869645214466
  | 9 => 65793
  | 10 => 309485083608322463091392513
  | 11 => 40882972215306664168122052771843
  | 12 => 309485083608602838539698436
  | 13 => 16778244
  | _ => 0

def C079_digit (i j : Fin 14) : ℕ := packedDigit 3 (C079_lowColumnCode j) i.val

private theorem C079_bound_00 : ∀ j : Fin 14, C079_digit 0 j < 5 := by decide +kernel

private theorem C079_bound_01 : ∀ j : Fin 14, C079_digit 1 j < 5 := by decide +kernel

private theorem C079_bound_02 : ∀ j : Fin 14, C079_digit 2 j < 5 := by decide +kernel

private theorem C079_bound_03 : ∀ j : Fin 14, C079_digit 3 j < 5 := by decide +kernel

private theorem C079_bound_04 : ∀ j : Fin 14, C079_digit 4 j < 5 := by decide +kernel

private theorem C079_bound_05 : ∀ j : Fin 14, C079_digit 5 j < 5 := by decide +kernel

private theorem C079_bound_06 : ∀ j : Fin 14, C079_digit 6 j < 5 := by decide +kernel

private theorem C079_bound_07 : ∀ j : Fin 14, C079_digit 7 j < 5 := by decide +kernel

private theorem C079_bound_08 : ∀ j : Fin 14, C079_digit 8 j < 5 := by decide +kernel

private theorem C079_bound_09 : ∀ j : Fin 14, C079_digit 9 j < 5 := by decide +kernel

private theorem C079_bound_10 : ∀ j : Fin 14, C079_digit 10 j < 5 := by decide +kernel

private theorem C079_bound_11 : ∀ j : Fin 14, C079_digit 11 j < 5 := by decide +kernel

private theorem C079_bound_12 : ∀ j : Fin 14, C079_digit 12 j < 5 := by decide +kernel

private theorem C079_bound_13 : ∀ j : Fin 14, C079_digit 13 j < 5 := by decide +kernel

theorem C079_bound : ∀ i j : Fin 14, C079_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C079_bound_00 j
  · exact C079_bound_01 j
  · exact C079_bound_02 j
  · exact C079_bound_03 j
  · exact C079_bound_04 j
  · exact C079_bound_05 j
  · exact C079_bound_06 j
  · exact C079_bound_07 j
  · exact C079_bound_08 j
  · exact C079_bound_09 j
  · exact C079_bound_10 j
  · exact C079_bound_11 j
  · exact C079_bound_12 j
  · exact C079_bound_13 j

private theorem C079_row_00 : pack 256 (C079_digit 0)=C079_rowCode 0 := by decide +kernel

private theorem C079_row_01 : pack 256 (C079_digit 1)=C079_rowCode 1 := by decide +kernel

private theorem C079_row_02 : pack 256 (C079_digit 2)=C079_rowCode 2 := by decide +kernel

private theorem C079_row_03 : pack 256 (C079_digit 3)=C079_rowCode 3 := by decide +kernel

private theorem C079_row_04 : pack 256 (C079_digit 4)=C079_rowCode 4 := by decide +kernel

private theorem C079_row_05 : pack 256 (C079_digit 5)=C079_rowCode 5 := by decide +kernel

private theorem C079_row_06 : pack 256 (C079_digit 6)=C079_rowCode 6 := by decide +kernel

private theorem C079_row_07 : pack 256 (C079_digit 7)=C079_rowCode 7 := by decide +kernel

private theorem C079_row_08 : pack 256 (C079_digit 8)=C079_rowCode 8 := by decide +kernel

private theorem C079_row_09 : pack 256 (C079_digit 9)=C079_rowCode 9 := by decide +kernel

private theorem C079_row_10 : pack 256 (C079_digit 10)=C079_rowCode 10 := by decide +kernel

private theorem C079_row_11 : pack 256 (C079_digit 11)=C079_rowCode 11 := by decide +kernel

private theorem C079_row_12 : pack 256 (C079_digit 12)=C079_rowCode 12 := by decide +kernel

private theorem C079_row_13 : pack 256 (C079_digit 13)=C079_rowCode 13 := by decide +kernel

theorem C079_row_binding : ∀ i : Fin 14, pack 256 (C079_digit i)=C079_rowCode i := by
  intro i
  fin_cases i
  · exact C079_row_00
  · exact C079_row_01
  · exact C079_row_02
  · exact C079_row_03
  · exact C079_row_04
  · exact C079_row_05
  · exact C079_row_06
  · exact C079_row_07
  · exact C079_row_08
  · exact C079_row_09
  · exact C079_row_10
  · exact C079_row_11
  · exact C079_row_12
  · exact C079_row_13

private theorem C079_column_00 : reversePack 256 (fun j : Fin 14 => C079_digit j 0)=C079_columnCode 0 := by decide +kernel

private theorem C079_column_01 : reversePack 256 (fun j : Fin 14 => C079_digit j 1)=C079_columnCode 1 := by decide +kernel

private theorem C079_column_02 : reversePack 256 (fun j : Fin 14 => C079_digit j 2)=C079_columnCode 2 := by decide +kernel

private theorem C079_column_03 : reversePack 256 (fun j : Fin 14 => C079_digit j 3)=C079_columnCode 3 := by decide +kernel

private theorem C079_column_04 : reversePack 256 (fun j : Fin 14 => C079_digit j 4)=C079_columnCode 4 := by decide +kernel

private theorem C079_column_05 : reversePack 256 (fun j : Fin 14 => C079_digit j 5)=C079_columnCode 5 := by decide +kernel

private theorem C079_column_06 : reversePack 256 (fun j : Fin 14 => C079_digit j 6)=C079_columnCode 6 := by decide +kernel

private theorem C079_column_07 : reversePack 256 (fun j : Fin 14 => C079_digit j 7)=C079_columnCode 7 := by decide +kernel

private theorem C079_column_08 : reversePack 256 (fun j : Fin 14 => C079_digit j 8)=C079_columnCode 8 := by decide +kernel

private theorem C079_column_09 : reversePack 256 (fun j : Fin 14 => C079_digit j 9)=C079_columnCode 9 := by decide +kernel

private theorem C079_column_10 : reversePack 256 (fun j : Fin 14 => C079_digit j 10)=C079_columnCode 10 := by decide +kernel

private theorem C079_column_11 : reversePack 256 (fun j : Fin 14 => C079_digit j 11)=C079_columnCode 11 := by decide +kernel

private theorem C079_column_12 : reversePack 256 (fun j : Fin 14 => C079_digit j 12)=C079_columnCode 12 := by decide +kernel

private theorem C079_column_13 : reversePack 256 (fun j : Fin 14 => C079_digit j 13)=C079_columnCode 13 := by decide +kernel

theorem C079_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C079_digit j i)=C079_columnCode i := by
  intro i
  fin_cases i
  · exact C079_column_00
  · exact C079_column_01
  · exact C079_column_02
  · exact C079_column_03
  · exact C079_column_04
  · exact C079_column_05
  · exact C079_column_06
  · exact C079_column_07
  · exact C079_column_08
  · exact C079_column_09
  · exact C079_column_10
  · exact C079_column_11
  · exact C079_column_12
  · exact C079_column_13

def C079_data : PackedData 14 5 256 where
  raw := C079_digit
  digit_lt := C079_bound
  rowCode := C079_rowCode
  columnCode := C079_columnCode
  row_binding := C079_row_binding
  column_binding := C079_column_binding

def C080_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 2423771698314
  | 1 => 1126896632009
  | 2 => 2226211622916
  | 3 => 2201196008209
  | 4 => 73073169041
  | 5 => 1236954841280
  | 6 => 1305670062080
  | 7 => 627065225216
  | 8 => 1963245449433
  | 9 => 550846464064
  | 10 => 704379193472
  | 11 => 2267744960576
  | 12 => 2474974904320
  | 13 => 1653604451618
  | _ => 0

def C080_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 40564819207321787591972524130562
  | 1 => 81129638414662021928018757288193
  | 2 => 81129950322245848988514045133570
  | 3 => 40564824043006619306415513141250
  | 4 => 55340513700417175553
  | 5 => 60848470396661221429681831740418
  | 6 => 1208981159846850303557891
  | 7 => 81129950317541929248627188040192
  | 8 => 40564819212062600818924468830212
  | 9 => 55340232221128786946
  | 10 => 81208866581917099492564246003969
  | 11 => 2417925498263147225744130
  | 12 => 317224552992377805218374483971
  | 13 => 61165380614754952954953859334660
  | _ => 0

def C080_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 40644668762448363253089676952324
  | 1 => 20362566221269258393602995978242
  | 2 => 81129638419384605713968453058564
  | 3 => 20442105082423011936128638910468
  | 4 => 20441486112348029015969117503744
  | 5 => 928455066358086303546868226
  | 6 => 4722366482869645214466
  | 7 => 65793
  | 8 => 20521022560391244221436989277187
  | 9 => 309485083608322463091392513
  | 10 => 623805778334001419268522497
  | 11 => 309485083608602838539698436
  | 12 => 16778244
  | 13 => 40882972215306664168122052771843
  | _ => 0

def C080_digit (i j : Fin 14) : ℕ := packedDigit 3 (C080_lowColumnCode j) i.val

private theorem C080_bound_00 : ∀ j : Fin 14, C080_digit 0 j < 5 := by decide +kernel

private theorem C080_bound_01 : ∀ j : Fin 14, C080_digit 1 j < 5 := by decide +kernel

private theorem C080_bound_02 : ∀ j : Fin 14, C080_digit 2 j < 5 := by decide +kernel

private theorem C080_bound_03 : ∀ j : Fin 14, C080_digit 3 j < 5 := by decide +kernel

private theorem C080_bound_04 : ∀ j : Fin 14, C080_digit 4 j < 5 := by decide +kernel

private theorem C080_bound_05 : ∀ j : Fin 14, C080_digit 5 j < 5 := by decide +kernel

private theorem C080_bound_06 : ∀ j : Fin 14, C080_digit 6 j < 5 := by decide +kernel

private theorem C080_bound_07 : ∀ j : Fin 14, C080_digit 7 j < 5 := by decide +kernel

private theorem C080_bound_08 : ∀ j : Fin 14, C080_digit 8 j < 5 := by decide +kernel

private theorem C080_bound_09 : ∀ j : Fin 14, C080_digit 9 j < 5 := by decide +kernel

private theorem C080_bound_10 : ∀ j : Fin 14, C080_digit 10 j < 5 := by decide +kernel

private theorem C080_bound_11 : ∀ j : Fin 14, C080_digit 11 j < 5 := by decide +kernel

private theorem C080_bound_12 : ∀ j : Fin 14, C080_digit 12 j < 5 := by decide +kernel

private theorem C080_bound_13 : ∀ j : Fin 14, C080_digit 13 j < 5 := by decide +kernel

theorem C080_bound : ∀ i j : Fin 14, C080_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C080_bound_00 j
  · exact C080_bound_01 j
  · exact C080_bound_02 j
  · exact C080_bound_03 j
  · exact C080_bound_04 j
  · exact C080_bound_05 j
  · exact C080_bound_06 j
  · exact C080_bound_07 j
  · exact C080_bound_08 j
  · exact C080_bound_09 j
  · exact C080_bound_10 j
  · exact C080_bound_11 j
  · exact C080_bound_12 j
  · exact C080_bound_13 j

private theorem C080_row_00 : pack 256 (C080_digit 0)=C080_rowCode 0 := by decide +kernel

private theorem C080_row_01 : pack 256 (C080_digit 1)=C080_rowCode 1 := by decide +kernel

private theorem C080_row_02 : pack 256 (C080_digit 2)=C080_rowCode 2 := by decide +kernel

private theorem C080_row_03 : pack 256 (C080_digit 3)=C080_rowCode 3 := by decide +kernel

private theorem C080_row_04 : pack 256 (C080_digit 4)=C080_rowCode 4 := by decide +kernel

private theorem C080_row_05 : pack 256 (C080_digit 5)=C080_rowCode 5 := by decide +kernel

private theorem C080_row_06 : pack 256 (C080_digit 6)=C080_rowCode 6 := by decide +kernel

private theorem C080_row_07 : pack 256 (C080_digit 7)=C080_rowCode 7 := by decide +kernel

private theorem C080_row_08 : pack 256 (C080_digit 8)=C080_rowCode 8 := by decide +kernel

private theorem C080_row_09 : pack 256 (C080_digit 9)=C080_rowCode 9 := by decide +kernel

private theorem C080_row_10 : pack 256 (C080_digit 10)=C080_rowCode 10 := by decide +kernel

private theorem C080_row_11 : pack 256 (C080_digit 11)=C080_rowCode 11 := by decide +kernel

private theorem C080_row_12 : pack 256 (C080_digit 12)=C080_rowCode 12 := by decide +kernel

private theorem C080_row_13 : pack 256 (C080_digit 13)=C080_rowCode 13 := by decide +kernel

theorem C080_row_binding : ∀ i : Fin 14, pack 256 (C080_digit i)=C080_rowCode i := by
  intro i
  fin_cases i
  · exact C080_row_00
  · exact C080_row_01
  · exact C080_row_02
  · exact C080_row_03
  · exact C080_row_04
  · exact C080_row_05
  · exact C080_row_06
  · exact C080_row_07
  · exact C080_row_08
  · exact C080_row_09
  · exact C080_row_10
  · exact C080_row_11
  · exact C080_row_12
  · exact C080_row_13

private theorem C080_column_00 : reversePack 256 (fun j : Fin 14 => C080_digit j 0)=C080_columnCode 0 := by decide +kernel

private theorem C080_column_01 : reversePack 256 (fun j : Fin 14 => C080_digit j 1)=C080_columnCode 1 := by decide +kernel

private theorem C080_column_02 : reversePack 256 (fun j : Fin 14 => C080_digit j 2)=C080_columnCode 2 := by decide +kernel

private theorem C080_column_03 : reversePack 256 (fun j : Fin 14 => C080_digit j 3)=C080_columnCode 3 := by decide +kernel

private theorem C080_column_04 : reversePack 256 (fun j : Fin 14 => C080_digit j 4)=C080_columnCode 4 := by decide +kernel

private theorem C080_column_05 : reversePack 256 (fun j : Fin 14 => C080_digit j 5)=C080_columnCode 5 := by decide +kernel

private theorem C080_column_06 : reversePack 256 (fun j : Fin 14 => C080_digit j 6)=C080_columnCode 6 := by decide +kernel

private theorem C080_column_07 : reversePack 256 (fun j : Fin 14 => C080_digit j 7)=C080_columnCode 7 := by decide +kernel

private theorem C080_column_08 : reversePack 256 (fun j : Fin 14 => C080_digit j 8)=C080_columnCode 8 := by decide +kernel

private theorem C080_column_09 : reversePack 256 (fun j : Fin 14 => C080_digit j 9)=C080_columnCode 9 := by decide +kernel

private theorem C080_column_10 : reversePack 256 (fun j : Fin 14 => C080_digit j 10)=C080_columnCode 10 := by decide +kernel

private theorem C080_column_11 : reversePack 256 (fun j : Fin 14 => C080_digit j 11)=C080_columnCode 11 := by decide +kernel

private theorem C080_column_12 : reversePack 256 (fun j : Fin 14 => C080_digit j 12)=C080_columnCode 12 := by decide +kernel

private theorem C080_column_13 : reversePack 256 (fun j : Fin 14 => C080_digit j 13)=C080_columnCode 13 := by decide +kernel

theorem C080_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C080_digit j i)=C080_columnCode i := by
  intro i
  fin_cases i
  · exact C080_column_00
  · exact C080_column_01
  · exact C080_column_02
  · exact C080_column_03
  · exact C080_column_04
  · exact C080_column_05
  · exact C080_column_06
  · exact C080_column_07
  · exact C080_column_08
  · exact C080_column_09
  · exact C080_column_10
  · exact C080_column_11
  · exact C080_column_12
  · exact C080_column_13

def C080_data : PackedData 14 5 256 where
  raw := C080_digit
  digit_lt := C080_bound
  rowCode := C080_rowCode
  columnCode := C080_columnCode
  row_binding := C080_row_binding
  column_binding := C080_column_binding

def C081_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 2442920763608
  | 1 => 1893160487202
  | 2 => 2409478886690
  | 3 => 1924313679068
  | 4 => 2203343421969
  | 5 => 1855463657472
  | 6 => 1867237031936
  | 7 => 70866964480
  | 8 => 2204174492
  | 9 => 1731182766083
  | 10 => 549789434914
  | 11 => 2422418441419
  | 12 => 2474974904320
  | 13 => 1653604451618
  | _ => 0

def C081_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 40565750094425330537267162382848
  | 1 => 81129952735375121731604197934083
  | 2 => 81130566869673039219142649185283
  | 3 => 40565440614137875675068049261568
  | 4 => 9444805024432840048642
  | 5 => 60847231233565910473220991222017
  | 6 => 309494454554310808048763395
  | 7 => 81130566888580951896911092187395
  | 8 => 40565750089684517312522797187329
  | 9 => 9444732965739307204865
  | 10 => 81208866596047450412638735172355
  | 11 => 618974742009454482071487492
  | 12 => 317841109808960773767565607683
  | 13 => 61165380624144273913469634609924
  | _ => 0

def C081_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 238612952035653776110707278596
  | 1 => 40882974633121553178900895630083
  | 2 => 40882972220047476548441454150404
  | 3 => 81368253775049168834499264381955
  | 4 => 20440867137624466584836709023748
  | 5 => 4740813792092331442947
  | 6 => 50397955
  | 7 => 4722366482869678768384
  | 8 => 81367946707909290193094703054848
  | 9 => 60847233656121614683467115725059
  | 10 => 40881734275248930917873470144513
  | 11 => 60927387846350451779217324638980
  | 12 => 16778244
  | 13 => 40882972215306664168122052771843
  | _ => 0

def C081_digit (i j : Fin 14) : ℕ := packedDigit 3 (C081_lowColumnCode j) i.val

private theorem C081_bound_00 : ∀ j : Fin 14, C081_digit 0 j < 5 := by decide +kernel

private theorem C081_bound_01 : ∀ j : Fin 14, C081_digit 1 j < 5 := by decide +kernel

private theorem C081_bound_02 : ∀ j : Fin 14, C081_digit 2 j < 5 := by decide +kernel

private theorem C081_bound_03 : ∀ j : Fin 14, C081_digit 3 j < 5 := by decide +kernel

private theorem C081_bound_04 : ∀ j : Fin 14, C081_digit 4 j < 5 := by decide +kernel

private theorem C081_bound_05 : ∀ j : Fin 14, C081_digit 5 j < 5 := by decide +kernel

private theorem C081_bound_06 : ∀ j : Fin 14, C081_digit 6 j < 5 := by decide +kernel

private theorem C081_bound_07 : ∀ j : Fin 14, C081_digit 7 j < 5 := by decide +kernel

private theorem C081_bound_08 : ∀ j : Fin 14, C081_digit 8 j < 5 := by decide +kernel

private theorem C081_bound_09 : ∀ j : Fin 14, C081_digit 9 j < 5 := by decide +kernel

private theorem C081_bound_10 : ∀ j : Fin 14, C081_digit 10 j < 5 := by decide +kernel

private theorem C081_bound_11 : ∀ j : Fin 14, C081_digit 11 j < 5 := by decide +kernel

private theorem C081_bound_12 : ∀ j : Fin 14, C081_digit 12 j < 5 := by decide +kernel

private theorem C081_bound_13 : ∀ j : Fin 14, C081_digit 13 j < 5 := by decide +kernel

theorem C081_bound : ∀ i j : Fin 14, C081_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C081_bound_00 j
  · exact C081_bound_01 j
  · exact C081_bound_02 j
  · exact C081_bound_03 j
  · exact C081_bound_04 j
  · exact C081_bound_05 j
  · exact C081_bound_06 j
  · exact C081_bound_07 j
  · exact C081_bound_08 j
  · exact C081_bound_09 j
  · exact C081_bound_10 j
  · exact C081_bound_11 j
  · exact C081_bound_12 j
  · exact C081_bound_13 j

private theorem C081_row_00 : pack 256 (C081_digit 0)=C081_rowCode 0 := by decide +kernel

private theorem C081_row_01 : pack 256 (C081_digit 1)=C081_rowCode 1 := by decide +kernel

private theorem C081_row_02 : pack 256 (C081_digit 2)=C081_rowCode 2 := by decide +kernel

private theorem C081_row_03 : pack 256 (C081_digit 3)=C081_rowCode 3 := by decide +kernel

private theorem C081_row_04 : pack 256 (C081_digit 4)=C081_rowCode 4 := by decide +kernel

private theorem C081_row_05 : pack 256 (C081_digit 5)=C081_rowCode 5 := by decide +kernel

private theorem C081_row_06 : pack 256 (C081_digit 6)=C081_rowCode 6 := by decide +kernel

private theorem C081_row_07 : pack 256 (C081_digit 7)=C081_rowCode 7 := by decide +kernel

private theorem C081_row_08 : pack 256 (C081_digit 8)=C081_rowCode 8 := by decide +kernel

private theorem C081_row_09 : pack 256 (C081_digit 9)=C081_rowCode 9 := by decide +kernel

private theorem C081_row_10 : pack 256 (C081_digit 10)=C081_rowCode 10 := by decide +kernel

private theorem C081_row_11 : pack 256 (C081_digit 11)=C081_rowCode 11 := by decide +kernel

private theorem C081_row_12 : pack 256 (C081_digit 12)=C081_rowCode 12 := by decide +kernel

private theorem C081_row_13 : pack 256 (C081_digit 13)=C081_rowCode 13 := by decide +kernel

theorem C081_row_binding : ∀ i : Fin 14, pack 256 (C081_digit i)=C081_rowCode i := by
  intro i
  fin_cases i
  · exact C081_row_00
  · exact C081_row_01
  · exact C081_row_02
  · exact C081_row_03
  · exact C081_row_04
  · exact C081_row_05
  · exact C081_row_06
  · exact C081_row_07
  · exact C081_row_08
  · exact C081_row_09
  · exact C081_row_10
  · exact C081_row_11
  · exact C081_row_12
  · exact C081_row_13

private theorem C081_column_00 : reversePack 256 (fun j : Fin 14 => C081_digit j 0)=C081_columnCode 0 := by decide +kernel

private theorem C081_column_01 : reversePack 256 (fun j : Fin 14 => C081_digit j 1)=C081_columnCode 1 := by decide +kernel

private theorem C081_column_02 : reversePack 256 (fun j : Fin 14 => C081_digit j 2)=C081_columnCode 2 := by decide +kernel

private theorem C081_column_03 : reversePack 256 (fun j : Fin 14 => C081_digit j 3)=C081_columnCode 3 := by decide +kernel

private theorem C081_column_04 : reversePack 256 (fun j : Fin 14 => C081_digit j 4)=C081_columnCode 4 := by decide +kernel

private theorem C081_column_05 : reversePack 256 (fun j : Fin 14 => C081_digit j 5)=C081_columnCode 5 := by decide +kernel

private theorem C081_column_06 : reversePack 256 (fun j : Fin 14 => C081_digit j 6)=C081_columnCode 6 := by decide +kernel

private theorem C081_column_07 : reversePack 256 (fun j : Fin 14 => C081_digit j 7)=C081_columnCode 7 := by decide +kernel

private theorem C081_column_08 : reversePack 256 (fun j : Fin 14 => C081_digit j 8)=C081_columnCode 8 := by decide +kernel

private theorem C081_column_09 : reversePack 256 (fun j : Fin 14 => C081_digit j 9)=C081_columnCode 9 := by decide +kernel

private theorem C081_column_10 : reversePack 256 (fun j : Fin 14 => C081_digit j 10)=C081_columnCode 10 := by decide +kernel

private theorem C081_column_11 : reversePack 256 (fun j : Fin 14 => C081_digit j 11)=C081_columnCode 11 := by decide +kernel

private theorem C081_column_12 : reversePack 256 (fun j : Fin 14 => C081_digit j 12)=C081_columnCode 12 := by decide +kernel

private theorem C081_column_13 : reversePack 256 (fun j : Fin 14 => C081_digit j 13)=C081_columnCode 13 := by decide +kernel

theorem C081_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C081_digit j i)=C081_columnCode i := by
  intro i
  fin_cases i
  · exact C081_column_00
  · exact C081_column_01
  · exact C081_column_02
  · exact C081_column_03
  · exact C081_column_04
  · exact C081_column_05
  · exact C081_column_06
  · exact C081_column_07
  · exact C081_column_08
  · exact C081_column_09
  · exact C081_column_10
  · exact C081_column_11
  · exact C081_column_12
  · exact C081_column_13

def C081_data : PackedData 14 5 256 where
  raw := C081_digit
  digit_lt := C081_bound
  rowCode := C081_rowCode
  columnCode := C081_columnCode
  row_binding := C081_row_binding
  column_binding := C081_column_binding

def C082_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 1257808938640
  | 1 => 1787132227588
  | 2 => 2484907610260
  | 3 => 623383414946
  | 4 => 1168819226257
  | 5 => 1867237031936
  | 6 => 2204174492
  | 7 => 1731182766083
  | 8 => 1855463657472
  | 9 => 549789434914
  | 10 => 70866964480
  | 11 => 2474974904320
  | 12 => 1653604451618
  | 13 => 2422418441419
  | _ => 0

def C082_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 61005685145428490211454481597440
  | 1 => 20599322272598194550233595248642
  | 2 => 61164141461012069185174506700802
  | 3 => 40723275541776891845109891465219
  | 4 => 1208944410473890960179972
  | 5 => 237684497006045343154803180290
  | 6 => 20282409603651814539148262506496
  | 7 => 61164141461049251185164497715970
  | 8 => 61005685145465311360541509288195
  | 9 => 144115205322965763
  | 10 => 317224552918806721325957251075
  | 11 => 40564819207303412906588052193282
  | 12 => 60848467959975528559863841161730
  | 13 => 81368560846966682980024565629698
  | _ => 0

def C082_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 159078940751990195099485209090
  | 1 => 81129638428829122222156396102147
  | 2 => 81288713714414257147327306335236
  | 3 => 40882355663083536650020140876033
  | 4 => 20441488525551303785551979610370
  | 5 => 50397955
  | 6 => 81367946707909290193094703054848
  | 7 => 60847233656121614683467115725059
  | 8 => 4740813792092331442947
  | 9 => 40881734275248930917873470144513
  | 10 => 4722366482869678768384
  | 11 => 16778244
  | 12 => 40882972215306664168122052771843
  | 13 => 60927387846350451779217324638980
  | _ => 0

def C082_digit (i j : Fin 14) : ℕ := packedDigit 3 (C082_lowColumnCode j) i.val

private theorem C082_bound_00 : ∀ j : Fin 14, C082_digit 0 j < 5 := by decide +kernel

private theorem C082_bound_01 : ∀ j : Fin 14, C082_digit 1 j < 5 := by decide +kernel

private theorem C082_bound_02 : ∀ j : Fin 14, C082_digit 2 j < 5 := by decide +kernel

private theorem C082_bound_03 : ∀ j : Fin 14, C082_digit 3 j < 5 := by decide +kernel

private theorem C082_bound_04 : ∀ j : Fin 14, C082_digit 4 j < 5 := by decide +kernel

private theorem C082_bound_05 : ∀ j : Fin 14, C082_digit 5 j < 5 := by decide +kernel

private theorem C082_bound_06 : ∀ j : Fin 14, C082_digit 6 j < 5 := by decide +kernel

private theorem C082_bound_07 : ∀ j : Fin 14, C082_digit 7 j < 5 := by decide +kernel

private theorem C082_bound_08 : ∀ j : Fin 14, C082_digit 8 j < 5 := by decide +kernel

private theorem C082_bound_09 : ∀ j : Fin 14, C082_digit 9 j < 5 := by decide +kernel

private theorem C082_bound_10 : ∀ j : Fin 14, C082_digit 10 j < 5 := by decide +kernel

private theorem C082_bound_11 : ∀ j : Fin 14, C082_digit 11 j < 5 := by decide +kernel

private theorem C082_bound_12 : ∀ j : Fin 14, C082_digit 12 j < 5 := by decide +kernel

private theorem C082_bound_13 : ∀ j : Fin 14, C082_digit 13 j < 5 := by decide +kernel

theorem C082_bound : ∀ i j : Fin 14, C082_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C082_bound_00 j
  · exact C082_bound_01 j
  · exact C082_bound_02 j
  · exact C082_bound_03 j
  · exact C082_bound_04 j
  · exact C082_bound_05 j
  · exact C082_bound_06 j
  · exact C082_bound_07 j
  · exact C082_bound_08 j
  · exact C082_bound_09 j
  · exact C082_bound_10 j
  · exact C082_bound_11 j
  · exact C082_bound_12 j
  · exact C082_bound_13 j

private theorem C082_row_00 : pack 256 (C082_digit 0)=C082_rowCode 0 := by decide +kernel

private theorem C082_row_01 : pack 256 (C082_digit 1)=C082_rowCode 1 := by decide +kernel

private theorem C082_row_02 : pack 256 (C082_digit 2)=C082_rowCode 2 := by decide +kernel

private theorem C082_row_03 : pack 256 (C082_digit 3)=C082_rowCode 3 := by decide +kernel

private theorem C082_row_04 : pack 256 (C082_digit 4)=C082_rowCode 4 := by decide +kernel

private theorem C082_row_05 : pack 256 (C082_digit 5)=C082_rowCode 5 := by decide +kernel

private theorem C082_row_06 : pack 256 (C082_digit 6)=C082_rowCode 6 := by decide +kernel

private theorem C082_row_07 : pack 256 (C082_digit 7)=C082_rowCode 7 := by decide +kernel

private theorem C082_row_08 : pack 256 (C082_digit 8)=C082_rowCode 8 := by decide +kernel

private theorem C082_row_09 : pack 256 (C082_digit 9)=C082_rowCode 9 := by decide +kernel

private theorem C082_row_10 : pack 256 (C082_digit 10)=C082_rowCode 10 := by decide +kernel

private theorem C082_row_11 : pack 256 (C082_digit 11)=C082_rowCode 11 := by decide +kernel

private theorem C082_row_12 : pack 256 (C082_digit 12)=C082_rowCode 12 := by decide +kernel

private theorem C082_row_13 : pack 256 (C082_digit 13)=C082_rowCode 13 := by decide +kernel

theorem C082_row_binding : ∀ i : Fin 14, pack 256 (C082_digit i)=C082_rowCode i := by
  intro i
  fin_cases i
  · exact C082_row_00
  · exact C082_row_01
  · exact C082_row_02
  · exact C082_row_03
  · exact C082_row_04
  · exact C082_row_05
  · exact C082_row_06
  · exact C082_row_07
  · exact C082_row_08
  · exact C082_row_09
  · exact C082_row_10
  · exact C082_row_11
  · exact C082_row_12
  · exact C082_row_13

private theorem C082_column_00 : reversePack 256 (fun j : Fin 14 => C082_digit j 0)=C082_columnCode 0 := by decide +kernel

private theorem C082_column_01 : reversePack 256 (fun j : Fin 14 => C082_digit j 1)=C082_columnCode 1 := by decide +kernel

private theorem C082_column_02 : reversePack 256 (fun j : Fin 14 => C082_digit j 2)=C082_columnCode 2 := by decide +kernel

private theorem C082_column_03 : reversePack 256 (fun j : Fin 14 => C082_digit j 3)=C082_columnCode 3 := by decide +kernel

private theorem C082_column_04 : reversePack 256 (fun j : Fin 14 => C082_digit j 4)=C082_columnCode 4 := by decide +kernel

private theorem C082_column_05 : reversePack 256 (fun j : Fin 14 => C082_digit j 5)=C082_columnCode 5 := by decide +kernel

private theorem C082_column_06 : reversePack 256 (fun j : Fin 14 => C082_digit j 6)=C082_columnCode 6 := by decide +kernel

private theorem C082_column_07 : reversePack 256 (fun j : Fin 14 => C082_digit j 7)=C082_columnCode 7 := by decide +kernel

private theorem C082_column_08 : reversePack 256 (fun j : Fin 14 => C082_digit j 8)=C082_columnCode 8 := by decide +kernel

private theorem C082_column_09 : reversePack 256 (fun j : Fin 14 => C082_digit j 9)=C082_columnCode 9 := by decide +kernel

private theorem C082_column_10 : reversePack 256 (fun j : Fin 14 => C082_digit j 10)=C082_columnCode 10 := by decide +kernel

private theorem C082_column_11 : reversePack 256 (fun j : Fin 14 => C082_digit j 11)=C082_columnCode 11 := by decide +kernel

private theorem C082_column_12 : reversePack 256 (fun j : Fin 14 => C082_digit j 12)=C082_columnCode 12 := by decide +kernel

private theorem C082_column_13 : reversePack 256 (fun j : Fin 14 => C082_digit j 13)=C082_columnCode 13 := by decide +kernel

theorem C082_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C082_digit j i)=C082_columnCode i := by
  intro i
  fin_cases i
  · exact C082_column_00
  · exact C082_column_01
  · exact C082_column_02
  · exact C082_column_03
  · exact C082_column_04
  · exact C082_column_05
  · exact C082_column_06
  · exact C082_column_07
  · exact C082_column_08
  · exact C082_column_09
  · exact C082_column_10
  · exact C082_column_11
  · exact C082_column_12
  · exact C082_column_13

def C082_data : PackedData 14 5 256 where
  raw := C082_digit
  digit_lt := C082_bound
  rowCode := C082_rowCode
  columnCode := C082_columnCode
  row_binding := C082_row_binding
  column_binding := C082_column_binding

end SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedCaches08
