import SymmetricSubgroupAsymptotics.MatrixKroneckerProductReflection
import Mathlib.Tactic.FinCases

/-! Fixed Co2 binary22 shared caches. Every digit and pack binding is kernel checked. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoCaches01
open MatrixKroneckerProductReflection MatrixKroneckerDotReflection
open MatrixNaturalRowDotReflection SmallNaturalMatrixProductReflection

def R03e08_lowColumnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 99330
  | 1 => 623636
  | 2 => 1576448
  | 3 => 1572998
  | 4 => 1910095
  | 5 => 1165327
  | 6 => 786761
  | 7 => 1638407
  | 8 => 1678351
  | 9 => 1674240
  | 10 => 1246208
  | 11 => 1902592
  | 12 => 1641480
  | 13 => 3148032
  | 14 => 1640448
  | 15 => 527680
  | 16 => 3328
  | 17 => 1639488
  | 18 => 2304
  | 19 => 352
  | 20 => 65536
  | 21 => 1572864
  | _ => 0

def R03e08_rowCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1134979710976
  | 1 => 1133906001921
  | 2 => 1133906001952
  | 3 => 1152922605226819584
  | 4 => 32
  | 5 => 39614081257132168796771975168
  | 6 => 39652804662291699888599072768
  | 7 => 32768
  | 8 => 40853268038062514806501408768
  | 9 => 1024
  | 10 => 39932332133229408325469217
  | 11 => 1239187962710953311609029632
  | 12 => 1099511627776
  | 13 => 1048576
  | 14 => 33554432
  | 15 => 36283917271073
  | 16 => 1267689287036238802867515818017
  | 17 => 1125899906842624
  | 18 => 36028798093754368
  | 19 => 40564857931890280986323610272800
  | 20 => 40564857894148243737412734321664
  | 21 => 36893488147419103232
  | _ => 0

def R03e08_columnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1267650600228265430294829465600
  | 1 => 39652766883395865728488834048
  | 2 => 1190076201532654624
  | 3 => 1307264682665953191010886485024
  | 4 => 41873321866643849179464021869600
  | 5 => 41873321828827988924398250754080
  | 6 => 40566057185158451579273982542848
  | 7 => 41872083888788702418188011308064
  | 8 => 41873321828828024988345282069536
  | 9 => 37154698033103904
  | 10 => 36028797053567008
  | 11 => 1125899940430880
  | 12 => 1237940039322534971858486304
  | 13 => 36894614047325945889
  | 14 => 1125899940398112
  | 15 => 37815862505801506620416
  | 16 => 36930642844344909824
  | 17 => 37778967891754214229024
  | 18 => 36894614047325945856
  | 19 => 1246741644965733755518976
  | 20 => 33554432
  | 21 => 1056
  | _ => 0

def R03e08_digit (i j : Fin 22) : ℕ := packedDigit 1 (R03e08_lowColumnCode j) i.val

private theorem R03e08_bound_00 : ∀ j : Fin 22,R03e08_digit 0 j<2 := by decide +kernel

private theorem R03e08_bound_01 : ∀ j : Fin 22,R03e08_digit 1 j<2 := by decide +kernel

private theorem R03e08_bound_02 : ∀ j : Fin 22,R03e08_digit 2 j<2 := by decide +kernel

private theorem R03e08_bound_03 : ∀ j : Fin 22,R03e08_digit 3 j<2 := by decide +kernel

private theorem R03e08_bound_04 : ∀ j : Fin 22,R03e08_digit 4 j<2 := by decide +kernel

private theorem R03e08_bound_05 : ∀ j : Fin 22,R03e08_digit 5 j<2 := by decide +kernel

private theorem R03e08_bound_06 : ∀ j : Fin 22,R03e08_digit 6 j<2 := by decide +kernel

private theorem R03e08_bound_07 : ∀ j : Fin 22,R03e08_digit 7 j<2 := by decide +kernel

private theorem R03e08_bound_08 : ∀ j : Fin 22,R03e08_digit 8 j<2 := by decide +kernel

private theorem R03e08_bound_09 : ∀ j : Fin 22,R03e08_digit 9 j<2 := by decide +kernel

private theorem R03e08_bound_10 : ∀ j : Fin 22,R03e08_digit 10 j<2 := by decide +kernel

private theorem R03e08_bound_11 : ∀ j : Fin 22,R03e08_digit 11 j<2 := by decide +kernel

private theorem R03e08_bound_12 : ∀ j : Fin 22,R03e08_digit 12 j<2 := by decide +kernel

private theorem R03e08_bound_13 : ∀ j : Fin 22,R03e08_digit 13 j<2 := by decide +kernel

private theorem R03e08_bound_14 : ∀ j : Fin 22,R03e08_digit 14 j<2 := by decide +kernel

private theorem R03e08_bound_15 : ∀ j : Fin 22,R03e08_digit 15 j<2 := by decide +kernel

private theorem R03e08_bound_16 : ∀ j : Fin 22,R03e08_digit 16 j<2 := by decide +kernel

private theorem R03e08_bound_17 : ∀ j : Fin 22,R03e08_digit 17 j<2 := by decide +kernel

private theorem R03e08_bound_18 : ∀ j : Fin 22,R03e08_digit 18 j<2 := by decide +kernel

private theorem R03e08_bound_19 : ∀ j : Fin 22,R03e08_digit 19 j<2 := by decide +kernel

private theorem R03e08_bound_20 : ∀ j : Fin 22,R03e08_digit 20 j<2 := by decide +kernel

private theorem R03e08_bound_21 : ∀ j : Fin 22,R03e08_digit 21 j<2 := by decide +kernel

theorem R03e08_bound : ∀ i j : Fin 22,R03e08_digit i j<2 := by
  intro i j
  fin_cases i
  · exact R03e08_bound_00 j
  · exact R03e08_bound_01 j
  · exact R03e08_bound_02 j
  · exact R03e08_bound_03 j
  · exact R03e08_bound_04 j
  · exact R03e08_bound_05 j
  · exact R03e08_bound_06 j
  · exact R03e08_bound_07 j
  · exact R03e08_bound_08 j
  · exact R03e08_bound_09 j
  · exact R03e08_bound_10 j
  · exact R03e08_bound_11 j
  · exact R03e08_bound_12 j
  · exact R03e08_bound_13 j
  · exact R03e08_bound_14 j
  · exact R03e08_bound_15 j
  · exact R03e08_bound_16 j
  · exact R03e08_bound_17 j
  · exact R03e08_bound_18 j
  · exact R03e08_bound_19 j
  · exact R03e08_bound_20 j
  · exact R03e08_bound_21 j

private theorem R03e08_row_00 : pack 32 (R03e08_digit 0)=R03e08_rowCode 0 := by decide +kernel

private theorem R03e08_row_01 : pack 32 (R03e08_digit 1)=R03e08_rowCode 1 := by decide +kernel

private theorem R03e08_row_02 : pack 32 (R03e08_digit 2)=R03e08_rowCode 2 := by decide +kernel

private theorem R03e08_row_03 : pack 32 (R03e08_digit 3)=R03e08_rowCode 3 := by decide +kernel

private theorem R03e08_row_04 : pack 32 (R03e08_digit 4)=R03e08_rowCode 4 := by decide +kernel

private theorem R03e08_row_05 : pack 32 (R03e08_digit 5)=R03e08_rowCode 5 := by decide +kernel

private theorem R03e08_row_06 : pack 32 (R03e08_digit 6)=R03e08_rowCode 6 := by decide +kernel

private theorem R03e08_row_07 : pack 32 (R03e08_digit 7)=R03e08_rowCode 7 := by decide +kernel

private theorem R03e08_row_08 : pack 32 (R03e08_digit 8)=R03e08_rowCode 8 := by decide +kernel

private theorem R03e08_row_09 : pack 32 (R03e08_digit 9)=R03e08_rowCode 9 := by decide +kernel

private theorem R03e08_row_10 : pack 32 (R03e08_digit 10)=R03e08_rowCode 10 := by decide +kernel

private theorem R03e08_row_11 : pack 32 (R03e08_digit 11)=R03e08_rowCode 11 := by decide +kernel

private theorem R03e08_row_12 : pack 32 (R03e08_digit 12)=R03e08_rowCode 12 := by decide +kernel

private theorem R03e08_row_13 : pack 32 (R03e08_digit 13)=R03e08_rowCode 13 := by decide +kernel

private theorem R03e08_row_14 : pack 32 (R03e08_digit 14)=R03e08_rowCode 14 := by decide +kernel

private theorem R03e08_row_15 : pack 32 (R03e08_digit 15)=R03e08_rowCode 15 := by decide +kernel

private theorem R03e08_row_16 : pack 32 (R03e08_digit 16)=R03e08_rowCode 16 := by decide +kernel

private theorem R03e08_row_17 : pack 32 (R03e08_digit 17)=R03e08_rowCode 17 := by decide +kernel

private theorem R03e08_row_18 : pack 32 (R03e08_digit 18)=R03e08_rowCode 18 := by decide +kernel

private theorem R03e08_row_19 : pack 32 (R03e08_digit 19)=R03e08_rowCode 19 := by decide +kernel

private theorem R03e08_row_20 : pack 32 (R03e08_digit 20)=R03e08_rowCode 20 := by decide +kernel

private theorem R03e08_row_21 : pack 32 (R03e08_digit 21)=R03e08_rowCode 21 := by decide +kernel

theorem R03e08_row_binding : ∀ i : Fin 22,pack 32 (R03e08_digit i)=R03e08_rowCode i := by
  intro i
  fin_cases i
  · exact R03e08_row_00
  · exact R03e08_row_01
  · exact R03e08_row_02
  · exact R03e08_row_03
  · exact R03e08_row_04
  · exact R03e08_row_05
  · exact R03e08_row_06
  · exact R03e08_row_07
  · exact R03e08_row_08
  · exact R03e08_row_09
  · exact R03e08_row_10
  · exact R03e08_row_11
  · exact R03e08_row_12
  · exact R03e08_row_13
  · exact R03e08_row_14
  · exact R03e08_row_15
  · exact R03e08_row_16
  · exact R03e08_row_17
  · exact R03e08_row_18
  · exact R03e08_row_19
  · exact R03e08_row_20
  · exact R03e08_row_21

private theorem R03e08_column_00 : reversePack 32 (fun j : Fin 22 => R03e08_digit j 0)=R03e08_columnCode 0 := by decide +kernel

private theorem R03e08_column_01 : reversePack 32 (fun j : Fin 22 => R03e08_digit j 1)=R03e08_columnCode 1 := by decide +kernel

private theorem R03e08_column_02 : reversePack 32 (fun j : Fin 22 => R03e08_digit j 2)=R03e08_columnCode 2 := by decide +kernel

private theorem R03e08_column_03 : reversePack 32 (fun j : Fin 22 => R03e08_digit j 3)=R03e08_columnCode 3 := by decide +kernel

private theorem R03e08_column_04 : reversePack 32 (fun j : Fin 22 => R03e08_digit j 4)=R03e08_columnCode 4 := by decide +kernel

private theorem R03e08_column_05 : reversePack 32 (fun j : Fin 22 => R03e08_digit j 5)=R03e08_columnCode 5 := by decide +kernel

private theorem R03e08_column_06 : reversePack 32 (fun j : Fin 22 => R03e08_digit j 6)=R03e08_columnCode 6 := by decide +kernel

private theorem R03e08_column_07 : reversePack 32 (fun j : Fin 22 => R03e08_digit j 7)=R03e08_columnCode 7 := by decide +kernel

private theorem R03e08_column_08 : reversePack 32 (fun j : Fin 22 => R03e08_digit j 8)=R03e08_columnCode 8 := by decide +kernel

private theorem R03e08_column_09 : reversePack 32 (fun j : Fin 22 => R03e08_digit j 9)=R03e08_columnCode 9 := by decide +kernel

private theorem R03e08_column_10 : reversePack 32 (fun j : Fin 22 => R03e08_digit j 10)=R03e08_columnCode 10 := by decide +kernel

private theorem R03e08_column_11 : reversePack 32 (fun j : Fin 22 => R03e08_digit j 11)=R03e08_columnCode 11 := by decide +kernel

private theorem R03e08_column_12 : reversePack 32 (fun j : Fin 22 => R03e08_digit j 12)=R03e08_columnCode 12 := by decide +kernel

private theorem R03e08_column_13 : reversePack 32 (fun j : Fin 22 => R03e08_digit j 13)=R03e08_columnCode 13 := by decide +kernel

private theorem R03e08_column_14 : reversePack 32 (fun j : Fin 22 => R03e08_digit j 14)=R03e08_columnCode 14 := by decide +kernel

private theorem R03e08_column_15 : reversePack 32 (fun j : Fin 22 => R03e08_digit j 15)=R03e08_columnCode 15 := by decide +kernel

private theorem R03e08_column_16 : reversePack 32 (fun j : Fin 22 => R03e08_digit j 16)=R03e08_columnCode 16 := by decide +kernel

private theorem R03e08_column_17 : reversePack 32 (fun j : Fin 22 => R03e08_digit j 17)=R03e08_columnCode 17 := by decide +kernel

private theorem R03e08_column_18 : reversePack 32 (fun j : Fin 22 => R03e08_digit j 18)=R03e08_columnCode 18 := by decide +kernel

private theorem R03e08_column_19 : reversePack 32 (fun j : Fin 22 => R03e08_digit j 19)=R03e08_columnCode 19 := by decide +kernel

private theorem R03e08_column_20 : reversePack 32 (fun j : Fin 22 => R03e08_digit j 20)=R03e08_columnCode 20 := by decide +kernel

private theorem R03e08_column_21 : reversePack 32 (fun j : Fin 22 => R03e08_digit j 21)=R03e08_columnCode 21 := by decide +kernel

theorem R03e08_column_binding : ∀ i : Fin 22,reversePack 32 (fun j : Fin 22 => R03e08_digit j i)=R03e08_columnCode i := by
  intro i
  fin_cases i
  · exact R03e08_column_00
  · exact R03e08_column_01
  · exact R03e08_column_02
  · exact R03e08_column_03
  · exact R03e08_column_04
  · exact R03e08_column_05
  · exact R03e08_column_06
  · exact R03e08_column_07
  · exact R03e08_column_08
  · exact R03e08_column_09
  · exact R03e08_column_10
  · exact R03e08_column_11
  · exact R03e08_column_12
  · exact R03e08_column_13
  · exact R03e08_column_14
  · exact R03e08_column_15
  · exact R03e08_column_16
  · exact R03e08_column_17
  · exact R03e08_column_18
  · exact R03e08_column_19
  · exact R03e08_column_20
  · exact R03e08_column_21

def R03e08_data : PackedData 22 2 32 where
  raw := R03e08_digit
  digit_lt := R03e08_bound
  rowCode := R03e08_rowCode
  columnCode := R03e08_columnCode
  row_binding := R03e08_row_binding
  column_binding := R03e08_column_binding

def R04p01_lowColumnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 2367499
  | 1 => 1335809
  | 2 => 1358530
  | 3 => 3471792
  | 4 => 1237634
  | 5 => 321584
  | 6 => 56464
  | 7 => 1335810
  | 8 => 178848
  | 9 => 326192
  | 10 => 489616
  | 11 => 193184
  | 12 => 715312
  | 13 => 3176592
  | 14 => 12960
  | 15 => 1370676
  | 16 => 1474560
  | 17 => 3471504
  | 18 => 3576480
  | 19 => 3317760
  | 20 => 2097152
  | 21 => 3416064
  | _ => 0

def R04p01_rowCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 33
  | 1 => 34360787969
  | 2 => 37778931862957161709568
  | 3 => 1
  | 4 => 38723443207101828164517888
  | 5 => 1237978999997850535015251968
  | 6 => 1024
  | 7 => 1276626883035313070832387072
  | 8 => 32768
  | 9 => 1237978999997850569342452768
  | 10 => 1073741824
  | 11 => 38723443207102927676146688
  | 12 => 1276626883035348255203427328
  | 13 => 40604472013184307769166668006433
  | 14 => 38723443243130659544268832
  | 15 => 40891953628585681378216018944
  | 16 => 1125899906842624
  | 17 => 40853230223427241001891135488
  | 18 => 40566097079673606535008000967713
  | 19 => 1152921504606846976
  | 20 => 40605711160967631030867880608800
  | 21 => 41873360514491108954743886610433
  | _ => 0

def R04p01_columnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 41833707747570855630765616562177
  | 1 => 40564819207304493770532980817952
  | 2 => 1267650639188906968860747399200
  | 3 => 39895769533553846819782689
  | 4 => 1267650601409973944853667512352
  | 5 => 39894552048409797617287168
  | 6 => 38686806856478767733276672
  | 7 => 1267650600229382324135181451296
  | 8 => 1210107565319036058206208
  | 9 => 39894553201366486596222976
  | 10 => 38686806820451069186834432
  | 11 => 1210107564193170511101952
  | 12 => 39894553201331302225150976
  | 13 => 38686806820451069152198689
  | 14 => 1210107564193135076573184
  | 15 => 39653975810333500098996109344
  | 16 => 1074823200
  | 17 => 38686806820451070225973281
  | 18 => 1210107564192036639768609
  | 19 => 1100586418209
  | 20 => 1
  | 21 => 1099511660577
  | _ => 0

def R04p01_digit (i j : Fin 22) : ℕ := packedDigit 1 (R04p01_lowColumnCode j) i.val

private theorem R04p01_bound_00 : ∀ j : Fin 22,R04p01_digit 0 j<2 := by decide +kernel

private theorem R04p01_bound_01 : ∀ j : Fin 22,R04p01_digit 1 j<2 := by decide +kernel

private theorem R04p01_bound_02 : ∀ j : Fin 22,R04p01_digit 2 j<2 := by decide +kernel

private theorem R04p01_bound_03 : ∀ j : Fin 22,R04p01_digit 3 j<2 := by decide +kernel

private theorem R04p01_bound_04 : ∀ j : Fin 22,R04p01_digit 4 j<2 := by decide +kernel

private theorem R04p01_bound_05 : ∀ j : Fin 22,R04p01_digit 5 j<2 := by decide +kernel

private theorem R04p01_bound_06 : ∀ j : Fin 22,R04p01_digit 6 j<2 := by decide +kernel

private theorem R04p01_bound_07 : ∀ j : Fin 22,R04p01_digit 7 j<2 := by decide +kernel

private theorem R04p01_bound_08 : ∀ j : Fin 22,R04p01_digit 8 j<2 := by decide +kernel

private theorem R04p01_bound_09 : ∀ j : Fin 22,R04p01_digit 9 j<2 := by decide +kernel

private theorem R04p01_bound_10 : ∀ j : Fin 22,R04p01_digit 10 j<2 := by decide +kernel

private theorem R04p01_bound_11 : ∀ j : Fin 22,R04p01_digit 11 j<2 := by decide +kernel

private theorem R04p01_bound_12 : ∀ j : Fin 22,R04p01_digit 12 j<2 := by decide +kernel

private theorem R04p01_bound_13 : ∀ j : Fin 22,R04p01_digit 13 j<2 := by decide +kernel

private theorem R04p01_bound_14 : ∀ j : Fin 22,R04p01_digit 14 j<2 := by decide +kernel

private theorem R04p01_bound_15 : ∀ j : Fin 22,R04p01_digit 15 j<2 := by decide +kernel

private theorem R04p01_bound_16 : ∀ j : Fin 22,R04p01_digit 16 j<2 := by decide +kernel

private theorem R04p01_bound_17 : ∀ j : Fin 22,R04p01_digit 17 j<2 := by decide +kernel

private theorem R04p01_bound_18 : ∀ j : Fin 22,R04p01_digit 18 j<2 := by decide +kernel

private theorem R04p01_bound_19 : ∀ j : Fin 22,R04p01_digit 19 j<2 := by decide +kernel

private theorem R04p01_bound_20 : ∀ j : Fin 22,R04p01_digit 20 j<2 := by decide +kernel

private theorem R04p01_bound_21 : ∀ j : Fin 22,R04p01_digit 21 j<2 := by decide +kernel

theorem R04p01_bound : ∀ i j : Fin 22,R04p01_digit i j<2 := by
  intro i j
  fin_cases i
  · exact R04p01_bound_00 j
  · exact R04p01_bound_01 j
  · exact R04p01_bound_02 j
  · exact R04p01_bound_03 j
  · exact R04p01_bound_04 j
  · exact R04p01_bound_05 j
  · exact R04p01_bound_06 j
  · exact R04p01_bound_07 j
  · exact R04p01_bound_08 j
  · exact R04p01_bound_09 j
  · exact R04p01_bound_10 j
  · exact R04p01_bound_11 j
  · exact R04p01_bound_12 j
  · exact R04p01_bound_13 j
  · exact R04p01_bound_14 j
  · exact R04p01_bound_15 j
  · exact R04p01_bound_16 j
  · exact R04p01_bound_17 j
  · exact R04p01_bound_18 j
  · exact R04p01_bound_19 j
  · exact R04p01_bound_20 j
  · exact R04p01_bound_21 j

private theorem R04p01_row_00 : pack 32 (R04p01_digit 0)=R04p01_rowCode 0 := by decide +kernel

private theorem R04p01_row_01 : pack 32 (R04p01_digit 1)=R04p01_rowCode 1 := by decide +kernel

private theorem R04p01_row_02 : pack 32 (R04p01_digit 2)=R04p01_rowCode 2 := by decide +kernel

private theorem R04p01_row_03 : pack 32 (R04p01_digit 3)=R04p01_rowCode 3 := by decide +kernel

private theorem R04p01_row_04 : pack 32 (R04p01_digit 4)=R04p01_rowCode 4 := by decide +kernel

private theorem R04p01_row_05 : pack 32 (R04p01_digit 5)=R04p01_rowCode 5 := by decide +kernel

private theorem R04p01_row_06 : pack 32 (R04p01_digit 6)=R04p01_rowCode 6 := by decide +kernel

private theorem R04p01_row_07 : pack 32 (R04p01_digit 7)=R04p01_rowCode 7 := by decide +kernel

private theorem R04p01_row_08 : pack 32 (R04p01_digit 8)=R04p01_rowCode 8 := by decide +kernel

private theorem R04p01_row_09 : pack 32 (R04p01_digit 9)=R04p01_rowCode 9 := by decide +kernel

private theorem R04p01_row_10 : pack 32 (R04p01_digit 10)=R04p01_rowCode 10 := by decide +kernel

private theorem R04p01_row_11 : pack 32 (R04p01_digit 11)=R04p01_rowCode 11 := by decide +kernel

private theorem R04p01_row_12 : pack 32 (R04p01_digit 12)=R04p01_rowCode 12 := by decide +kernel

private theorem R04p01_row_13 : pack 32 (R04p01_digit 13)=R04p01_rowCode 13 := by decide +kernel

private theorem R04p01_row_14 : pack 32 (R04p01_digit 14)=R04p01_rowCode 14 := by decide +kernel

private theorem R04p01_row_15 : pack 32 (R04p01_digit 15)=R04p01_rowCode 15 := by decide +kernel

private theorem R04p01_row_16 : pack 32 (R04p01_digit 16)=R04p01_rowCode 16 := by decide +kernel

private theorem R04p01_row_17 : pack 32 (R04p01_digit 17)=R04p01_rowCode 17 := by decide +kernel

private theorem R04p01_row_18 : pack 32 (R04p01_digit 18)=R04p01_rowCode 18 := by decide +kernel

private theorem R04p01_row_19 : pack 32 (R04p01_digit 19)=R04p01_rowCode 19 := by decide +kernel

private theorem R04p01_row_20 : pack 32 (R04p01_digit 20)=R04p01_rowCode 20 := by decide +kernel

private theorem R04p01_row_21 : pack 32 (R04p01_digit 21)=R04p01_rowCode 21 := by decide +kernel

theorem R04p01_row_binding : ∀ i : Fin 22,pack 32 (R04p01_digit i)=R04p01_rowCode i := by
  intro i
  fin_cases i
  · exact R04p01_row_00
  · exact R04p01_row_01
  · exact R04p01_row_02
  · exact R04p01_row_03
  · exact R04p01_row_04
  · exact R04p01_row_05
  · exact R04p01_row_06
  · exact R04p01_row_07
  · exact R04p01_row_08
  · exact R04p01_row_09
  · exact R04p01_row_10
  · exact R04p01_row_11
  · exact R04p01_row_12
  · exact R04p01_row_13
  · exact R04p01_row_14
  · exact R04p01_row_15
  · exact R04p01_row_16
  · exact R04p01_row_17
  · exact R04p01_row_18
  · exact R04p01_row_19
  · exact R04p01_row_20
  · exact R04p01_row_21

private theorem R04p01_column_00 : reversePack 32 (fun j : Fin 22 => R04p01_digit j 0)=R04p01_columnCode 0 := by decide +kernel

private theorem R04p01_column_01 : reversePack 32 (fun j : Fin 22 => R04p01_digit j 1)=R04p01_columnCode 1 := by decide +kernel

private theorem R04p01_column_02 : reversePack 32 (fun j : Fin 22 => R04p01_digit j 2)=R04p01_columnCode 2 := by decide +kernel

private theorem R04p01_column_03 : reversePack 32 (fun j : Fin 22 => R04p01_digit j 3)=R04p01_columnCode 3 := by decide +kernel

private theorem R04p01_column_04 : reversePack 32 (fun j : Fin 22 => R04p01_digit j 4)=R04p01_columnCode 4 := by decide +kernel

private theorem R04p01_column_05 : reversePack 32 (fun j : Fin 22 => R04p01_digit j 5)=R04p01_columnCode 5 := by decide +kernel

private theorem R04p01_column_06 : reversePack 32 (fun j : Fin 22 => R04p01_digit j 6)=R04p01_columnCode 6 := by decide +kernel

private theorem R04p01_column_07 : reversePack 32 (fun j : Fin 22 => R04p01_digit j 7)=R04p01_columnCode 7 := by decide +kernel

private theorem R04p01_column_08 : reversePack 32 (fun j : Fin 22 => R04p01_digit j 8)=R04p01_columnCode 8 := by decide +kernel

private theorem R04p01_column_09 : reversePack 32 (fun j : Fin 22 => R04p01_digit j 9)=R04p01_columnCode 9 := by decide +kernel

private theorem R04p01_column_10 : reversePack 32 (fun j : Fin 22 => R04p01_digit j 10)=R04p01_columnCode 10 := by decide +kernel

private theorem R04p01_column_11 : reversePack 32 (fun j : Fin 22 => R04p01_digit j 11)=R04p01_columnCode 11 := by decide +kernel

private theorem R04p01_column_12 : reversePack 32 (fun j : Fin 22 => R04p01_digit j 12)=R04p01_columnCode 12 := by decide +kernel

private theorem R04p01_column_13 : reversePack 32 (fun j : Fin 22 => R04p01_digit j 13)=R04p01_columnCode 13 := by decide +kernel

private theorem R04p01_column_14 : reversePack 32 (fun j : Fin 22 => R04p01_digit j 14)=R04p01_columnCode 14 := by decide +kernel

private theorem R04p01_column_15 : reversePack 32 (fun j : Fin 22 => R04p01_digit j 15)=R04p01_columnCode 15 := by decide +kernel

private theorem R04p01_column_16 : reversePack 32 (fun j : Fin 22 => R04p01_digit j 16)=R04p01_columnCode 16 := by decide +kernel

private theorem R04p01_column_17 : reversePack 32 (fun j : Fin 22 => R04p01_digit j 17)=R04p01_columnCode 17 := by decide +kernel

private theorem R04p01_column_18 : reversePack 32 (fun j : Fin 22 => R04p01_digit j 18)=R04p01_columnCode 18 := by decide +kernel

private theorem R04p01_column_19 : reversePack 32 (fun j : Fin 22 => R04p01_digit j 19)=R04p01_columnCode 19 := by decide +kernel

private theorem R04p01_column_20 : reversePack 32 (fun j : Fin 22 => R04p01_digit j 20)=R04p01_columnCode 20 := by decide +kernel

private theorem R04p01_column_21 : reversePack 32 (fun j : Fin 22 => R04p01_digit j 21)=R04p01_columnCode 21 := by decide +kernel

theorem R04p01_column_binding : ∀ i : Fin 22,reversePack 32 (fun j : Fin 22 => R04p01_digit j i)=R04p01_columnCode i := by
  intro i
  fin_cases i
  · exact R04p01_column_00
  · exact R04p01_column_01
  · exact R04p01_column_02
  · exact R04p01_column_03
  · exact R04p01_column_04
  · exact R04p01_column_05
  · exact R04p01_column_06
  · exact R04p01_column_07
  · exact R04p01_column_08
  · exact R04p01_column_09
  · exact R04p01_column_10
  · exact R04p01_column_11
  · exact R04p01_column_12
  · exact R04p01_column_13
  · exact R04p01_column_14
  · exact R04p01_column_15
  · exact R04p01_column_16
  · exact R04p01_column_17
  · exact R04p01_column_18
  · exact R04p01_column_19
  · exact R04p01_column_20
  · exact R04p01_column_21

def R04p01_data : PackedData 22 2 32 where
  raw := R04p01_digit
  digit_lt := R04p01_bound
  rowCode := R04p01_rowCode
  columnCode := R04p01_columnCode
  row_binding := R04p01_row_binding
  column_binding := R04p01_column_binding

def R04p02_lowColumnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 2394769
  | 1 => 1362075
  | 2 => 1374640
  | 3 => 3455682
  | 4 => 2031250
  | 5 => 845986
  | 6 => 835712
  | 7 => 1335810
  | 8 => 703026
  | 9 => 326192
  | 10 => 489616
  | 11 => 193184
  | 12 => 715312
  | 13 => 3420832
  | 14 => 12960
  | 15 => 3197488
  | 16 => 1231408
  | 17 => 3471504
  | 18 => 3576480
  | 19 => 1474564
  | 20 => 2097152
  | 21 => 3416064
  | _ => 0

def R04p02_rowCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 33
  | 1 => 1133906001952
  | 2 => 39614081257132168796771975168
  | 3 => 32
  | 4 => 39932332133229408325469217
  | 5 => 1239187962710953311609029632
  | 6 => 32768
  | 7 => 1276626883035311971354313761
  | 8 => 1024
  | 9 => 1239187962710953345936293889
  | 10 => 1048576
  | 11 => 39932332133229408359056417
  | 12 => 1276626883035348254130734080
  | 13 => 40564857894148243737412734321664
  | 14 => 39932332169257141299840032
  | 15 => 40891953628585681378216018977
  | 16 => 1125899906842624
  | 17 => 40853230223427241001891135488
  | 18 => 40605709914262880714366930420769
  | 19 => 1152922605226819584
  | 20 => 40605711160967631030867880608800
  | 21 => 41833746471012908648904276344833
  | _ => 0

def R04p02_columnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 40564857894111314184151091937281
  | 1 => 41833746434377676044452447158304
  | 2 => 39895769533553846819782688
  | 3 => 1267650639188906968860747399201
  | 4 => 1267689287036238802868556039200
  | 5 => 1267651810334641763878141199360
  | 6 => 1180591620752844817408
  | 7 => 1267650600229382324135181451296
  | 8 => 1267690494781430767948940706816
  | 9 => 39894553201366486596222976
  | 10 => 38686806820451069186834432
  | 11 => 1210107564193170511101952
  | 12 => 39894553201331302225150976
  | 13 => 1210107564193135076605985
  | 14 => 1210107564193135076573184
  | 15 => 39894553201330202712473633
  | 16 => 39894553201330202713522208
  | 17 => 38686806820451070225973281
  | 18 => 1210107564192036639768609
  | 19 => 39614081257132168797846798368
  | 20 => 1
  | 21 => 1099511660577
  | _ => 0

def R04p02_digit (i j : Fin 22) : ℕ := packedDigit 1 (R04p02_lowColumnCode j) i.val

private theorem R04p02_bound_00 : ∀ j : Fin 22,R04p02_digit 0 j<2 := by decide +kernel

private theorem R04p02_bound_01 : ∀ j : Fin 22,R04p02_digit 1 j<2 := by decide +kernel

private theorem R04p02_bound_02 : ∀ j : Fin 22,R04p02_digit 2 j<2 := by decide +kernel

private theorem R04p02_bound_03 : ∀ j : Fin 22,R04p02_digit 3 j<2 := by decide +kernel

private theorem R04p02_bound_04 : ∀ j : Fin 22,R04p02_digit 4 j<2 := by decide +kernel

private theorem R04p02_bound_05 : ∀ j : Fin 22,R04p02_digit 5 j<2 := by decide +kernel

private theorem R04p02_bound_06 : ∀ j : Fin 22,R04p02_digit 6 j<2 := by decide +kernel

private theorem R04p02_bound_07 : ∀ j : Fin 22,R04p02_digit 7 j<2 := by decide +kernel

private theorem R04p02_bound_08 : ∀ j : Fin 22,R04p02_digit 8 j<2 := by decide +kernel

private theorem R04p02_bound_09 : ∀ j : Fin 22,R04p02_digit 9 j<2 := by decide +kernel

private theorem R04p02_bound_10 : ∀ j : Fin 22,R04p02_digit 10 j<2 := by decide +kernel

private theorem R04p02_bound_11 : ∀ j : Fin 22,R04p02_digit 11 j<2 := by decide +kernel

private theorem R04p02_bound_12 : ∀ j : Fin 22,R04p02_digit 12 j<2 := by decide +kernel

private theorem R04p02_bound_13 : ∀ j : Fin 22,R04p02_digit 13 j<2 := by decide +kernel

private theorem R04p02_bound_14 : ∀ j : Fin 22,R04p02_digit 14 j<2 := by decide +kernel

private theorem R04p02_bound_15 : ∀ j : Fin 22,R04p02_digit 15 j<2 := by decide +kernel

private theorem R04p02_bound_16 : ∀ j : Fin 22,R04p02_digit 16 j<2 := by decide +kernel

private theorem R04p02_bound_17 : ∀ j : Fin 22,R04p02_digit 17 j<2 := by decide +kernel

private theorem R04p02_bound_18 : ∀ j : Fin 22,R04p02_digit 18 j<2 := by decide +kernel

private theorem R04p02_bound_19 : ∀ j : Fin 22,R04p02_digit 19 j<2 := by decide +kernel

private theorem R04p02_bound_20 : ∀ j : Fin 22,R04p02_digit 20 j<2 := by decide +kernel

private theorem R04p02_bound_21 : ∀ j : Fin 22,R04p02_digit 21 j<2 := by decide +kernel

theorem R04p02_bound : ∀ i j : Fin 22,R04p02_digit i j<2 := by
  intro i j
  fin_cases i
  · exact R04p02_bound_00 j
  · exact R04p02_bound_01 j
  · exact R04p02_bound_02 j
  · exact R04p02_bound_03 j
  · exact R04p02_bound_04 j
  · exact R04p02_bound_05 j
  · exact R04p02_bound_06 j
  · exact R04p02_bound_07 j
  · exact R04p02_bound_08 j
  · exact R04p02_bound_09 j
  · exact R04p02_bound_10 j
  · exact R04p02_bound_11 j
  · exact R04p02_bound_12 j
  · exact R04p02_bound_13 j
  · exact R04p02_bound_14 j
  · exact R04p02_bound_15 j
  · exact R04p02_bound_16 j
  · exact R04p02_bound_17 j
  · exact R04p02_bound_18 j
  · exact R04p02_bound_19 j
  · exact R04p02_bound_20 j
  · exact R04p02_bound_21 j

private theorem R04p02_row_00 : pack 32 (R04p02_digit 0)=R04p02_rowCode 0 := by decide +kernel

private theorem R04p02_row_01 : pack 32 (R04p02_digit 1)=R04p02_rowCode 1 := by decide +kernel

private theorem R04p02_row_02 : pack 32 (R04p02_digit 2)=R04p02_rowCode 2 := by decide +kernel

private theorem R04p02_row_03 : pack 32 (R04p02_digit 3)=R04p02_rowCode 3 := by decide +kernel

private theorem R04p02_row_04 : pack 32 (R04p02_digit 4)=R04p02_rowCode 4 := by decide +kernel

private theorem R04p02_row_05 : pack 32 (R04p02_digit 5)=R04p02_rowCode 5 := by decide +kernel

private theorem R04p02_row_06 : pack 32 (R04p02_digit 6)=R04p02_rowCode 6 := by decide +kernel

private theorem R04p02_row_07 : pack 32 (R04p02_digit 7)=R04p02_rowCode 7 := by decide +kernel

private theorem R04p02_row_08 : pack 32 (R04p02_digit 8)=R04p02_rowCode 8 := by decide +kernel

private theorem R04p02_row_09 : pack 32 (R04p02_digit 9)=R04p02_rowCode 9 := by decide +kernel

private theorem R04p02_row_10 : pack 32 (R04p02_digit 10)=R04p02_rowCode 10 := by decide +kernel

private theorem R04p02_row_11 : pack 32 (R04p02_digit 11)=R04p02_rowCode 11 := by decide +kernel

private theorem R04p02_row_12 : pack 32 (R04p02_digit 12)=R04p02_rowCode 12 := by decide +kernel

private theorem R04p02_row_13 : pack 32 (R04p02_digit 13)=R04p02_rowCode 13 := by decide +kernel

private theorem R04p02_row_14 : pack 32 (R04p02_digit 14)=R04p02_rowCode 14 := by decide +kernel

private theorem R04p02_row_15 : pack 32 (R04p02_digit 15)=R04p02_rowCode 15 := by decide +kernel

private theorem R04p02_row_16 : pack 32 (R04p02_digit 16)=R04p02_rowCode 16 := by decide +kernel

private theorem R04p02_row_17 : pack 32 (R04p02_digit 17)=R04p02_rowCode 17 := by decide +kernel

private theorem R04p02_row_18 : pack 32 (R04p02_digit 18)=R04p02_rowCode 18 := by decide +kernel

private theorem R04p02_row_19 : pack 32 (R04p02_digit 19)=R04p02_rowCode 19 := by decide +kernel

private theorem R04p02_row_20 : pack 32 (R04p02_digit 20)=R04p02_rowCode 20 := by decide +kernel

private theorem R04p02_row_21 : pack 32 (R04p02_digit 21)=R04p02_rowCode 21 := by decide +kernel

theorem R04p02_row_binding : ∀ i : Fin 22,pack 32 (R04p02_digit i)=R04p02_rowCode i := by
  intro i
  fin_cases i
  · exact R04p02_row_00
  · exact R04p02_row_01
  · exact R04p02_row_02
  · exact R04p02_row_03
  · exact R04p02_row_04
  · exact R04p02_row_05
  · exact R04p02_row_06
  · exact R04p02_row_07
  · exact R04p02_row_08
  · exact R04p02_row_09
  · exact R04p02_row_10
  · exact R04p02_row_11
  · exact R04p02_row_12
  · exact R04p02_row_13
  · exact R04p02_row_14
  · exact R04p02_row_15
  · exact R04p02_row_16
  · exact R04p02_row_17
  · exact R04p02_row_18
  · exact R04p02_row_19
  · exact R04p02_row_20
  · exact R04p02_row_21

private theorem R04p02_column_00 : reversePack 32 (fun j : Fin 22 => R04p02_digit j 0)=R04p02_columnCode 0 := by decide +kernel

private theorem R04p02_column_01 : reversePack 32 (fun j : Fin 22 => R04p02_digit j 1)=R04p02_columnCode 1 := by decide +kernel

private theorem R04p02_column_02 : reversePack 32 (fun j : Fin 22 => R04p02_digit j 2)=R04p02_columnCode 2 := by decide +kernel

private theorem R04p02_column_03 : reversePack 32 (fun j : Fin 22 => R04p02_digit j 3)=R04p02_columnCode 3 := by decide +kernel

private theorem R04p02_column_04 : reversePack 32 (fun j : Fin 22 => R04p02_digit j 4)=R04p02_columnCode 4 := by decide +kernel

private theorem R04p02_column_05 : reversePack 32 (fun j : Fin 22 => R04p02_digit j 5)=R04p02_columnCode 5 := by decide +kernel

private theorem R04p02_column_06 : reversePack 32 (fun j : Fin 22 => R04p02_digit j 6)=R04p02_columnCode 6 := by decide +kernel

private theorem R04p02_column_07 : reversePack 32 (fun j : Fin 22 => R04p02_digit j 7)=R04p02_columnCode 7 := by decide +kernel

private theorem R04p02_column_08 : reversePack 32 (fun j : Fin 22 => R04p02_digit j 8)=R04p02_columnCode 8 := by decide +kernel

private theorem R04p02_column_09 : reversePack 32 (fun j : Fin 22 => R04p02_digit j 9)=R04p02_columnCode 9 := by decide +kernel

private theorem R04p02_column_10 : reversePack 32 (fun j : Fin 22 => R04p02_digit j 10)=R04p02_columnCode 10 := by decide +kernel

private theorem R04p02_column_11 : reversePack 32 (fun j : Fin 22 => R04p02_digit j 11)=R04p02_columnCode 11 := by decide +kernel

private theorem R04p02_column_12 : reversePack 32 (fun j : Fin 22 => R04p02_digit j 12)=R04p02_columnCode 12 := by decide +kernel

private theorem R04p02_column_13 : reversePack 32 (fun j : Fin 22 => R04p02_digit j 13)=R04p02_columnCode 13 := by decide +kernel

private theorem R04p02_column_14 : reversePack 32 (fun j : Fin 22 => R04p02_digit j 14)=R04p02_columnCode 14 := by decide +kernel

private theorem R04p02_column_15 : reversePack 32 (fun j : Fin 22 => R04p02_digit j 15)=R04p02_columnCode 15 := by decide +kernel

private theorem R04p02_column_16 : reversePack 32 (fun j : Fin 22 => R04p02_digit j 16)=R04p02_columnCode 16 := by decide +kernel

private theorem R04p02_column_17 : reversePack 32 (fun j : Fin 22 => R04p02_digit j 17)=R04p02_columnCode 17 := by decide +kernel

private theorem R04p02_column_18 : reversePack 32 (fun j : Fin 22 => R04p02_digit j 18)=R04p02_columnCode 18 := by decide +kernel

private theorem R04p02_column_19 : reversePack 32 (fun j : Fin 22 => R04p02_digit j 19)=R04p02_columnCode 19 := by decide +kernel

private theorem R04p02_column_20 : reversePack 32 (fun j : Fin 22 => R04p02_digit j 20)=R04p02_columnCode 20 := by decide +kernel

private theorem R04p02_column_21 : reversePack 32 (fun j : Fin 22 => R04p02_digit j 21)=R04p02_columnCode 21 := by decide +kernel

theorem R04p02_column_binding : ∀ i : Fin 22,reversePack 32 (fun j : Fin 22 => R04p02_digit j i)=R04p02_columnCode i := by
  intro i
  fin_cases i
  · exact R04p02_column_00
  · exact R04p02_column_01
  · exact R04p02_column_02
  · exact R04p02_column_03
  · exact R04p02_column_04
  · exact R04p02_column_05
  · exact R04p02_column_06
  · exact R04p02_column_07
  · exact R04p02_column_08
  · exact R04p02_column_09
  · exact R04p02_column_10
  · exact R04p02_column_11
  · exact R04p02_column_12
  · exact R04p02_column_13
  · exact R04p02_column_14
  · exact R04p02_column_15
  · exact R04p02_column_16
  · exact R04p02_column_17
  · exact R04p02_column_18
  · exact R04p02_column_19
  · exact R04p02_column_20
  · exact R04p02_column_21

def R04p02_data : PackedData 22 2 32 where
  raw := R04p02_digit
  digit_lt := R04p02_bound
  rowCode := R04p02_rowCode
  columnCode := R04p02_columnCode
  row_binding := R04p02_row_binding
  column_binding := R04p02_column_binding

def R04p03_lowColumnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 2114050
  | 1 => 2156699
  | 2 => 1048584
  | 3 => 1048580
  | 4 => 2243510
  | 5 => 1339638
  | 6 => 2259092
  | 7 => 2636948
  | 8 => 1323684
  | 9 => 2892438
  | 10 => 792592
  | 11 => 526482
  | 12 => 2371588
  | 13 => 1122308
  | 14 => 16384
  | 15 => 2760708
  | 16 => 3416064
  | 17 => 2255412
  | 18 => 2105348
  | 19 => 2269188
  | 20 => 3172916
  | 21 => 2097152
  | _ => 0

def R04p03_rowCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 32
  | 1 => 36063981425655841
  | 2 => 1308541344967852927630504394752
  | 3 => 1056
  | 4 => 1267689285854494259547059781664
  | 5 => 1267689285854457070729840033792
  | 6 => 33554432
  | 7 => 36065116370763808
  | 8 => 1048576
  | 9 => 1267689285854457105914178568193
  | 10 => 34359738368
  | 11 => 1267689285854494224362654138400
  | 12 => 1154048539493400576
  | 13 => 1308542553893672542259679068192
  | 14 => 1267689287035048690348812402721
  | 15 => 39614081257132168796771975200
  | 16 => 36893488147419103232
  | 17 => 39652804662291699888599072768
  | 18 => 1208926973698317605666816
  | 19 => 37778969052872819343360
  | 20 => 1267651809190942505372842230784
  | 21 => 41873361761160119900907217354785
  | _ => 0

def R04p03_columnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1267650600229382323035669790721
  | 1 => 41833746434377676045551958753281
  | 2 => 1237940039285380274899124256
  | 3 => 39614081257132168796771975200
  | 4 => 1307304577256048045609469345793
  | 5 => 1307304614996932373049056985120
  | 6 => 39652768063952619865925222401
  | 7 => 39652768063988648628583400449
  | 8 => 39615291364696361931848581152
  | 9 => 1307303368293333781748595590145
  | 10 => 38685626228829217869562880
  | 11 => 1267689287035049816247611950080
  | 12 => 39614081257132205080655724545
  | 13 => 39614081257132169896317157408
  | 14 => 34359738368
  | 15 => 39614081257132169896284652545
  | 16 => 1099511660577
  | 17 => 39653975810333500097923383297
  | 18 => 39614081257132169896283602945
  | 19 => 39614081257132169897358393345
  | 20 => 39653975810333500097922334753
  | 21 => 1
  | _ => 0

def R04p03_digit (i j : Fin 22) : ℕ := packedDigit 1 (R04p03_lowColumnCode j) i.val

private theorem R04p03_bound_00 : ∀ j : Fin 22,R04p03_digit 0 j<2 := by decide +kernel

private theorem R04p03_bound_01 : ∀ j : Fin 22,R04p03_digit 1 j<2 := by decide +kernel

private theorem R04p03_bound_02 : ∀ j : Fin 22,R04p03_digit 2 j<2 := by decide +kernel

private theorem R04p03_bound_03 : ∀ j : Fin 22,R04p03_digit 3 j<2 := by decide +kernel

private theorem R04p03_bound_04 : ∀ j : Fin 22,R04p03_digit 4 j<2 := by decide +kernel

private theorem R04p03_bound_05 : ∀ j : Fin 22,R04p03_digit 5 j<2 := by decide +kernel

private theorem R04p03_bound_06 : ∀ j : Fin 22,R04p03_digit 6 j<2 := by decide +kernel

private theorem R04p03_bound_07 : ∀ j : Fin 22,R04p03_digit 7 j<2 := by decide +kernel

private theorem R04p03_bound_08 : ∀ j : Fin 22,R04p03_digit 8 j<2 := by decide +kernel

private theorem R04p03_bound_09 : ∀ j : Fin 22,R04p03_digit 9 j<2 := by decide +kernel

private theorem R04p03_bound_10 : ∀ j : Fin 22,R04p03_digit 10 j<2 := by decide +kernel

private theorem R04p03_bound_11 : ∀ j : Fin 22,R04p03_digit 11 j<2 := by decide +kernel

private theorem R04p03_bound_12 : ∀ j : Fin 22,R04p03_digit 12 j<2 := by decide +kernel

private theorem R04p03_bound_13 : ∀ j : Fin 22,R04p03_digit 13 j<2 := by decide +kernel

private theorem R04p03_bound_14 : ∀ j : Fin 22,R04p03_digit 14 j<2 := by decide +kernel

private theorem R04p03_bound_15 : ∀ j : Fin 22,R04p03_digit 15 j<2 := by decide +kernel

private theorem R04p03_bound_16 : ∀ j : Fin 22,R04p03_digit 16 j<2 := by decide +kernel

private theorem R04p03_bound_17 : ∀ j : Fin 22,R04p03_digit 17 j<2 := by decide +kernel

private theorem R04p03_bound_18 : ∀ j : Fin 22,R04p03_digit 18 j<2 := by decide +kernel

private theorem R04p03_bound_19 : ∀ j : Fin 22,R04p03_digit 19 j<2 := by decide +kernel

private theorem R04p03_bound_20 : ∀ j : Fin 22,R04p03_digit 20 j<2 := by decide +kernel

private theorem R04p03_bound_21 : ∀ j : Fin 22,R04p03_digit 21 j<2 := by decide +kernel

theorem R04p03_bound : ∀ i j : Fin 22,R04p03_digit i j<2 := by
  intro i j
  fin_cases i
  · exact R04p03_bound_00 j
  · exact R04p03_bound_01 j
  · exact R04p03_bound_02 j
  · exact R04p03_bound_03 j
  · exact R04p03_bound_04 j
  · exact R04p03_bound_05 j
  · exact R04p03_bound_06 j
  · exact R04p03_bound_07 j
  · exact R04p03_bound_08 j
  · exact R04p03_bound_09 j
  · exact R04p03_bound_10 j
  · exact R04p03_bound_11 j
  · exact R04p03_bound_12 j
  · exact R04p03_bound_13 j
  · exact R04p03_bound_14 j
  · exact R04p03_bound_15 j
  · exact R04p03_bound_16 j
  · exact R04p03_bound_17 j
  · exact R04p03_bound_18 j
  · exact R04p03_bound_19 j
  · exact R04p03_bound_20 j
  · exact R04p03_bound_21 j

private theorem R04p03_row_00 : pack 32 (R04p03_digit 0)=R04p03_rowCode 0 := by decide +kernel

private theorem R04p03_row_01 : pack 32 (R04p03_digit 1)=R04p03_rowCode 1 := by decide +kernel

private theorem R04p03_row_02 : pack 32 (R04p03_digit 2)=R04p03_rowCode 2 := by decide +kernel

private theorem R04p03_row_03 : pack 32 (R04p03_digit 3)=R04p03_rowCode 3 := by decide +kernel

private theorem R04p03_row_04 : pack 32 (R04p03_digit 4)=R04p03_rowCode 4 := by decide +kernel

private theorem R04p03_row_05 : pack 32 (R04p03_digit 5)=R04p03_rowCode 5 := by decide +kernel

private theorem R04p03_row_06 : pack 32 (R04p03_digit 6)=R04p03_rowCode 6 := by decide +kernel

private theorem R04p03_row_07 : pack 32 (R04p03_digit 7)=R04p03_rowCode 7 := by decide +kernel

private theorem R04p03_row_08 : pack 32 (R04p03_digit 8)=R04p03_rowCode 8 := by decide +kernel

private theorem R04p03_row_09 : pack 32 (R04p03_digit 9)=R04p03_rowCode 9 := by decide +kernel

private theorem R04p03_row_10 : pack 32 (R04p03_digit 10)=R04p03_rowCode 10 := by decide +kernel

private theorem R04p03_row_11 : pack 32 (R04p03_digit 11)=R04p03_rowCode 11 := by decide +kernel

private theorem R04p03_row_12 : pack 32 (R04p03_digit 12)=R04p03_rowCode 12 := by decide +kernel

private theorem R04p03_row_13 : pack 32 (R04p03_digit 13)=R04p03_rowCode 13 := by decide +kernel

private theorem R04p03_row_14 : pack 32 (R04p03_digit 14)=R04p03_rowCode 14 := by decide +kernel

private theorem R04p03_row_15 : pack 32 (R04p03_digit 15)=R04p03_rowCode 15 := by decide +kernel

private theorem R04p03_row_16 : pack 32 (R04p03_digit 16)=R04p03_rowCode 16 := by decide +kernel

private theorem R04p03_row_17 : pack 32 (R04p03_digit 17)=R04p03_rowCode 17 := by decide +kernel

private theorem R04p03_row_18 : pack 32 (R04p03_digit 18)=R04p03_rowCode 18 := by decide +kernel

private theorem R04p03_row_19 : pack 32 (R04p03_digit 19)=R04p03_rowCode 19 := by decide +kernel

private theorem R04p03_row_20 : pack 32 (R04p03_digit 20)=R04p03_rowCode 20 := by decide +kernel

private theorem R04p03_row_21 : pack 32 (R04p03_digit 21)=R04p03_rowCode 21 := by decide +kernel

theorem R04p03_row_binding : ∀ i : Fin 22,pack 32 (R04p03_digit i)=R04p03_rowCode i := by
  intro i
  fin_cases i
  · exact R04p03_row_00
  · exact R04p03_row_01
  · exact R04p03_row_02
  · exact R04p03_row_03
  · exact R04p03_row_04
  · exact R04p03_row_05
  · exact R04p03_row_06
  · exact R04p03_row_07
  · exact R04p03_row_08
  · exact R04p03_row_09
  · exact R04p03_row_10
  · exact R04p03_row_11
  · exact R04p03_row_12
  · exact R04p03_row_13
  · exact R04p03_row_14
  · exact R04p03_row_15
  · exact R04p03_row_16
  · exact R04p03_row_17
  · exact R04p03_row_18
  · exact R04p03_row_19
  · exact R04p03_row_20
  · exact R04p03_row_21

private theorem R04p03_column_00 : reversePack 32 (fun j : Fin 22 => R04p03_digit j 0)=R04p03_columnCode 0 := by decide +kernel

private theorem R04p03_column_01 : reversePack 32 (fun j : Fin 22 => R04p03_digit j 1)=R04p03_columnCode 1 := by decide +kernel

private theorem R04p03_column_02 : reversePack 32 (fun j : Fin 22 => R04p03_digit j 2)=R04p03_columnCode 2 := by decide +kernel

private theorem R04p03_column_03 : reversePack 32 (fun j : Fin 22 => R04p03_digit j 3)=R04p03_columnCode 3 := by decide +kernel

private theorem R04p03_column_04 : reversePack 32 (fun j : Fin 22 => R04p03_digit j 4)=R04p03_columnCode 4 := by decide +kernel

private theorem R04p03_column_05 : reversePack 32 (fun j : Fin 22 => R04p03_digit j 5)=R04p03_columnCode 5 := by decide +kernel

private theorem R04p03_column_06 : reversePack 32 (fun j : Fin 22 => R04p03_digit j 6)=R04p03_columnCode 6 := by decide +kernel

private theorem R04p03_column_07 : reversePack 32 (fun j : Fin 22 => R04p03_digit j 7)=R04p03_columnCode 7 := by decide +kernel

private theorem R04p03_column_08 : reversePack 32 (fun j : Fin 22 => R04p03_digit j 8)=R04p03_columnCode 8 := by decide +kernel

private theorem R04p03_column_09 : reversePack 32 (fun j : Fin 22 => R04p03_digit j 9)=R04p03_columnCode 9 := by decide +kernel

private theorem R04p03_column_10 : reversePack 32 (fun j : Fin 22 => R04p03_digit j 10)=R04p03_columnCode 10 := by decide +kernel

private theorem R04p03_column_11 : reversePack 32 (fun j : Fin 22 => R04p03_digit j 11)=R04p03_columnCode 11 := by decide +kernel

private theorem R04p03_column_12 : reversePack 32 (fun j : Fin 22 => R04p03_digit j 12)=R04p03_columnCode 12 := by decide +kernel

private theorem R04p03_column_13 : reversePack 32 (fun j : Fin 22 => R04p03_digit j 13)=R04p03_columnCode 13 := by decide +kernel

private theorem R04p03_column_14 : reversePack 32 (fun j : Fin 22 => R04p03_digit j 14)=R04p03_columnCode 14 := by decide +kernel

private theorem R04p03_column_15 : reversePack 32 (fun j : Fin 22 => R04p03_digit j 15)=R04p03_columnCode 15 := by decide +kernel

private theorem R04p03_column_16 : reversePack 32 (fun j : Fin 22 => R04p03_digit j 16)=R04p03_columnCode 16 := by decide +kernel

private theorem R04p03_column_17 : reversePack 32 (fun j : Fin 22 => R04p03_digit j 17)=R04p03_columnCode 17 := by decide +kernel

private theorem R04p03_column_18 : reversePack 32 (fun j : Fin 22 => R04p03_digit j 18)=R04p03_columnCode 18 := by decide +kernel

private theorem R04p03_column_19 : reversePack 32 (fun j : Fin 22 => R04p03_digit j 19)=R04p03_columnCode 19 := by decide +kernel

private theorem R04p03_column_20 : reversePack 32 (fun j : Fin 22 => R04p03_digit j 20)=R04p03_columnCode 20 := by decide +kernel

private theorem R04p03_column_21 : reversePack 32 (fun j : Fin 22 => R04p03_digit j 21)=R04p03_columnCode 21 := by decide +kernel

theorem R04p03_column_binding : ∀ i : Fin 22,reversePack 32 (fun j : Fin 22 => R04p03_digit j i)=R04p03_columnCode i := by
  intro i
  fin_cases i
  · exact R04p03_column_00
  · exact R04p03_column_01
  · exact R04p03_column_02
  · exact R04p03_column_03
  · exact R04p03_column_04
  · exact R04p03_column_05
  · exact R04p03_column_06
  · exact R04p03_column_07
  · exact R04p03_column_08
  · exact R04p03_column_09
  · exact R04p03_column_10
  · exact R04p03_column_11
  · exact R04p03_column_12
  · exact R04p03_column_13
  · exact R04p03_column_14
  · exact R04p03_column_15
  · exact R04p03_column_16
  · exact R04p03_column_17
  · exact R04p03_column_18
  · exact R04p03_column_19
  · exact R04p03_column_20
  · exact R04p03_column_21

def R04p03_data : PackedData 22 2 32 where
  raw := R04p03_digit
  digit_lt := R04p03_bound
  rowCode := R04p03_rowCode
  columnCode := R04p03_columnCode
  row_binding := R04p03_row_binding
  column_binding := R04p03_column_binding

end SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoCaches01
