import SymmetricSubgroupAsymptotics.MatrixKroneckerProductReflection
import Mathlib.Tactic.FinCases

/-! Fixed Co2 binary22 shared caches. Every digit and pack binding is kernel checked. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoCaches00
open MatrixKroneckerProductReflection MatrixKroneckerDotReflection
open MatrixNaturalRowDotReflection SmallNaturalMatrixProductReflection

def B3_lowColumnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1114132
  | 1 => 1638402
  | 2 => 1638534
  | 3 => 1641984
  | 4 => 1114118
  | 5 => 1645568
  | 6 => 9216
  | 7 => 1638407
  | 8 => 1132544
  | 9 => 1674240
  | 10 => 1246208
  | 11 => 1902592
  | 12 => 1641480
  | 13 => 1639424
  | 14 => 1640448
  | 15 => 1641504
  | 16 => 2686976
  | 17 => 1639488
  | 18 => 2304
  | 19 => 1114112
  | 20 => 65536
  | 21 => 1572864
  | _ => 0

def B3_rowCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 34359738368
  | 1 => 34360788000
  | 2 => 34360787969
  | 3 => 1152921504606846976
  | 4 => 1
  | 5 => 37778931862957161709568
  | 6 => 38685626227668133590597632
  | 7 => 1024
  | 8 => 1237940039285380274899124224
  | 9 => 32768
  | 10 => 38723443207101828164517888
  | 11 => 1237978999997850535015251968
  | 12 => 33554432
  | 13 => 1073741824
  | 14 => 1099511627776
  | 15 => 35184372088832
  | 16 => 1307304615035015937398043345953
  | 17 => 1125899906842624
  | 18 => 36028797018963968
  | 19 => 40564859140852994087999651218464
  | 20 => 40604472013184307769166668006433
  | 21 => 1208925819614629174706176
  | _ => 0

def B3_columnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 39652766883359836930396127264
  | 1 => 1267650600228229401496736760864
  | 2 => 1307264682665953191010920039456
  | 3 => 1190076201566209056
  | 4 => 1307264681485361570293508735008
  | 5 => 37189881331450912
  | 6 => 36029896530591744
  | 7 => 41872083888788702418188011308064
  | 8 => 1125934300135456
  | 9 => 37154698033103904
  | 10 => 36028797053567008
  | 11 => 1125899940430880
  | 12 => 1237940039322534971858486304
  | 13 => 36028797052519456
  | 14 => 1125899940398112
  | 15 => 1208925856769326134068256
  | 16 => 33555457
  | 17 => 37778967891754214229024
  | 18 => 36894614047325945856
  | 19 => 33554464
  | 20 => 33554432
  | 21 => 1056
  | _ => 0

def B3_digit (i j : Fin 22) : ℕ := packedDigit 1 (B3_lowColumnCode j) i.val

private theorem B3_bound_00 : ∀ j : Fin 22,B3_digit 0 j<2 := by decide +kernel

private theorem B3_bound_01 : ∀ j : Fin 22,B3_digit 1 j<2 := by decide +kernel

private theorem B3_bound_02 : ∀ j : Fin 22,B3_digit 2 j<2 := by decide +kernel

private theorem B3_bound_03 : ∀ j : Fin 22,B3_digit 3 j<2 := by decide +kernel

private theorem B3_bound_04 : ∀ j : Fin 22,B3_digit 4 j<2 := by decide +kernel

private theorem B3_bound_05 : ∀ j : Fin 22,B3_digit 5 j<2 := by decide +kernel

private theorem B3_bound_06 : ∀ j : Fin 22,B3_digit 6 j<2 := by decide +kernel

private theorem B3_bound_07 : ∀ j : Fin 22,B3_digit 7 j<2 := by decide +kernel

private theorem B3_bound_08 : ∀ j : Fin 22,B3_digit 8 j<2 := by decide +kernel

private theorem B3_bound_09 : ∀ j : Fin 22,B3_digit 9 j<2 := by decide +kernel

private theorem B3_bound_10 : ∀ j : Fin 22,B3_digit 10 j<2 := by decide +kernel

private theorem B3_bound_11 : ∀ j : Fin 22,B3_digit 11 j<2 := by decide +kernel

private theorem B3_bound_12 : ∀ j : Fin 22,B3_digit 12 j<2 := by decide +kernel

private theorem B3_bound_13 : ∀ j : Fin 22,B3_digit 13 j<2 := by decide +kernel

private theorem B3_bound_14 : ∀ j : Fin 22,B3_digit 14 j<2 := by decide +kernel

private theorem B3_bound_15 : ∀ j : Fin 22,B3_digit 15 j<2 := by decide +kernel

private theorem B3_bound_16 : ∀ j : Fin 22,B3_digit 16 j<2 := by decide +kernel

private theorem B3_bound_17 : ∀ j : Fin 22,B3_digit 17 j<2 := by decide +kernel

private theorem B3_bound_18 : ∀ j : Fin 22,B3_digit 18 j<2 := by decide +kernel

private theorem B3_bound_19 : ∀ j : Fin 22,B3_digit 19 j<2 := by decide +kernel

private theorem B3_bound_20 : ∀ j : Fin 22,B3_digit 20 j<2 := by decide +kernel

private theorem B3_bound_21 : ∀ j : Fin 22,B3_digit 21 j<2 := by decide +kernel

theorem B3_bound : ∀ i j : Fin 22,B3_digit i j<2 := by
  intro i j
  fin_cases i
  · exact B3_bound_00 j
  · exact B3_bound_01 j
  · exact B3_bound_02 j
  · exact B3_bound_03 j
  · exact B3_bound_04 j
  · exact B3_bound_05 j
  · exact B3_bound_06 j
  · exact B3_bound_07 j
  · exact B3_bound_08 j
  · exact B3_bound_09 j
  · exact B3_bound_10 j
  · exact B3_bound_11 j
  · exact B3_bound_12 j
  · exact B3_bound_13 j
  · exact B3_bound_14 j
  · exact B3_bound_15 j
  · exact B3_bound_16 j
  · exact B3_bound_17 j
  · exact B3_bound_18 j
  · exact B3_bound_19 j
  · exact B3_bound_20 j
  · exact B3_bound_21 j

private theorem B3_row_00 : pack 32 (B3_digit 0)=B3_rowCode 0 := by decide +kernel

private theorem B3_row_01 : pack 32 (B3_digit 1)=B3_rowCode 1 := by decide +kernel

private theorem B3_row_02 : pack 32 (B3_digit 2)=B3_rowCode 2 := by decide +kernel

private theorem B3_row_03 : pack 32 (B3_digit 3)=B3_rowCode 3 := by decide +kernel

private theorem B3_row_04 : pack 32 (B3_digit 4)=B3_rowCode 4 := by decide +kernel

private theorem B3_row_05 : pack 32 (B3_digit 5)=B3_rowCode 5 := by decide +kernel

private theorem B3_row_06 : pack 32 (B3_digit 6)=B3_rowCode 6 := by decide +kernel

private theorem B3_row_07 : pack 32 (B3_digit 7)=B3_rowCode 7 := by decide +kernel

private theorem B3_row_08 : pack 32 (B3_digit 8)=B3_rowCode 8 := by decide +kernel

private theorem B3_row_09 : pack 32 (B3_digit 9)=B3_rowCode 9 := by decide +kernel

private theorem B3_row_10 : pack 32 (B3_digit 10)=B3_rowCode 10 := by decide +kernel

private theorem B3_row_11 : pack 32 (B3_digit 11)=B3_rowCode 11 := by decide +kernel

private theorem B3_row_12 : pack 32 (B3_digit 12)=B3_rowCode 12 := by decide +kernel

private theorem B3_row_13 : pack 32 (B3_digit 13)=B3_rowCode 13 := by decide +kernel

private theorem B3_row_14 : pack 32 (B3_digit 14)=B3_rowCode 14 := by decide +kernel

private theorem B3_row_15 : pack 32 (B3_digit 15)=B3_rowCode 15 := by decide +kernel

private theorem B3_row_16 : pack 32 (B3_digit 16)=B3_rowCode 16 := by decide +kernel

private theorem B3_row_17 : pack 32 (B3_digit 17)=B3_rowCode 17 := by decide +kernel

private theorem B3_row_18 : pack 32 (B3_digit 18)=B3_rowCode 18 := by decide +kernel

private theorem B3_row_19 : pack 32 (B3_digit 19)=B3_rowCode 19 := by decide +kernel

private theorem B3_row_20 : pack 32 (B3_digit 20)=B3_rowCode 20 := by decide +kernel

private theorem B3_row_21 : pack 32 (B3_digit 21)=B3_rowCode 21 := by decide +kernel

theorem B3_row_binding : ∀ i : Fin 22,pack 32 (B3_digit i)=B3_rowCode i := by
  intro i
  fin_cases i
  · exact B3_row_00
  · exact B3_row_01
  · exact B3_row_02
  · exact B3_row_03
  · exact B3_row_04
  · exact B3_row_05
  · exact B3_row_06
  · exact B3_row_07
  · exact B3_row_08
  · exact B3_row_09
  · exact B3_row_10
  · exact B3_row_11
  · exact B3_row_12
  · exact B3_row_13
  · exact B3_row_14
  · exact B3_row_15
  · exact B3_row_16
  · exact B3_row_17
  · exact B3_row_18
  · exact B3_row_19
  · exact B3_row_20
  · exact B3_row_21

private theorem B3_column_00 : reversePack 32 (fun j : Fin 22 => B3_digit j 0)=B3_columnCode 0 := by decide +kernel

private theorem B3_column_01 : reversePack 32 (fun j : Fin 22 => B3_digit j 1)=B3_columnCode 1 := by decide +kernel

private theorem B3_column_02 : reversePack 32 (fun j : Fin 22 => B3_digit j 2)=B3_columnCode 2 := by decide +kernel

private theorem B3_column_03 : reversePack 32 (fun j : Fin 22 => B3_digit j 3)=B3_columnCode 3 := by decide +kernel

private theorem B3_column_04 : reversePack 32 (fun j : Fin 22 => B3_digit j 4)=B3_columnCode 4 := by decide +kernel

private theorem B3_column_05 : reversePack 32 (fun j : Fin 22 => B3_digit j 5)=B3_columnCode 5 := by decide +kernel

private theorem B3_column_06 : reversePack 32 (fun j : Fin 22 => B3_digit j 6)=B3_columnCode 6 := by decide +kernel

private theorem B3_column_07 : reversePack 32 (fun j : Fin 22 => B3_digit j 7)=B3_columnCode 7 := by decide +kernel

private theorem B3_column_08 : reversePack 32 (fun j : Fin 22 => B3_digit j 8)=B3_columnCode 8 := by decide +kernel

private theorem B3_column_09 : reversePack 32 (fun j : Fin 22 => B3_digit j 9)=B3_columnCode 9 := by decide +kernel

private theorem B3_column_10 : reversePack 32 (fun j : Fin 22 => B3_digit j 10)=B3_columnCode 10 := by decide +kernel

private theorem B3_column_11 : reversePack 32 (fun j : Fin 22 => B3_digit j 11)=B3_columnCode 11 := by decide +kernel

private theorem B3_column_12 : reversePack 32 (fun j : Fin 22 => B3_digit j 12)=B3_columnCode 12 := by decide +kernel

private theorem B3_column_13 : reversePack 32 (fun j : Fin 22 => B3_digit j 13)=B3_columnCode 13 := by decide +kernel

private theorem B3_column_14 : reversePack 32 (fun j : Fin 22 => B3_digit j 14)=B3_columnCode 14 := by decide +kernel

private theorem B3_column_15 : reversePack 32 (fun j : Fin 22 => B3_digit j 15)=B3_columnCode 15 := by decide +kernel

private theorem B3_column_16 : reversePack 32 (fun j : Fin 22 => B3_digit j 16)=B3_columnCode 16 := by decide +kernel

private theorem B3_column_17 : reversePack 32 (fun j : Fin 22 => B3_digit j 17)=B3_columnCode 17 := by decide +kernel

private theorem B3_column_18 : reversePack 32 (fun j : Fin 22 => B3_digit j 18)=B3_columnCode 18 := by decide +kernel

private theorem B3_column_19 : reversePack 32 (fun j : Fin 22 => B3_digit j 19)=B3_columnCode 19 := by decide +kernel

private theorem B3_column_20 : reversePack 32 (fun j : Fin 22 => B3_digit j 20)=B3_columnCode 20 := by decide +kernel

private theorem B3_column_21 : reversePack 32 (fun j : Fin 22 => B3_digit j 21)=B3_columnCode 21 := by decide +kernel

theorem B3_column_binding : ∀ i : Fin 22,reversePack 32 (fun j : Fin 22 => B3_digit j i)=B3_columnCode i := by
  intro i
  fin_cases i
  · exact B3_column_00
  · exact B3_column_01
  · exact B3_column_02
  · exact B3_column_03
  · exact B3_column_04
  · exact B3_column_05
  · exact B3_column_06
  · exact B3_column_07
  · exact B3_column_08
  · exact B3_column_09
  · exact B3_column_10
  · exact B3_column_11
  · exact B3_column_12
  · exact B3_column_13
  · exact B3_column_14
  · exact B3_column_15
  · exact B3_column_16
  · exact B3_column_17
  · exact B3_column_18
  · exact B3_column_19
  · exact B3_column_20
  · exact B3_column_21

def B3_data : PackedData 22 2 32 where
  raw := B3_digit
  digit_lt := B3_bound
  rowCode := B3_rowCode
  columnCode := B3_columnCode
  row_binding := B3_row_binding
  column_binding := B3_column_binding

def R03p01_lowColumnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 3201088
  | 1 => 1065473
  | 2 => 1088193
  | 3 => 348160
  | 4 => 3561667
  | 5 => 737280
  | 6 => 3604480
  | 7 => 2152648
  | 8 => 3424256
  | 9 => 1392644
  | 10 => 327680
  | 11 => 3162112
  | 12 => 3494784
  | 13 => 219280
  | 14 => 447136
  | 15 => 344576
  | 16 => 1048576
  | 17 => 230400
  | 18 => 18432
  | 19 => 3571712
  | 20 => 1474560
  | 21 => 1220608
  | _ => 0

def R03p01_rowCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1049632
  | 1 => 1048576
  | 2 => 35184372088832
  | 3 => 34359738368
  | 4 => 36893488147419103232
  | 5 => 1180591620717411303424
  | 6 => 34360787969
  | 7 => 1218638030403798041600
  | 8 => 1152921504606846976
  | 9 => 38960676405179179861024
  | 10 => 38685626227668133590597632
  | 11 => 1237940076178868456679015425
  | 12 => 1218638030403798074369
  | 13 => 40564819207303340847894502572032
  | 14 => 1237979036891338716795142177
  | 15 => 41872122575595521707073339393025
  | 16 => 38723443207101828164517888
  | 17 => 41872122575632415195187507101696
  | 18 => 1307264720446039137657520422912
  | 19 => 33554432
  | 20 => 41872085097715711019403736777761
  | 21 => 39614081258321120233343942657
  | _ => 0

def R03p01_columnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 37778933024076874121249
  | 1 => 40564819207304493769433469157408
  | 2 => 40564819246264018414159035105312
  | 3 => 35218765414400
  | 4 => 41832469846491094894184418541601
  | 5 => 34394342400
  | 6 => 34635809
  | 7 => 1237978998810025069184548865
  | 8 => 34359771169
  | 9 => 39614081257132168831165300768
  | 10 => 33587200
  | 11 => 34359738401
  | 12 => 1218638065588202668065
  | 13 => 38686806820449969675173888
  | 14 => 1210107564192070999506944
  | 15 => 1152921539000172544
  | 16 => 32
  | 17 => 36028798127308800
  | 18 => 1125934266580992
  | 19 => 1074823201
  | 20 => 1074823200
  | 21 => 1100586418208
  | _ => 0

def R03p01_digit (i j : Fin 22) : ℕ := packedDigit 1 (R03p01_lowColumnCode j) i.val

private theorem R03p01_bound_00 : ∀ j : Fin 22,R03p01_digit 0 j<2 := by decide +kernel

private theorem R03p01_bound_01 : ∀ j : Fin 22,R03p01_digit 1 j<2 := by decide +kernel

private theorem R03p01_bound_02 : ∀ j : Fin 22,R03p01_digit 2 j<2 := by decide +kernel

private theorem R03p01_bound_03 : ∀ j : Fin 22,R03p01_digit 3 j<2 := by decide +kernel

private theorem R03p01_bound_04 : ∀ j : Fin 22,R03p01_digit 4 j<2 := by decide +kernel

private theorem R03p01_bound_05 : ∀ j : Fin 22,R03p01_digit 5 j<2 := by decide +kernel

private theorem R03p01_bound_06 : ∀ j : Fin 22,R03p01_digit 6 j<2 := by decide +kernel

private theorem R03p01_bound_07 : ∀ j : Fin 22,R03p01_digit 7 j<2 := by decide +kernel

private theorem R03p01_bound_08 : ∀ j : Fin 22,R03p01_digit 8 j<2 := by decide +kernel

private theorem R03p01_bound_09 : ∀ j : Fin 22,R03p01_digit 9 j<2 := by decide +kernel

private theorem R03p01_bound_10 : ∀ j : Fin 22,R03p01_digit 10 j<2 := by decide +kernel

private theorem R03p01_bound_11 : ∀ j : Fin 22,R03p01_digit 11 j<2 := by decide +kernel

private theorem R03p01_bound_12 : ∀ j : Fin 22,R03p01_digit 12 j<2 := by decide +kernel

private theorem R03p01_bound_13 : ∀ j : Fin 22,R03p01_digit 13 j<2 := by decide +kernel

private theorem R03p01_bound_14 : ∀ j : Fin 22,R03p01_digit 14 j<2 := by decide +kernel

private theorem R03p01_bound_15 : ∀ j : Fin 22,R03p01_digit 15 j<2 := by decide +kernel

private theorem R03p01_bound_16 : ∀ j : Fin 22,R03p01_digit 16 j<2 := by decide +kernel

private theorem R03p01_bound_17 : ∀ j : Fin 22,R03p01_digit 17 j<2 := by decide +kernel

private theorem R03p01_bound_18 : ∀ j : Fin 22,R03p01_digit 18 j<2 := by decide +kernel

private theorem R03p01_bound_19 : ∀ j : Fin 22,R03p01_digit 19 j<2 := by decide +kernel

private theorem R03p01_bound_20 : ∀ j : Fin 22,R03p01_digit 20 j<2 := by decide +kernel

private theorem R03p01_bound_21 : ∀ j : Fin 22,R03p01_digit 21 j<2 := by decide +kernel

theorem R03p01_bound : ∀ i j : Fin 22,R03p01_digit i j<2 := by
  intro i j
  fin_cases i
  · exact R03p01_bound_00 j
  · exact R03p01_bound_01 j
  · exact R03p01_bound_02 j
  · exact R03p01_bound_03 j
  · exact R03p01_bound_04 j
  · exact R03p01_bound_05 j
  · exact R03p01_bound_06 j
  · exact R03p01_bound_07 j
  · exact R03p01_bound_08 j
  · exact R03p01_bound_09 j
  · exact R03p01_bound_10 j
  · exact R03p01_bound_11 j
  · exact R03p01_bound_12 j
  · exact R03p01_bound_13 j
  · exact R03p01_bound_14 j
  · exact R03p01_bound_15 j
  · exact R03p01_bound_16 j
  · exact R03p01_bound_17 j
  · exact R03p01_bound_18 j
  · exact R03p01_bound_19 j
  · exact R03p01_bound_20 j
  · exact R03p01_bound_21 j

private theorem R03p01_row_00 : pack 32 (R03p01_digit 0)=R03p01_rowCode 0 := by decide +kernel

private theorem R03p01_row_01 : pack 32 (R03p01_digit 1)=R03p01_rowCode 1 := by decide +kernel

private theorem R03p01_row_02 : pack 32 (R03p01_digit 2)=R03p01_rowCode 2 := by decide +kernel

private theorem R03p01_row_03 : pack 32 (R03p01_digit 3)=R03p01_rowCode 3 := by decide +kernel

private theorem R03p01_row_04 : pack 32 (R03p01_digit 4)=R03p01_rowCode 4 := by decide +kernel

private theorem R03p01_row_05 : pack 32 (R03p01_digit 5)=R03p01_rowCode 5 := by decide +kernel

private theorem R03p01_row_06 : pack 32 (R03p01_digit 6)=R03p01_rowCode 6 := by decide +kernel

private theorem R03p01_row_07 : pack 32 (R03p01_digit 7)=R03p01_rowCode 7 := by decide +kernel

private theorem R03p01_row_08 : pack 32 (R03p01_digit 8)=R03p01_rowCode 8 := by decide +kernel

private theorem R03p01_row_09 : pack 32 (R03p01_digit 9)=R03p01_rowCode 9 := by decide +kernel

private theorem R03p01_row_10 : pack 32 (R03p01_digit 10)=R03p01_rowCode 10 := by decide +kernel

private theorem R03p01_row_11 : pack 32 (R03p01_digit 11)=R03p01_rowCode 11 := by decide +kernel

private theorem R03p01_row_12 : pack 32 (R03p01_digit 12)=R03p01_rowCode 12 := by decide +kernel

private theorem R03p01_row_13 : pack 32 (R03p01_digit 13)=R03p01_rowCode 13 := by decide +kernel

private theorem R03p01_row_14 : pack 32 (R03p01_digit 14)=R03p01_rowCode 14 := by decide +kernel

private theorem R03p01_row_15 : pack 32 (R03p01_digit 15)=R03p01_rowCode 15 := by decide +kernel

private theorem R03p01_row_16 : pack 32 (R03p01_digit 16)=R03p01_rowCode 16 := by decide +kernel

private theorem R03p01_row_17 : pack 32 (R03p01_digit 17)=R03p01_rowCode 17 := by decide +kernel

private theorem R03p01_row_18 : pack 32 (R03p01_digit 18)=R03p01_rowCode 18 := by decide +kernel

private theorem R03p01_row_19 : pack 32 (R03p01_digit 19)=R03p01_rowCode 19 := by decide +kernel

private theorem R03p01_row_20 : pack 32 (R03p01_digit 20)=R03p01_rowCode 20 := by decide +kernel

private theorem R03p01_row_21 : pack 32 (R03p01_digit 21)=R03p01_rowCode 21 := by decide +kernel

theorem R03p01_row_binding : ∀ i : Fin 22,pack 32 (R03p01_digit i)=R03p01_rowCode i := by
  intro i
  fin_cases i
  · exact R03p01_row_00
  · exact R03p01_row_01
  · exact R03p01_row_02
  · exact R03p01_row_03
  · exact R03p01_row_04
  · exact R03p01_row_05
  · exact R03p01_row_06
  · exact R03p01_row_07
  · exact R03p01_row_08
  · exact R03p01_row_09
  · exact R03p01_row_10
  · exact R03p01_row_11
  · exact R03p01_row_12
  · exact R03p01_row_13
  · exact R03p01_row_14
  · exact R03p01_row_15
  · exact R03p01_row_16
  · exact R03p01_row_17
  · exact R03p01_row_18
  · exact R03p01_row_19
  · exact R03p01_row_20
  · exact R03p01_row_21

private theorem R03p01_column_00 : reversePack 32 (fun j : Fin 22 => R03p01_digit j 0)=R03p01_columnCode 0 := by decide +kernel

private theorem R03p01_column_01 : reversePack 32 (fun j : Fin 22 => R03p01_digit j 1)=R03p01_columnCode 1 := by decide +kernel

private theorem R03p01_column_02 : reversePack 32 (fun j : Fin 22 => R03p01_digit j 2)=R03p01_columnCode 2 := by decide +kernel

private theorem R03p01_column_03 : reversePack 32 (fun j : Fin 22 => R03p01_digit j 3)=R03p01_columnCode 3 := by decide +kernel

private theorem R03p01_column_04 : reversePack 32 (fun j : Fin 22 => R03p01_digit j 4)=R03p01_columnCode 4 := by decide +kernel

private theorem R03p01_column_05 : reversePack 32 (fun j : Fin 22 => R03p01_digit j 5)=R03p01_columnCode 5 := by decide +kernel

private theorem R03p01_column_06 : reversePack 32 (fun j : Fin 22 => R03p01_digit j 6)=R03p01_columnCode 6 := by decide +kernel

private theorem R03p01_column_07 : reversePack 32 (fun j : Fin 22 => R03p01_digit j 7)=R03p01_columnCode 7 := by decide +kernel

private theorem R03p01_column_08 : reversePack 32 (fun j : Fin 22 => R03p01_digit j 8)=R03p01_columnCode 8 := by decide +kernel

private theorem R03p01_column_09 : reversePack 32 (fun j : Fin 22 => R03p01_digit j 9)=R03p01_columnCode 9 := by decide +kernel

private theorem R03p01_column_10 : reversePack 32 (fun j : Fin 22 => R03p01_digit j 10)=R03p01_columnCode 10 := by decide +kernel

private theorem R03p01_column_11 : reversePack 32 (fun j : Fin 22 => R03p01_digit j 11)=R03p01_columnCode 11 := by decide +kernel

private theorem R03p01_column_12 : reversePack 32 (fun j : Fin 22 => R03p01_digit j 12)=R03p01_columnCode 12 := by decide +kernel

private theorem R03p01_column_13 : reversePack 32 (fun j : Fin 22 => R03p01_digit j 13)=R03p01_columnCode 13 := by decide +kernel

private theorem R03p01_column_14 : reversePack 32 (fun j : Fin 22 => R03p01_digit j 14)=R03p01_columnCode 14 := by decide +kernel

private theorem R03p01_column_15 : reversePack 32 (fun j : Fin 22 => R03p01_digit j 15)=R03p01_columnCode 15 := by decide +kernel

private theorem R03p01_column_16 : reversePack 32 (fun j : Fin 22 => R03p01_digit j 16)=R03p01_columnCode 16 := by decide +kernel

private theorem R03p01_column_17 : reversePack 32 (fun j : Fin 22 => R03p01_digit j 17)=R03p01_columnCode 17 := by decide +kernel

private theorem R03p01_column_18 : reversePack 32 (fun j : Fin 22 => R03p01_digit j 18)=R03p01_columnCode 18 := by decide +kernel

private theorem R03p01_column_19 : reversePack 32 (fun j : Fin 22 => R03p01_digit j 19)=R03p01_columnCode 19 := by decide +kernel

private theorem R03p01_column_20 : reversePack 32 (fun j : Fin 22 => R03p01_digit j 20)=R03p01_columnCode 20 := by decide +kernel

private theorem R03p01_column_21 : reversePack 32 (fun j : Fin 22 => R03p01_digit j 21)=R03p01_columnCode 21 := by decide +kernel

theorem R03p01_column_binding : ∀ i : Fin 22,reversePack 32 (fun j : Fin 22 => R03p01_digit j i)=R03p01_columnCode i := by
  intro i
  fin_cases i
  · exact R03p01_column_00
  · exact R03p01_column_01
  · exact R03p01_column_02
  · exact R03p01_column_03
  · exact R03p01_column_04
  · exact R03p01_column_05
  · exact R03p01_column_06
  · exact R03p01_column_07
  · exact R03p01_column_08
  · exact R03p01_column_09
  · exact R03p01_column_10
  · exact R03p01_column_11
  · exact R03p01_column_12
  · exact R03p01_column_13
  · exact R03p01_column_14
  · exact R03p01_column_15
  · exact R03p01_column_16
  · exact R03p01_column_17
  · exact R03p01_column_18
  · exact R03p01_column_19
  · exact R03p01_column_20
  · exact R03p01_column_21

def R03p01_data : PackedData 22 2 32 where
  raw := R03p01_digit
  digit_lt := R03p01_bound
  rowCode := R03p01_rowCode
  columnCode := R03p01_columnCode
  row_binding := R03p01_row_binding
  column_binding := R03p01_column_binding

def R03e02_lowColumnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 3515168
  | 1 => 3525348
  | 2 => 2396428
  | 3 => 2345248
  | 4 => 3370921
  | 5 => 2348704
  | 6 => 1567744
  | 7 => 437224
  | 8 => 178848
  | 9 => 1081441
  | 10 => 1067008
  | 11 => 193184
  | 12 => 2503148
  | 13 => 443691
  | 14 => 776172
  | 15 => 252580
  | 16 => 1474560
  | 17 => 1295872
  | 18 => 3576480
  | 19 => 175616
  | 20 => 1052160
  | 21 => 1253008
  | _ => 0

def R03e02_rowCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 36893523331792240640
  | 1 => 36893488147419103232
  | 2 => 38960676405179179861024
  | 3 => 1218638030403798041600
  | 4 => 40564819207303340847894502572032
  | 5 => 1237979036891338716795142177
  | 6 => 1181744577440749977632
  | 7 => 40566057186303338663279506489376
  | 8 => 1218638030403798074369
  | 9 => 41873360553413774980201965420577
  | 10 => 41872122575632415195187507101696
  | 11 => 41872083926567635408179992494112
  | 12 => 40566057186303338663245145703424
  | 13 => 39614081258321120233343942657
  | 14 => 38724622681794653616898080
  | 15 => 40891954844917868772798268449
  | 16 => 40564857931889091999703774560289
  | 17 => 40605711162149411602987536646144
  | 18 => 1239149003151404591533261857
  | 19 => 1180591620717411303424
  | 20 => 41833747642122904073514223927329
  | 21 => 1237940040438301779540608033
  | _ => 0

def R03e02_columnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1208963866025381819613217
  | 1 => 39615329143629314540500451361
  | 2 => 40852021333311072404536066049
  | 3 => 1208962714228711968735233
  | 4 => 40566058357487121028998845431841
  | 5 => 1210107600220868051992577
  | 6 => 37155831905550368
  | 7 => 1239187962676015231166087168
  | 8 => 1210107565319036058206208
  | 9 => 40564820454008092325481912729632
  | 10 => 1125934266581024
  | 11 => 1210107564193170511101952
  | 12 => 40853269218654171806722719745
  | 13 => 41833708956533604761275152236544
  | 14 => 40853269219843121044303905792
  | 15 => 39615291364697486767711846400
  | 16 => 1074823200
  | 17 => 1188950337093894176
  | 18 => 1210107564192036639768609
  | 19 => 1190077302119071744
  | 20 => 1190076201532653600
  | 21 => 38686808009400236941246496
  | _ => 0

def R03e02_digit (i j : Fin 22) : ℕ := packedDigit 1 (R03e02_lowColumnCode j) i.val

private theorem R03e02_bound_00 : ∀ j : Fin 22,R03e02_digit 0 j<2 := by decide +kernel

private theorem R03e02_bound_01 : ∀ j : Fin 22,R03e02_digit 1 j<2 := by decide +kernel

private theorem R03e02_bound_02 : ∀ j : Fin 22,R03e02_digit 2 j<2 := by decide +kernel

private theorem R03e02_bound_03 : ∀ j : Fin 22,R03e02_digit 3 j<2 := by decide +kernel

private theorem R03e02_bound_04 : ∀ j : Fin 22,R03e02_digit 4 j<2 := by decide +kernel

private theorem R03e02_bound_05 : ∀ j : Fin 22,R03e02_digit 5 j<2 := by decide +kernel

private theorem R03e02_bound_06 : ∀ j : Fin 22,R03e02_digit 6 j<2 := by decide +kernel

private theorem R03e02_bound_07 : ∀ j : Fin 22,R03e02_digit 7 j<2 := by decide +kernel

private theorem R03e02_bound_08 : ∀ j : Fin 22,R03e02_digit 8 j<2 := by decide +kernel

private theorem R03e02_bound_09 : ∀ j : Fin 22,R03e02_digit 9 j<2 := by decide +kernel

private theorem R03e02_bound_10 : ∀ j : Fin 22,R03e02_digit 10 j<2 := by decide +kernel

private theorem R03e02_bound_11 : ∀ j : Fin 22,R03e02_digit 11 j<2 := by decide +kernel

private theorem R03e02_bound_12 : ∀ j : Fin 22,R03e02_digit 12 j<2 := by decide +kernel

private theorem R03e02_bound_13 : ∀ j : Fin 22,R03e02_digit 13 j<2 := by decide +kernel

private theorem R03e02_bound_14 : ∀ j : Fin 22,R03e02_digit 14 j<2 := by decide +kernel

private theorem R03e02_bound_15 : ∀ j : Fin 22,R03e02_digit 15 j<2 := by decide +kernel

private theorem R03e02_bound_16 : ∀ j : Fin 22,R03e02_digit 16 j<2 := by decide +kernel

private theorem R03e02_bound_17 : ∀ j : Fin 22,R03e02_digit 17 j<2 := by decide +kernel

private theorem R03e02_bound_18 : ∀ j : Fin 22,R03e02_digit 18 j<2 := by decide +kernel

private theorem R03e02_bound_19 : ∀ j : Fin 22,R03e02_digit 19 j<2 := by decide +kernel

private theorem R03e02_bound_20 : ∀ j : Fin 22,R03e02_digit 20 j<2 := by decide +kernel

private theorem R03e02_bound_21 : ∀ j : Fin 22,R03e02_digit 21 j<2 := by decide +kernel

theorem R03e02_bound : ∀ i j : Fin 22,R03e02_digit i j<2 := by
  intro i j
  fin_cases i
  · exact R03e02_bound_00 j
  · exact R03e02_bound_01 j
  · exact R03e02_bound_02 j
  · exact R03e02_bound_03 j
  · exact R03e02_bound_04 j
  · exact R03e02_bound_05 j
  · exact R03e02_bound_06 j
  · exact R03e02_bound_07 j
  · exact R03e02_bound_08 j
  · exact R03e02_bound_09 j
  · exact R03e02_bound_10 j
  · exact R03e02_bound_11 j
  · exact R03e02_bound_12 j
  · exact R03e02_bound_13 j
  · exact R03e02_bound_14 j
  · exact R03e02_bound_15 j
  · exact R03e02_bound_16 j
  · exact R03e02_bound_17 j
  · exact R03e02_bound_18 j
  · exact R03e02_bound_19 j
  · exact R03e02_bound_20 j
  · exact R03e02_bound_21 j

private theorem R03e02_row_00 : pack 32 (R03e02_digit 0)=R03e02_rowCode 0 := by decide +kernel

private theorem R03e02_row_01 : pack 32 (R03e02_digit 1)=R03e02_rowCode 1 := by decide +kernel

private theorem R03e02_row_02 : pack 32 (R03e02_digit 2)=R03e02_rowCode 2 := by decide +kernel

private theorem R03e02_row_03 : pack 32 (R03e02_digit 3)=R03e02_rowCode 3 := by decide +kernel

private theorem R03e02_row_04 : pack 32 (R03e02_digit 4)=R03e02_rowCode 4 := by decide +kernel

private theorem R03e02_row_05 : pack 32 (R03e02_digit 5)=R03e02_rowCode 5 := by decide +kernel

private theorem R03e02_row_06 : pack 32 (R03e02_digit 6)=R03e02_rowCode 6 := by decide +kernel

private theorem R03e02_row_07 : pack 32 (R03e02_digit 7)=R03e02_rowCode 7 := by decide +kernel

private theorem R03e02_row_08 : pack 32 (R03e02_digit 8)=R03e02_rowCode 8 := by decide +kernel

private theorem R03e02_row_09 : pack 32 (R03e02_digit 9)=R03e02_rowCode 9 := by decide +kernel

private theorem R03e02_row_10 : pack 32 (R03e02_digit 10)=R03e02_rowCode 10 := by decide +kernel

private theorem R03e02_row_11 : pack 32 (R03e02_digit 11)=R03e02_rowCode 11 := by decide +kernel

private theorem R03e02_row_12 : pack 32 (R03e02_digit 12)=R03e02_rowCode 12 := by decide +kernel

private theorem R03e02_row_13 : pack 32 (R03e02_digit 13)=R03e02_rowCode 13 := by decide +kernel

private theorem R03e02_row_14 : pack 32 (R03e02_digit 14)=R03e02_rowCode 14 := by decide +kernel

private theorem R03e02_row_15 : pack 32 (R03e02_digit 15)=R03e02_rowCode 15 := by decide +kernel

private theorem R03e02_row_16 : pack 32 (R03e02_digit 16)=R03e02_rowCode 16 := by decide +kernel

private theorem R03e02_row_17 : pack 32 (R03e02_digit 17)=R03e02_rowCode 17 := by decide +kernel

private theorem R03e02_row_18 : pack 32 (R03e02_digit 18)=R03e02_rowCode 18 := by decide +kernel

private theorem R03e02_row_19 : pack 32 (R03e02_digit 19)=R03e02_rowCode 19 := by decide +kernel

private theorem R03e02_row_20 : pack 32 (R03e02_digit 20)=R03e02_rowCode 20 := by decide +kernel

private theorem R03e02_row_21 : pack 32 (R03e02_digit 21)=R03e02_rowCode 21 := by decide +kernel

theorem R03e02_row_binding : ∀ i : Fin 22,pack 32 (R03e02_digit i)=R03e02_rowCode i := by
  intro i
  fin_cases i
  · exact R03e02_row_00
  · exact R03e02_row_01
  · exact R03e02_row_02
  · exact R03e02_row_03
  · exact R03e02_row_04
  · exact R03e02_row_05
  · exact R03e02_row_06
  · exact R03e02_row_07
  · exact R03e02_row_08
  · exact R03e02_row_09
  · exact R03e02_row_10
  · exact R03e02_row_11
  · exact R03e02_row_12
  · exact R03e02_row_13
  · exact R03e02_row_14
  · exact R03e02_row_15
  · exact R03e02_row_16
  · exact R03e02_row_17
  · exact R03e02_row_18
  · exact R03e02_row_19
  · exact R03e02_row_20
  · exact R03e02_row_21

private theorem R03e02_column_00 : reversePack 32 (fun j : Fin 22 => R03e02_digit j 0)=R03e02_columnCode 0 := by decide +kernel

private theorem R03e02_column_01 : reversePack 32 (fun j : Fin 22 => R03e02_digit j 1)=R03e02_columnCode 1 := by decide +kernel

private theorem R03e02_column_02 : reversePack 32 (fun j : Fin 22 => R03e02_digit j 2)=R03e02_columnCode 2 := by decide +kernel

private theorem R03e02_column_03 : reversePack 32 (fun j : Fin 22 => R03e02_digit j 3)=R03e02_columnCode 3 := by decide +kernel

private theorem R03e02_column_04 : reversePack 32 (fun j : Fin 22 => R03e02_digit j 4)=R03e02_columnCode 4 := by decide +kernel

private theorem R03e02_column_05 : reversePack 32 (fun j : Fin 22 => R03e02_digit j 5)=R03e02_columnCode 5 := by decide +kernel

private theorem R03e02_column_06 : reversePack 32 (fun j : Fin 22 => R03e02_digit j 6)=R03e02_columnCode 6 := by decide +kernel

private theorem R03e02_column_07 : reversePack 32 (fun j : Fin 22 => R03e02_digit j 7)=R03e02_columnCode 7 := by decide +kernel

private theorem R03e02_column_08 : reversePack 32 (fun j : Fin 22 => R03e02_digit j 8)=R03e02_columnCode 8 := by decide +kernel

private theorem R03e02_column_09 : reversePack 32 (fun j : Fin 22 => R03e02_digit j 9)=R03e02_columnCode 9 := by decide +kernel

private theorem R03e02_column_10 : reversePack 32 (fun j : Fin 22 => R03e02_digit j 10)=R03e02_columnCode 10 := by decide +kernel

private theorem R03e02_column_11 : reversePack 32 (fun j : Fin 22 => R03e02_digit j 11)=R03e02_columnCode 11 := by decide +kernel

private theorem R03e02_column_12 : reversePack 32 (fun j : Fin 22 => R03e02_digit j 12)=R03e02_columnCode 12 := by decide +kernel

private theorem R03e02_column_13 : reversePack 32 (fun j : Fin 22 => R03e02_digit j 13)=R03e02_columnCode 13 := by decide +kernel

private theorem R03e02_column_14 : reversePack 32 (fun j : Fin 22 => R03e02_digit j 14)=R03e02_columnCode 14 := by decide +kernel

private theorem R03e02_column_15 : reversePack 32 (fun j : Fin 22 => R03e02_digit j 15)=R03e02_columnCode 15 := by decide +kernel

private theorem R03e02_column_16 : reversePack 32 (fun j : Fin 22 => R03e02_digit j 16)=R03e02_columnCode 16 := by decide +kernel

private theorem R03e02_column_17 : reversePack 32 (fun j : Fin 22 => R03e02_digit j 17)=R03e02_columnCode 17 := by decide +kernel

private theorem R03e02_column_18 : reversePack 32 (fun j : Fin 22 => R03e02_digit j 18)=R03e02_columnCode 18 := by decide +kernel

private theorem R03e02_column_19 : reversePack 32 (fun j : Fin 22 => R03e02_digit j 19)=R03e02_columnCode 19 := by decide +kernel

private theorem R03e02_column_20 : reversePack 32 (fun j : Fin 22 => R03e02_digit j 20)=R03e02_columnCode 20 := by decide +kernel

private theorem R03e02_column_21 : reversePack 32 (fun j : Fin 22 => R03e02_digit j 21)=R03e02_columnCode 21 := by decide +kernel

theorem R03e02_column_binding : ∀ i : Fin 22,reversePack 32 (fun j : Fin 22 => R03e02_digit j i)=R03e02_columnCode i := by
  intro i
  fin_cases i
  · exact R03e02_column_00
  · exact R03e02_column_01
  · exact R03e02_column_02
  · exact R03e02_column_03
  · exact R03e02_column_04
  · exact R03e02_column_05
  · exact R03e02_column_06
  · exact R03e02_column_07
  · exact R03e02_column_08
  · exact R03e02_column_09
  · exact R03e02_column_10
  · exact R03e02_column_11
  · exact R03e02_column_12
  · exact R03e02_column_13
  · exact R03e02_column_14
  · exact R03e02_column_15
  · exact R03e02_column_16
  · exact R03e02_column_17
  · exact R03e02_column_18
  · exact R03e02_column_19
  · exact R03e02_column_20
  · exact R03e02_column_21

def R03e02_data : PackedData 22 2 32 where
  raw := R03e02_digit
  digit_lt := R03e02_bound
  rowCode := R03e02_rowCode
  columnCode := R03e02_columnCode
  row_binding := R03e02_row_binding
  column_binding := R03e02_column_binding

def R03e04_lowColumnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1569246
  | 1 => 3112445
  | 2 => 361972
  | 3 => 4049784
  | 4 => 3724158
  | 5 => 1954077
  | 6 => 4171875
  | 7 => 2218790
  | 8 => 518122
  | 9 => 1199396
  | 10 => 1649484
  | 11 => 967334
  | 12 => 2215219
  | 13 => 4185356
  | 14 => 1994497
  | 15 => 3728417
  | 16 => 3571716
  | 17 => 1936681
  | 18 => 3560017
  | 19 => 1368910
  | 20 => 1193153
  | 21 => 296812
  | _ => 0

def R03e04_rowCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1268927264854418855085480083488
  | 1 => 39614081258321120233343942657
  | 2 => 40604434497523223309383560594465
  | 3 => 40604471974223595299971737354273
  | 4 => 1237940040438301779540608033
  | 5 => 40564857930709689365606198969376
  | 6 => 41873321828827988925463370171425
  | 7 => 1267650600228265431393233798177
  | 8 => 40604471975405339877412487332897
  | 9 => 40605671229780387173514383228928
  | 10 => 41832508532155367847135279055904
  | 11 => 38686844866859622740295712
  | 12 => 1268888540304408269953415774241
  | 13 => 1307264720444886180968540405793
  | 14 => 40852060294023507513567117345
  | 15 => 40604473220929534601995226219521
  | 16 => 38685664275204820502086689
  | 17 => 1268889750410855570347583864865
  | 18 => 40605711124369326818491407303713
  | 19 => 38724622681794653616898080
  | 20 => 1308542555073112366238519033857
  | 21 => 1239186782083267548696051744
  | _ => 0

def R03e04_columnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1308541346147291626843308851232
  | 1 => 40605711162148259842566134989825
  | 2 => 39654014805632452179655688192
  | 3 => 1277872408312061582225998881
  | 4 => 1308542553893672541160132838433
  | 5 => 40605709914262879588467022529568
  | 6 => 41832471054236322853978069042209
  | 7 => 1307265890449228755694421803009
  | 8 => 1268889788190940319659374706688
  | 9 => 39615290219882426304652378144
  | 10 => 40852059113396948680310785056
  | 11 => 1307265891592925727180102599680
  | 12 => 41832509702120548175033783025665
  | 13 => 40852021333348227135856215073
  | 14 => 40564819207341424413377326777376
  | 15 => 40564820416229196492455641351201
  | 16 => 39614081257132168797846798369
  | 17 => 40566058356305376485644028642336
  | 18 => 40564857930709653335708594634785
  | 19 => 1308502659341625224312507105312
  | 20 => 40564819246262900396649979314208
  | 21 => 40853268039251465108126203904
  | _ => 0

def R03e04_digit (i j : Fin 22) : ℕ := packedDigit 1 (R03e04_lowColumnCode j) i.val

private theorem R03e04_bound_00 : ∀ j : Fin 22,R03e04_digit 0 j<2 := by decide +kernel

private theorem R03e04_bound_01 : ∀ j : Fin 22,R03e04_digit 1 j<2 := by decide +kernel

private theorem R03e04_bound_02 : ∀ j : Fin 22,R03e04_digit 2 j<2 := by decide +kernel

private theorem R03e04_bound_03 : ∀ j : Fin 22,R03e04_digit 3 j<2 := by decide +kernel

private theorem R03e04_bound_04 : ∀ j : Fin 22,R03e04_digit 4 j<2 := by decide +kernel

private theorem R03e04_bound_05 : ∀ j : Fin 22,R03e04_digit 5 j<2 := by decide +kernel

private theorem R03e04_bound_06 : ∀ j : Fin 22,R03e04_digit 6 j<2 := by decide +kernel

private theorem R03e04_bound_07 : ∀ j : Fin 22,R03e04_digit 7 j<2 := by decide +kernel

private theorem R03e04_bound_08 : ∀ j : Fin 22,R03e04_digit 8 j<2 := by decide +kernel

private theorem R03e04_bound_09 : ∀ j : Fin 22,R03e04_digit 9 j<2 := by decide +kernel

private theorem R03e04_bound_10 : ∀ j : Fin 22,R03e04_digit 10 j<2 := by decide +kernel

private theorem R03e04_bound_11 : ∀ j : Fin 22,R03e04_digit 11 j<2 := by decide +kernel

private theorem R03e04_bound_12 : ∀ j : Fin 22,R03e04_digit 12 j<2 := by decide +kernel

private theorem R03e04_bound_13 : ∀ j : Fin 22,R03e04_digit 13 j<2 := by decide +kernel

private theorem R03e04_bound_14 : ∀ j : Fin 22,R03e04_digit 14 j<2 := by decide +kernel

private theorem R03e04_bound_15 : ∀ j : Fin 22,R03e04_digit 15 j<2 := by decide +kernel

private theorem R03e04_bound_16 : ∀ j : Fin 22,R03e04_digit 16 j<2 := by decide +kernel

private theorem R03e04_bound_17 : ∀ j : Fin 22,R03e04_digit 17 j<2 := by decide +kernel

private theorem R03e04_bound_18 : ∀ j : Fin 22,R03e04_digit 18 j<2 := by decide +kernel

private theorem R03e04_bound_19 : ∀ j : Fin 22,R03e04_digit 19 j<2 := by decide +kernel

private theorem R03e04_bound_20 : ∀ j : Fin 22,R03e04_digit 20 j<2 := by decide +kernel

private theorem R03e04_bound_21 : ∀ j : Fin 22,R03e04_digit 21 j<2 := by decide +kernel

theorem R03e04_bound : ∀ i j : Fin 22,R03e04_digit i j<2 := by
  intro i j
  fin_cases i
  · exact R03e04_bound_00 j
  · exact R03e04_bound_01 j
  · exact R03e04_bound_02 j
  · exact R03e04_bound_03 j
  · exact R03e04_bound_04 j
  · exact R03e04_bound_05 j
  · exact R03e04_bound_06 j
  · exact R03e04_bound_07 j
  · exact R03e04_bound_08 j
  · exact R03e04_bound_09 j
  · exact R03e04_bound_10 j
  · exact R03e04_bound_11 j
  · exact R03e04_bound_12 j
  · exact R03e04_bound_13 j
  · exact R03e04_bound_14 j
  · exact R03e04_bound_15 j
  · exact R03e04_bound_16 j
  · exact R03e04_bound_17 j
  · exact R03e04_bound_18 j
  · exact R03e04_bound_19 j
  · exact R03e04_bound_20 j
  · exact R03e04_bound_21 j

private theorem R03e04_row_00 : pack 32 (R03e04_digit 0)=R03e04_rowCode 0 := by decide +kernel

private theorem R03e04_row_01 : pack 32 (R03e04_digit 1)=R03e04_rowCode 1 := by decide +kernel

private theorem R03e04_row_02 : pack 32 (R03e04_digit 2)=R03e04_rowCode 2 := by decide +kernel

private theorem R03e04_row_03 : pack 32 (R03e04_digit 3)=R03e04_rowCode 3 := by decide +kernel

private theorem R03e04_row_04 : pack 32 (R03e04_digit 4)=R03e04_rowCode 4 := by decide +kernel

private theorem R03e04_row_05 : pack 32 (R03e04_digit 5)=R03e04_rowCode 5 := by decide +kernel

private theorem R03e04_row_06 : pack 32 (R03e04_digit 6)=R03e04_rowCode 6 := by decide +kernel

private theorem R03e04_row_07 : pack 32 (R03e04_digit 7)=R03e04_rowCode 7 := by decide +kernel

private theorem R03e04_row_08 : pack 32 (R03e04_digit 8)=R03e04_rowCode 8 := by decide +kernel

private theorem R03e04_row_09 : pack 32 (R03e04_digit 9)=R03e04_rowCode 9 := by decide +kernel

private theorem R03e04_row_10 : pack 32 (R03e04_digit 10)=R03e04_rowCode 10 := by decide +kernel

private theorem R03e04_row_11 : pack 32 (R03e04_digit 11)=R03e04_rowCode 11 := by decide +kernel

private theorem R03e04_row_12 : pack 32 (R03e04_digit 12)=R03e04_rowCode 12 := by decide +kernel

private theorem R03e04_row_13 : pack 32 (R03e04_digit 13)=R03e04_rowCode 13 := by decide +kernel

private theorem R03e04_row_14 : pack 32 (R03e04_digit 14)=R03e04_rowCode 14 := by decide +kernel

private theorem R03e04_row_15 : pack 32 (R03e04_digit 15)=R03e04_rowCode 15 := by decide +kernel

private theorem R03e04_row_16 : pack 32 (R03e04_digit 16)=R03e04_rowCode 16 := by decide +kernel

private theorem R03e04_row_17 : pack 32 (R03e04_digit 17)=R03e04_rowCode 17 := by decide +kernel

private theorem R03e04_row_18 : pack 32 (R03e04_digit 18)=R03e04_rowCode 18 := by decide +kernel

private theorem R03e04_row_19 : pack 32 (R03e04_digit 19)=R03e04_rowCode 19 := by decide +kernel

private theorem R03e04_row_20 : pack 32 (R03e04_digit 20)=R03e04_rowCode 20 := by decide +kernel

private theorem R03e04_row_21 : pack 32 (R03e04_digit 21)=R03e04_rowCode 21 := by decide +kernel

theorem R03e04_row_binding : ∀ i : Fin 22,pack 32 (R03e04_digit i)=R03e04_rowCode i := by
  intro i
  fin_cases i
  · exact R03e04_row_00
  · exact R03e04_row_01
  · exact R03e04_row_02
  · exact R03e04_row_03
  · exact R03e04_row_04
  · exact R03e04_row_05
  · exact R03e04_row_06
  · exact R03e04_row_07
  · exact R03e04_row_08
  · exact R03e04_row_09
  · exact R03e04_row_10
  · exact R03e04_row_11
  · exact R03e04_row_12
  · exact R03e04_row_13
  · exact R03e04_row_14
  · exact R03e04_row_15
  · exact R03e04_row_16
  · exact R03e04_row_17
  · exact R03e04_row_18
  · exact R03e04_row_19
  · exact R03e04_row_20
  · exact R03e04_row_21

private theorem R03e04_column_00 : reversePack 32 (fun j : Fin 22 => R03e04_digit j 0)=R03e04_columnCode 0 := by decide +kernel

private theorem R03e04_column_01 : reversePack 32 (fun j : Fin 22 => R03e04_digit j 1)=R03e04_columnCode 1 := by decide +kernel

private theorem R03e04_column_02 : reversePack 32 (fun j : Fin 22 => R03e04_digit j 2)=R03e04_columnCode 2 := by decide +kernel

private theorem R03e04_column_03 : reversePack 32 (fun j : Fin 22 => R03e04_digit j 3)=R03e04_columnCode 3 := by decide +kernel

private theorem R03e04_column_04 : reversePack 32 (fun j : Fin 22 => R03e04_digit j 4)=R03e04_columnCode 4 := by decide +kernel

private theorem R03e04_column_05 : reversePack 32 (fun j : Fin 22 => R03e04_digit j 5)=R03e04_columnCode 5 := by decide +kernel

private theorem R03e04_column_06 : reversePack 32 (fun j : Fin 22 => R03e04_digit j 6)=R03e04_columnCode 6 := by decide +kernel

private theorem R03e04_column_07 : reversePack 32 (fun j : Fin 22 => R03e04_digit j 7)=R03e04_columnCode 7 := by decide +kernel

private theorem R03e04_column_08 : reversePack 32 (fun j : Fin 22 => R03e04_digit j 8)=R03e04_columnCode 8 := by decide +kernel

private theorem R03e04_column_09 : reversePack 32 (fun j : Fin 22 => R03e04_digit j 9)=R03e04_columnCode 9 := by decide +kernel

private theorem R03e04_column_10 : reversePack 32 (fun j : Fin 22 => R03e04_digit j 10)=R03e04_columnCode 10 := by decide +kernel

private theorem R03e04_column_11 : reversePack 32 (fun j : Fin 22 => R03e04_digit j 11)=R03e04_columnCode 11 := by decide +kernel

private theorem R03e04_column_12 : reversePack 32 (fun j : Fin 22 => R03e04_digit j 12)=R03e04_columnCode 12 := by decide +kernel

private theorem R03e04_column_13 : reversePack 32 (fun j : Fin 22 => R03e04_digit j 13)=R03e04_columnCode 13 := by decide +kernel

private theorem R03e04_column_14 : reversePack 32 (fun j : Fin 22 => R03e04_digit j 14)=R03e04_columnCode 14 := by decide +kernel

private theorem R03e04_column_15 : reversePack 32 (fun j : Fin 22 => R03e04_digit j 15)=R03e04_columnCode 15 := by decide +kernel

private theorem R03e04_column_16 : reversePack 32 (fun j : Fin 22 => R03e04_digit j 16)=R03e04_columnCode 16 := by decide +kernel

private theorem R03e04_column_17 : reversePack 32 (fun j : Fin 22 => R03e04_digit j 17)=R03e04_columnCode 17 := by decide +kernel

private theorem R03e04_column_18 : reversePack 32 (fun j : Fin 22 => R03e04_digit j 18)=R03e04_columnCode 18 := by decide +kernel

private theorem R03e04_column_19 : reversePack 32 (fun j : Fin 22 => R03e04_digit j 19)=R03e04_columnCode 19 := by decide +kernel

private theorem R03e04_column_20 : reversePack 32 (fun j : Fin 22 => R03e04_digit j 20)=R03e04_columnCode 20 := by decide +kernel

private theorem R03e04_column_21 : reversePack 32 (fun j : Fin 22 => R03e04_digit j 21)=R03e04_columnCode 21 := by decide +kernel

theorem R03e04_column_binding : ∀ i : Fin 22,reversePack 32 (fun j : Fin 22 => R03e04_digit j i)=R03e04_columnCode i := by
  intro i
  fin_cases i
  · exact R03e04_column_00
  · exact R03e04_column_01
  · exact R03e04_column_02
  · exact R03e04_column_03
  · exact R03e04_column_04
  · exact R03e04_column_05
  · exact R03e04_column_06
  · exact R03e04_column_07
  · exact R03e04_column_08
  · exact R03e04_column_09
  · exact R03e04_column_10
  · exact R03e04_column_11
  · exact R03e04_column_12
  · exact R03e04_column_13
  · exact R03e04_column_14
  · exact R03e04_column_15
  · exact R03e04_column_16
  · exact R03e04_column_17
  · exact R03e04_column_18
  · exact R03e04_column_19
  · exact R03e04_column_20
  · exact R03e04_column_21

def R03e04_data : PackedData 22 2 32 where
  raw := R03e04_digit
  digit_lt := R03e04_bound
  rowCode := R03e04_rowCode
  columnCode := R03e04_columnCode
  row_binding := R03e04_row_binding
  column_binding := R03e04_column_binding

end SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoCaches00
