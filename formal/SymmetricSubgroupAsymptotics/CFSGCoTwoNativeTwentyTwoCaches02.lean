import SymmetricSubgroupAsymptotics.MatrixKroneckerProductReflection
import Mathlib.Tactic.FinCases

/-! Fixed Co2 binary22 shared caches. Every digit and pack binding is kernel checked. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoCaches02
open MatrixKroneckerProductReflection MatrixKroneckerDotReflection
open MatrixNaturalRowDotReflection SmallNaturalMatrixProductReflection

def R04e02_lowColumnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 2918925
  | 1 => 648493
  | 2 => 2124336
  | 3 => 2124348
  | 4 => 2751955
  | 5 => 2751971
  | 6 => 2438540
  | 7 => 2729900
  | 8 => 2438348
  | 9 => 2452771
  | 10 => 820000
  | 11 => 18223
  | 12 => 2437132
  | 13 => 354872
  | 14 => 16384
  | 15 => 2222652
  | 16 => 2189876
  | 17 => 1141628
  | 18 => 2170892
  | 19 => 2714172
  | 20 => 224124
  | 21 => 2097152
  | _ => 0

def R04e02_rowCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 36063981425655841
  | 1 => 36063981425655808
  | 2 => 1308542553856815047724872269857
  | 3 => 1308541344967888921243116666913
  | 4 => 1307304613853234204160822379520
  | 5 => 1307304613853271394076512519200
  | 6 => 1267689285854457070729840033792
  | 7 => 1134979710976
  | 8 => 1267689285854494259547059781664
  | 9 => 1307304613853271358892106875905
  | 10 => 36065116370763808
  | 11 => 1307304613853234239345228022785
  | 12 => 1152922605226819584
  | 13 => 1308542553893672542259679101984
  | 14 => 1307304615033861888859658290208
  | 15 => 37778932988891462893601
  | 16 => 1308542553893672542259679068192
  | 17 => 1267650600228229401496703205376
  | 18 => 38047571836890251265
  | 19 => 39614081257133294731073159201
  | 20 => 38685626227668133590597632
  | 21 => 40605672475305662832376468767745
  | _ => 0

def R04e02_columnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 40605671228600912444371761136641
  | 1 => 40605672437562507529674765108224
  | 2 => 39894553201331301150359553
  | 3 => 40891915849618880372821458945
  | 4 => 41832508532154252080363065050113
  | 5 => 41832471055453844026858649158657
  | 6 => 40852022513938723017437773825
  | 7 => 40853231440911223967920948225
  | 8 => 40852060255977097827180380161
  | 9 => 41832471016494320507998630346753
  | 10 => 1208963866024282274432000
  | 11 => 41873323037791889851575456235520
  | 12 => 40852021296417585355588403201
  | 13 => 1277834592486711576083070976
  | 14 => 34359738368
  | 15 => 40891915849618880373928755201
  | 16 => 39653975810333500097955889153
  | 17 => 40891953665444231477435826208
  | 18 => 40852021296417550171216281601
  | 19 => 40891915849618880372855014401
  | 20 => 40891953665444231477436874752
  | 21 => 1
  | _ => 0

def R04e02_digit (i j : Fin 22) : ℕ := packedDigit 1 (R04e02_lowColumnCode j) i.val

private theorem R04e02_bound_00 : ∀ j : Fin 22,R04e02_digit 0 j<2 := by decide +kernel

private theorem R04e02_bound_01 : ∀ j : Fin 22,R04e02_digit 1 j<2 := by decide +kernel

private theorem R04e02_bound_02 : ∀ j : Fin 22,R04e02_digit 2 j<2 := by decide +kernel

private theorem R04e02_bound_03 : ∀ j : Fin 22,R04e02_digit 3 j<2 := by decide +kernel

private theorem R04e02_bound_04 : ∀ j : Fin 22,R04e02_digit 4 j<2 := by decide +kernel

private theorem R04e02_bound_05 : ∀ j : Fin 22,R04e02_digit 5 j<2 := by decide +kernel

private theorem R04e02_bound_06 : ∀ j : Fin 22,R04e02_digit 6 j<2 := by decide +kernel

private theorem R04e02_bound_07 : ∀ j : Fin 22,R04e02_digit 7 j<2 := by decide +kernel

private theorem R04e02_bound_08 : ∀ j : Fin 22,R04e02_digit 8 j<2 := by decide +kernel

private theorem R04e02_bound_09 : ∀ j : Fin 22,R04e02_digit 9 j<2 := by decide +kernel

private theorem R04e02_bound_10 : ∀ j : Fin 22,R04e02_digit 10 j<2 := by decide +kernel

private theorem R04e02_bound_11 : ∀ j : Fin 22,R04e02_digit 11 j<2 := by decide +kernel

private theorem R04e02_bound_12 : ∀ j : Fin 22,R04e02_digit 12 j<2 := by decide +kernel

private theorem R04e02_bound_13 : ∀ j : Fin 22,R04e02_digit 13 j<2 := by decide +kernel

private theorem R04e02_bound_14 : ∀ j : Fin 22,R04e02_digit 14 j<2 := by decide +kernel

private theorem R04e02_bound_15 : ∀ j : Fin 22,R04e02_digit 15 j<2 := by decide +kernel

private theorem R04e02_bound_16 : ∀ j : Fin 22,R04e02_digit 16 j<2 := by decide +kernel

private theorem R04e02_bound_17 : ∀ j : Fin 22,R04e02_digit 17 j<2 := by decide +kernel

private theorem R04e02_bound_18 : ∀ j : Fin 22,R04e02_digit 18 j<2 := by decide +kernel

private theorem R04e02_bound_19 : ∀ j : Fin 22,R04e02_digit 19 j<2 := by decide +kernel

private theorem R04e02_bound_20 : ∀ j : Fin 22,R04e02_digit 20 j<2 := by decide +kernel

private theorem R04e02_bound_21 : ∀ j : Fin 22,R04e02_digit 21 j<2 := by decide +kernel

theorem R04e02_bound : ∀ i j : Fin 22,R04e02_digit i j<2 := by
  intro i j
  fin_cases i
  · exact R04e02_bound_00 j
  · exact R04e02_bound_01 j
  · exact R04e02_bound_02 j
  · exact R04e02_bound_03 j
  · exact R04e02_bound_04 j
  · exact R04e02_bound_05 j
  · exact R04e02_bound_06 j
  · exact R04e02_bound_07 j
  · exact R04e02_bound_08 j
  · exact R04e02_bound_09 j
  · exact R04e02_bound_10 j
  · exact R04e02_bound_11 j
  · exact R04e02_bound_12 j
  · exact R04e02_bound_13 j
  · exact R04e02_bound_14 j
  · exact R04e02_bound_15 j
  · exact R04e02_bound_16 j
  · exact R04e02_bound_17 j
  · exact R04e02_bound_18 j
  · exact R04e02_bound_19 j
  · exact R04e02_bound_20 j
  · exact R04e02_bound_21 j

private theorem R04e02_row_00 : pack 32 (R04e02_digit 0)=R04e02_rowCode 0 := by decide +kernel

private theorem R04e02_row_01 : pack 32 (R04e02_digit 1)=R04e02_rowCode 1 := by decide +kernel

private theorem R04e02_row_02 : pack 32 (R04e02_digit 2)=R04e02_rowCode 2 := by decide +kernel

private theorem R04e02_row_03 : pack 32 (R04e02_digit 3)=R04e02_rowCode 3 := by decide +kernel

private theorem R04e02_row_04 : pack 32 (R04e02_digit 4)=R04e02_rowCode 4 := by decide +kernel

private theorem R04e02_row_05 : pack 32 (R04e02_digit 5)=R04e02_rowCode 5 := by decide +kernel

private theorem R04e02_row_06 : pack 32 (R04e02_digit 6)=R04e02_rowCode 6 := by decide +kernel

private theorem R04e02_row_07 : pack 32 (R04e02_digit 7)=R04e02_rowCode 7 := by decide +kernel

private theorem R04e02_row_08 : pack 32 (R04e02_digit 8)=R04e02_rowCode 8 := by decide +kernel

private theorem R04e02_row_09 : pack 32 (R04e02_digit 9)=R04e02_rowCode 9 := by decide +kernel

private theorem R04e02_row_10 : pack 32 (R04e02_digit 10)=R04e02_rowCode 10 := by decide +kernel

private theorem R04e02_row_11 : pack 32 (R04e02_digit 11)=R04e02_rowCode 11 := by decide +kernel

private theorem R04e02_row_12 : pack 32 (R04e02_digit 12)=R04e02_rowCode 12 := by decide +kernel

private theorem R04e02_row_13 : pack 32 (R04e02_digit 13)=R04e02_rowCode 13 := by decide +kernel

private theorem R04e02_row_14 : pack 32 (R04e02_digit 14)=R04e02_rowCode 14 := by decide +kernel

private theorem R04e02_row_15 : pack 32 (R04e02_digit 15)=R04e02_rowCode 15 := by decide +kernel

private theorem R04e02_row_16 : pack 32 (R04e02_digit 16)=R04e02_rowCode 16 := by decide +kernel

private theorem R04e02_row_17 : pack 32 (R04e02_digit 17)=R04e02_rowCode 17 := by decide +kernel

private theorem R04e02_row_18 : pack 32 (R04e02_digit 18)=R04e02_rowCode 18 := by decide +kernel

private theorem R04e02_row_19 : pack 32 (R04e02_digit 19)=R04e02_rowCode 19 := by decide +kernel

private theorem R04e02_row_20 : pack 32 (R04e02_digit 20)=R04e02_rowCode 20 := by decide +kernel

private theorem R04e02_row_21 : pack 32 (R04e02_digit 21)=R04e02_rowCode 21 := by decide +kernel

theorem R04e02_row_binding : ∀ i : Fin 22,pack 32 (R04e02_digit i)=R04e02_rowCode i := by
  intro i
  fin_cases i
  · exact R04e02_row_00
  · exact R04e02_row_01
  · exact R04e02_row_02
  · exact R04e02_row_03
  · exact R04e02_row_04
  · exact R04e02_row_05
  · exact R04e02_row_06
  · exact R04e02_row_07
  · exact R04e02_row_08
  · exact R04e02_row_09
  · exact R04e02_row_10
  · exact R04e02_row_11
  · exact R04e02_row_12
  · exact R04e02_row_13
  · exact R04e02_row_14
  · exact R04e02_row_15
  · exact R04e02_row_16
  · exact R04e02_row_17
  · exact R04e02_row_18
  · exact R04e02_row_19
  · exact R04e02_row_20
  · exact R04e02_row_21

private theorem R04e02_column_00 : reversePack 32 (fun j : Fin 22 => R04e02_digit j 0)=R04e02_columnCode 0 := by decide +kernel

private theorem R04e02_column_01 : reversePack 32 (fun j : Fin 22 => R04e02_digit j 1)=R04e02_columnCode 1 := by decide +kernel

private theorem R04e02_column_02 : reversePack 32 (fun j : Fin 22 => R04e02_digit j 2)=R04e02_columnCode 2 := by decide +kernel

private theorem R04e02_column_03 : reversePack 32 (fun j : Fin 22 => R04e02_digit j 3)=R04e02_columnCode 3 := by decide +kernel

private theorem R04e02_column_04 : reversePack 32 (fun j : Fin 22 => R04e02_digit j 4)=R04e02_columnCode 4 := by decide +kernel

private theorem R04e02_column_05 : reversePack 32 (fun j : Fin 22 => R04e02_digit j 5)=R04e02_columnCode 5 := by decide +kernel

private theorem R04e02_column_06 : reversePack 32 (fun j : Fin 22 => R04e02_digit j 6)=R04e02_columnCode 6 := by decide +kernel

private theorem R04e02_column_07 : reversePack 32 (fun j : Fin 22 => R04e02_digit j 7)=R04e02_columnCode 7 := by decide +kernel

private theorem R04e02_column_08 : reversePack 32 (fun j : Fin 22 => R04e02_digit j 8)=R04e02_columnCode 8 := by decide +kernel

private theorem R04e02_column_09 : reversePack 32 (fun j : Fin 22 => R04e02_digit j 9)=R04e02_columnCode 9 := by decide +kernel

private theorem R04e02_column_10 : reversePack 32 (fun j : Fin 22 => R04e02_digit j 10)=R04e02_columnCode 10 := by decide +kernel

private theorem R04e02_column_11 : reversePack 32 (fun j : Fin 22 => R04e02_digit j 11)=R04e02_columnCode 11 := by decide +kernel

private theorem R04e02_column_12 : reversePack 32 (fun j : Fin 22 => R04e02_digit j 12)=R04e02_columnCode 12 := by decide +kernel

private theorem R04e02_column_13 : reversePack 32 (fun j : Fin 22 => R04e02_digit j 13)=R04e02_columnCode 13 := by decide +kernel

private theorem R04e02_column_14 : reversePack 32 (fun j : Fin 22 => R04e02_digit j 14)=R04e02_columnCode 14 := by decide +kernel

private theorem R04e02_column_15 : reversePack 32 (fun j : Fin 22 => R04e02_digit j 15)=R04e02_columnCode 15 := by decide +kernel

private theorem R04e02_column_16 : reversePack 32 (fun j : Fin 22 => R04e02_digit j 16)=R04e02_columnCode 16 := by decide +kernel

private theorem R04e02_column_17 : reversePack 32 (fun j : Fin 22 => R04e02_digit j 17)=R04e02_columnCode 17 := by decide +kernel

private theorem R04e02_column_18 : reversePack 32 (fun j : Fin 22 => R04e02_digit j 18)=R04e02_columnCode 18 := by decide +kernel

private theorem R04e02_column_19 : reversePack 32 (fun j : Fin 22 => R04e02_digit j 19)=R04e02_columnCode 19 := by decide +kernel

private theorem R04e02_column_20 : reversePack 32 (fun j : Fin 22 => R04e02_digit j 20)=R04e02_columnCode 20 := by decide +kernel

private theorem R04e02_column_21 : reversePack 32 (fun j : Fin 22 => R04e02_digit j 21)=R04e02_columnCode 21 := by decide +kernel

theorem R04e02_column_binding : ∀ i : Fin 22,reversePack 32 (fun j : Fin 22 => R04e02_digit j i)=R04e02_columnCode i := by
  intro i
  fin_cases i
  · exact R04e02_column_00
  · exact R04e02_column_01
  · exact R04e02_column_02
  · exact R04e02_column_03
  · exact R04e02_column_04
  · exact R04e02_column_05
  · exact R04e02_column_06
  · exact R04e02_column_07
  · exact R04e02_column_08
  · exact R04e02_column_09
  · exact R04e02_column_10
  · exact R04e02_column_11
  · exact R04e02_column_12
  · exact R04e02_column_13
  · exact R04e02_column_14
  · exact R04e02_column_15
  · exact R04e02_column_16
  · exact R04e02_column_17
  · exact R04e02_column_18
  · exact R04e02_column_19
  · exact R04e02_column_20
  · exact R04e02_column_21

def R04e02_data : PackedData 22 2 32 where
  raw := R04e02_digit
  digit_lt := R04e02_bound
  rowCode := R04e02_rowCode
  columnCode := R04e02_columnCode
  row_binding := R04e02_row_binding
  column_binding := R04e02_column_binding

def R05p01_lowColumnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 3307720
  | 1 => 188929
  | 2 => 1237641
  | 3 => 2272768
  | 4 => 1335817
  | 5 => 2276352
  | 6 => 3474432
  | 7 => 3317771
  | 8 => 2385920
  | 9 => 2927616
  | 10 => 2499584
  | 11 => 2533376
  | 12 => 3320836
  | 13 => 2270208
  | 14 => 2271232
  | 15 => 1228672
  | 16 => 1220608
  | 17 => 2423952
  | 18 => 3152544
  | 19 => 2367488
  | 20 => 3416064
  | 21 => 1474560
  | _ => 0

def R05p01_rowCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 34360788000
  | 1 => 34359738368
  | 2 => 1152921504606846976
  | 3 => 34360787969
  | 4 => 38685626227668133590597632
  | 5 => 1237940039285380274899124224
  | 6 => 1
  | 7 => 1276663444444911365651432449
  | 8 => 37778931862957161709568
  | 9 => 1237977818217243232061916192
  | 10 => 38723443207101828164517888
  | 11 => 1276664626225518668605849601
  | 12 => 1276663444444911365684985857
  | 13 => 1307304615035015937398043345953
  | 14 => 38685626227669233103275041
  | 15 => 40564859140852994087999651218464
  | 16 => 1073741824
  | 17 => 40564820455226767510581595374625
  | 18 => 41872122574414967277303452663808
  | 19 => 35184372088832
  | 20 => 41833708994276760028792482694145
  | 21 => 1308541308369549840087678746625
  | _ => 0

def R05p01_columnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1237978998810026167623483425
  | 1 => 40564819207304493770534055575552
  | 2 => 40566057148524370771526366003232
  | 3 => 1190077302119071745
  | 4 => 40566057147343779150807879942176
  | 5 => 37190981884313601
  | 6 => 36028797052551201
  | 7 => 41833707747570855630766691319841
  | 8 => 1127033778241537
  | 9 => 37155797511209985
  | 10 => 36029896531673089
  | 11 => 1127000493293569
  | 12 => 39614081257169324594284199969
  | 13 => 36029897605382145
  | 14 => 1127000493260801
  | 15 => 1218675221351321567264
  | 16 => 1100586418208
  | 17 => 38686806856479867244937217
  | 18 => 1210107565317935471788065
  | 19 => 1099511660545
  | 20 => 1099511660577
  | 21 => 1074823200
  | _ => 0

def R05p01_digit (i j : Fin 22) : ℕ := packedDigit 1 (R05p01_lowColumnCode j) i.val

private theorem R05p01_bound_00 : ∀ j : Fin 22,R05p01_digit 0 j<2 := by decide +kernel

private theorem R05p01_bound_01 : ∀ j : Fin 22,R05p01_digit 1 j<2 := by decide +kernel

private theorem R05p01_bound_02 : ∀ j : Fin 22,R05p01_digit 2 j<2 := by decide +kernel

private theorem R05p01_bound_03 : ∀ j : Fin 22,R05p01_digit 3 j<2 := by decide +kernel

private theorem R05p01_bound_04 : ∀ j : Fin 22,R05p01_digit 4 j<2 := by decide +kernel

private theorem R05p01_bound_05 : ∀ j : Fin 22,R05p01_digit 5 j<2 := by decide +kernel

private theorem R05p01_bound_06 : ∀ j : Fin 22,R05p01_digit 6 j<2 := by decide +kernel

private theorem R05p01_bound_07 : ∀ j : Fin 22,R05p01_digit 7 j<2 := by decide +kernel

private theorem R05p01_bound_08 : ∀ j : Fin 22,R05p01_digit 8 j<2 := by decide +kernel

private theorem R05p01_bound_09 : ∀ j : Fin 22,R05p01_digit 9 j<2 := by decide +kernel

private theorem R05p01_bound_10 : ∀ j : Fin 22,R05p01_digit 10 j<2 := by decide +kernel

private theorem R05p01_bound_11 : ∀ j : Fin 22,R05p01_digit 11 j<2 := by decide +kernel

private theorem R05p01_bound_12 : ∀ j : Fin 22,R05p01_digit 12 j<2 := by decide +kernel

private theorem R05p01_bound_13 : ∀ j : Fin 22,R05p01_digit 13 j<2 := by decide +kernel

private theorem R05p01_bound_14 : ∀ j : Fin 22,R05p01_digit 14 j<2 := by decide +kernel

private theorem R05p01_bound_15 : ∀ j : Fin 22,R05p01_digit 15 j<2 := by decide +kernel

private theorem R05p01_bound_16 : ∀ j : Fin 22,R05p01_digit 16 j<2 := by decide +kernel

private theorem R05p01_bound_17 : ∀ j : Fin 22,R05p01_digit 17 j<2 := by decide +kernel

private theorem R05p01_bound_18 : ∀ j : Fin 22,R05p01_digit 18 j<2 := by decide +kernel

private theorem R05p01_bound_19 : ∀ j : Fin 22,R05p01_digit 19 j<2 := by decide +kernel

private theorem R05p01_bound_20 : ∀ j : Fin 22,R05p01_digit 20 j<2 := by decide +kernel

private theorem R05p01_bound_21 : ∀ j : Fin 22,R05p01_digit 21 j<2 := by decide +kernel

theorem R05p01_bound : ∀ i j : Fin 22,R05p01_digit i j<2 := by
  intro i j
  fin_cases i
  · exact R05p01_bound_00 j
  · exact R05p01_bound_01 j
  · exact R05p01_bound_02 j
  · exact R05p01_bound_03 j
  · exact R05p01_bound_04 j
  · exact R05p01_bound_05 j
  · exact R05p01_bound_06 j
  · exact R05p01_bound_07 j
  · exact R05p01_bound_08 j
  · exact R05p01_bound_09 j
  · exact R05p01_bound_10 j
  · exact R05p01_bound_11 j
  · exact R05p01_bound_12 j
  · exact R05p01_bound_13 j
  · exact R05p01_bound_14 j
  · exact R05p01_bound_15 j
  · exact R05p01_bound_16 j
  · exact R05p01_bound_17 j
  · exact R05p01_bound_18 j
  · exact R05p01_bound_19 j
  · exact R05p01_bound_20 j
  · exact R05p01_bound_21 j

private theorem R05p01_row_00 : pack 32 (R05p01_digit 0)=R05p01_rowCode 0 := by decide +kernel

private theorem R05p01_row_01 : pack 32 (R05p01_digit 1)=R05p01_rowCode 1 := by decide +kernel

private theorem R05p01_row_02 : pack 32 (R05p01_digit 2)=R05p01_rowCode 2 := by decide +kernel

private theorem R05p01_row_03 : pack 32 (R05p01_digit 3)=R05p01_rowCode 3 := by decide +kernel

private theorem R05p01_row_04 : pack 32 (R05p01_digit 4)=R05p01_rowCode 4 := by decide +kernel

private theorem R05p01_row_05 : pack 32 (R05p01_digit 5)=R05p01_rowCode 5 := by decide +kernel

private theorem R05p01_row_06 : pack 32 (R05p01_digit 6)=R05p01_rowCode 6 := by decide +kernel

private theorem R05p01_row_07 : pack 32 (R05p01_digit 7)=R05p01_rowCode 7 := by decide +kernel

private theorem R05p01_row_08 : pack 32 (R05p01_digit 8)=R05p01_rowCode 8 := by decide +kernel

private theorem R05p01_row_09 : pack 32 (R05p01_digit 9)=R05p01_rowCode 9 := by decide +kernel

private theorem R05p01_row_10 : pack 32 (R05p01_digit 10)=R05p01_rowCode 10 := by decide +kernel

private theorem R05p01_row_11 : pack 32 (R05p01_digit 11)=R05p01_rowCode 11 := by decide +kernel

private theorem R05p01_row_12 : pack 32 (R05p01_digit 12)=R05p01_rowCode 12 := by decide +kernel

private theorem R05p01_row_13 : pack 32 (R05p01_digit 13)=R05p01_rowCode 13 := by decide +kernel

private theorem R05p01_row_14 : pack 32 (R05p01_digit 14)=R05p01_rowCode 14 := by decide +kernel

private theorem R05p01_row_15 : pack 32 (R05p01_digit 15)=R05p01_rowCode 15 := by decide +kernel

private theorem R05p01_row_16 : pack 32 (R05p01_digit 16)=R05p01_rowCode 16 := by decide +kernel

private theorem R05p01_row_17 : pack 32 (R05p01_digit 17)=R05p01_rowCode 17 := by decide +kernel

private theorem R05p01_row_18 : pack 32 (R05p01_digit 18)=R05p01_rowCode 18 := by decide +kernel

private theorem R05p01_row_19 : pack 32 (R05p01_digit 19)=R05p01_rowCode 19 := by decide +kernel

private theorem R05p01_row_20 : pack 32 (R05p01_digit 20)=R05p01_rowCode 20 := by decide +kernel

private theorem R05p01_row_21 : pack 32 (R05p01_digit 21)=R05p01_rowCode 21 := by decide +kernel

theorem R05p01_row_binding : ∀ i : Fin 22,pack 32 (R05p01_digit i)=R05p01_rowCode i := by
  intro i
  fin_cases i
  · exact R05p01_row_00
  · exact R05p01_row_01
  · exact R05p01_row_02
  · exact R05p01_row_03
  · exact R05p01_row_04
  · exact R05p01_row_05
  · exact R05p01_row_06
  · exact R05p01_row_07
  · exact R05p01_row_08
  · exact R05p01_row_09
  · exact R05p01_row_10
  · exact R05p01_row_11
  · exact R05p01_row_12
  · exact R05p01_row_13
  · exact R05p01_row_14
  · exact R05p01_row_15
  · exact R05p01_row_16
  · exact R05p01_row_17
  · exact R05p01_row_18
  · exact R05p01_row_19
  · exact R05p01_row_20
  · exact R05p01_row_21

private theorem R05p01_column_00 : reversePack 32 (fun j : Fin 22 => R05p01_digit j 0)=R05p01_columnCode 0 := by decide +kernel

private theorem R05p01_column_01 : reversePack 32 (fun j : Fin 22 => R05p01_digit j 1)=R05p01_columnCode 1 := by decide +kernel

private theorem R05p01_column_02 : reversePack 32 (fun j : Fin 22 => R05p01_digit j 2)=R05p01_columnCode 2 := by decide +kernel

private theorem R05p01_column_03 : reversePack 32 (fun j : Fin 22 => R05p01_digit j 3)=R05p01_columnCode 3 := by decide +kernel

private theorem R05p01_column_04 : reversePack 32 (fun j : Fin 22 => R05p01_digit j 4)=R05p01_columnCode 4 := by decide +kernel

private theorem R05p01_column_05 : reversePack 32 (fun j : Fin 22 => R05p01_digit j 5)=R05p01_columnCode 5 := by decide +kernel

private theorem R05p01_column_06 : reversePack 32 (fun j : Fin 22 => R05p01_digit j 6)=R05p01_columnCode 6 := by decide +kernel

private theorem R05p01_column_07 : reversePack 32 (fun j : Fin 22 => R05p01_digit j 7)=R05p01_columnCode 7 := by decide +kernel

private theorem R05p01_column_08 : reversePack 32 (fun j : Fin 22 => R05p01_digit j 8)=R05p01_columnCode 8 := by decide +kernel

private theorem R05p01_column_09 : reversePack 32 (fun j : Fin 22 => R05p01_digit j 9)=R05p01_columnCode 9 := by decide +kernel

private theorem R05p01_column_10 : reversePack 32 (fun j : Fin 22 => R05p01_digit j 10)=R05p01_columnCode 10 := by decide +kernel

private theorem R05p01_column_11 : reversePack 32 (fun j : Fin 22 => R05p01_digit j 11)=R05p01_columnCode 11 := by decide +kernel

private theorem R05p01_column_12 : reversePack 32 (fun j : Fin 22 => R05p01_digit j 12)=R05p01_columnCode 12 := by decide +kernel

private theorem R05p01_column_13 : reversePack 32 (fun j : Fin 22 => R05p01_digit j 13)=R05p01_columnCode 13 := by decide +kernel

private theorem R05p01_column_14 : reversePack 32 (fun j : Fin 22 => R05p01_digit j 14)=R05p01_columnCode 14 := by decide +kernel

private theorem R05p01_column_15 : reversePack 32 (fun j : Fin 22 => R05p01_digit j 15)=R05p01_columnCode 15 := by decide +kernel

private theorem R05p01_column_16 : reversePack 32 (fun j : Fin 22 => R05p01_digit j 16)=R05p01_columnCode 16 := by decide +kernel

private theorem R05p01_column_17 : reversePack 32 (fun j : Fin 22 => R05p01_digit j 17)=R05p01_columnCode 17 := by decide +kernel

private theorem R05p01_column_18 : reversePack 32 (fun j : Fin 22 => R05p01_digit j 18)=R05p01_columnCode 18 := by decide +kernel

private theorem R05p01_column_19 : reversePack 32 (fun j : Fin 22 => R05p01_digit j 19)=R05p01_columnCode 19 := by decide +kernel

private theorem R05p01_column_20 : reversePack 32 (fun j : Fin 22 => R05p01_digit j 20)=R05p01_columnCode 20 := by decide +kernel

private theorem R05p01_column_21 : reversePack 32 (fun j : Fin 22 => R05p01_digit j 21)=R05p01_columnCode 21 := by decide +kernel

theorem R05p01_column_binding : ∀ i : Fin 22,reversePack 32 (fun j : Fin 22 => R05p01_digit j i)=R05p01_columnCode i := by
  intro i
  fin_cases i
  · exact R05p01_column_00
  · exact R05p01_column_01
  · exact R05p01_column_02
  · exact R05p01_column_03
  · exact R05p01_column_04
  · exact R05p01_column_05
  · exact R05p01_column_06
  · exact R05p01_column_07
  · exact R05p01_column_08
  · exact R05p01_column_09
  · exact R05p01_column_10
  · exact R05p01_column_11
  · exact R05p01_column_12
  · exact R05p01_column_13
  · exact R05p01_column_14
  · exact R05p01_column_15
  · exact R05p01_column_16
  · exact R05p01_column_17
  · exact R05p01_column_18
  · exact R05p01_column_19
  · exact R05p01_column_20
  · exact R05p01_column_21

def R05p01_data : PackedData 22 2 32 where
  raw := R05p01_digit
  digit_lt := R05p01_bound
  rowCode := R05p01_rowCode
  columnCode := R05p01_columnCode
  row_binding := R05p01_row_binding
  column_binding := R05p01_column_binding

def R05p02_lowColumnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1730049
  | 1 => 2817224
  | 2 => 1478144
  | 3 => 2540169
  | 4 => 2485823
  | 5 => 2779151
  | 6 => 297014
  | 7 => 3317771
  | 8 => 2931727
  | 9 => 2927616
  | 10 => 2499584
  | 11 => 2533376
  | 12 => 3320836
  | 13 => 6816
  | 14 => 2271232
  | 15 => 3196464
  | 16 => 3153568
  | 17 => 2423952
  | 18 => 3152544
  | 19 => 416176
  | 20 => 3416064
  | 21 => 1474560
  | _ => 0

def R05p02_rowCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1133906001921
  | 1 => 1134979710976
  | 2 => 1152922605226819584
  | 3 => 1133906001952
  | 4 => 39652804662291699888599072768
  | 5 => 40853268038062514806501408768
  | 6 => 32
  | 7 => 40891915885358319981855539232
  | 8 => 39614081257132168796771975168
  | 9 => 1239186780930346008655725569
  | 10 => 39932332133229408325469217
  | 11 => 40891917067138927285884683296
  | 12 => 40891915885358321081367134240
  | 13 => 1267689287036238802867515818017
  | 14 => 39652804662291699887558918177
  | 15 => 40564857931890280986323610272800
  | 16 => 1048576
  | 17 => 40604433289742254713644611830817
  | 18 => 41872122574414967277303452697600
  | 19 => 36283917271073
  | 20 => 41833708994276760028791407903745
  | 21 => 1268928473780275660728751390752
  | _ => 0

def R05p02_columnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 40564819207304529799330000798752
  | 1 => 1237978998846054965716190209
  | 2 => 1190076202607476768
  | 3 => 40566057148524370770426854408193
  | 4 => 41873361723381225158562153529345
  | 5 => 41873321828827988925496656135169
  | 6 => 1307304576037409978957221101568
  | 7 => 41833707747570855630766691319841
  | 8 => 41873321828828024989444760175617
  | 9 => 37155797511209985
  | 10 => 36029896531673089
  | 11 => 1127000493293569
  | 12 => 39614081257169324594284199969
  | 13 => 1210107565317935471788032
  | 14 => 1127000493260801
  | 15 => 39894553236233099824594977
  | 16 => 1210107601346732490752033
  | 17 => 38686806856479867244937217
  | 18 => 1210107565317935471788065
  | 19 => 39895769533552746235461632
  | 20 => 1099511660577
  | 21 => 1074823200
  | _ => 0

def R05p02_digit (i j : Fin 22) : ℕ := packedDigit 1 (R05p02_lowColumnCode j) i.val

private theorem R05p02_bound_00 : ∀ j : Fin 22,R05p02_digit 0 j<2 := by decide +kernel

private theorem R05p02_bound_01 : ∀ j : Fin 22,R05p02_digit 1 j<2 := by decide +kernel

private theorem R05p02_bound_02 : ∀ j : Fin 22,R05p02_digit 2 j<2 := by decide +kernel

private theorem R05p02_bound_03 : ∀ j : Fin 22,R05p02_digit 3 j<2 := by decide +kernel

private theorem R05p02_bound_04 : ∀ j : Fin 22,R05p02_digit 4 j<2 := by decide +kernel

private theorem R05p02_bound_05 : ∀ j : Fin 22,R05p02_digit 5 j<2 := by decide +kernel

private theorem R05p02_bound_06 : ∀ j : Fin 22,R05p02_digit 6 j<2 := by decide +kernel

private theorem R05p02_bound_07 : ∀ j : Fin 22,R05p02_digit 7 j<2 := by decide +kernel

private theorem R05p02_bound_08 : ∀ j : Fin 22,R05p02_digit 8 j<2 := by decide +kernel

private theorem R05p02_bound_09 : ∀ j : Fin 22,R05p02_digit 9 j<2 := by decide +kernel

private theorem R05p02_bound_10 : ∀ j : Fin 22,R05p02_digit 10 j<2 := by decide +kernel

private theorem R05p02_bound_11 : ∀ j : Fin 22,R05p02_digit 11 j<2 := by decide +kernel

private theorem R05p02_bound_12 : ∀ j : Fin 22,R05p02_digit 12 j<2 := by decide +kernel

private theorem R05p02_bound_13 : ∀ j : Fin 22,R05p02_digit 13 j<2 := by decide +kernel

private theorem R05p02_bound_14 : ∀ j : Fin 22,R05p02_digit 14 j<2 := by decide +kernel

private theorem R05p02_bound_15 : ∀ j : Fin 22,R05p02_digit 15 j<2 := by decide +kernel

private theorem R05p02_bound_16 : ∀ j : Fin 22,R05p02_digit 16 j<2 := by decide +kernel

private theorem R05p02_bound_17 : ∀ j : Fin 22,R05p02_digit 17 j<2 := by decide +kernel

private theorem R05p02_bound_18 : ∀ j : Fin 22,R05p02_digit 18 j<2 := by decide +kernel

private theorem R05p02_bound_19 : ∀ j : Fin 22,R05p02_digit 19 j<2 := by decide +kernel

private theorem R05p02_bound_20 : ∀ j : Fin 22,R05p02_digit 20 j<2 := by decide +kernel

private theorem R05p02_bound_21 : ∀ j : Fin 22,R05p02_digit 21 j<2 := by decide +kernel

theorem R05p02_bound : ∀ i j : Fin 22,R05p02_digit i j<2 := by
  intro i j
  fin_cases i
  · exact R05p02_bound_00 j
  · exact R05p02_bound_01 j
  · exact R05p02_bound_02 j
  · exact R05p02_bound_03 j
  · exact R05p02_bound_04 j
  · exact R05p02_bound_05 j
  · exact R05p02_bound_06 j
  · exact R05p02_bound_07 j
  · exact R05p02_bound_08 j
  · exact R05p02_bound_09 j
  · exact R05p02_bound_10 j
  · exact R05p02_bound_11 j
  · exact R05p02_bound_12 j
  · exact R05p02_bound_13 j
  · exact R05p02_bound_14 j
  · exact R05p02_bound_15 j
  · exact R05p02_bound_16 j
  · exact R05p02_bound_17 j
  · exact R05p02_bound_18 j
  · exact R05p02_bound_19 j
  · exact R05p02_bound_20 j
  · exact R05p02_bound_21 j

private theorem R05p02_row_00 : pack 32 (R05p02_digit 0)=R05p02_rowCode 0 := by decide +kernel

private theorem R05p02_row_01 : pack 32 (R05p02_digit 1)=R05p02_rowCode 1 := by decide +kernel

private theorem R05p02_row_02 : pack 32 (R05p02_digit 2)=R05p02_rowCode 2 := by decide +kernel

private theorem R05p02_row_03 : pack 32 (R05p02_digit 3)=R05p02_rowCode 3 := by decide +kernel

private theorem R05p02_row_04 : pack 32 (R05p02_digit 4)=R05p02_rowCode 4 := by decide +kernel

private theorem R05p02_row_05 : pack 32 (R05p02_digit 5)=R05p02_rowCode 5 := by decide +kernel

private theorem R05p02_row_06 : pack 32 (R05p02_digit 6)=R05p02_rowCode 6 := by decide +kernel

private theorem R05p02_row_07 : pack 32 (R05p02_digit 7)=R05p02_rowCode 7 := by decide +kernel

private theorem R05p02_row_08 : pack 32 (R05p02_digit 8)=R05p02_rowCode 8 := by decide +kernel

private theorem R05p02_row_09 : pack 32 (R05p02_digit 9)=R05p02_rowCode 9 := by decide +kernel

private theorem R05p02_row_10 : pack 32 (R05p02_digit 10)=R05p02_rowCode 10 := by decide +kernel

private theorem R05p02_row_11 : pack 32 (R05p02_digit 11)=R05p02_rowCode 11 := by decide +kernel

private theorem R05p02_row_12 : pack 32 (R05p02_digit 12)=R05p02_rowCode 12 := by decide +kernel

private theorem R05p02_row_13 : pack 32 (R05p02_digit 13)=R05p02_rowCode 13 := by decide +kernel

private theorem R05p02_row_14 : pack 32 (R05p02_digit 14)=R05p02_rowCode 14 := by decide +kernel

private theorem R05p02_row_15 : pack 32 (R05p02_digit 15)=R05p02_rowCode 15 := by decide +kernel

private theorem R05p02_row_16 : pack 32 (R05p02_digit 16)=R05p02_rowCode 16 := by decide +kernel

private theorem R05p02_row_17 : pack 32 (R05p02_digit 17)=R05p02_rowCode 17 := by decide +kernel

private theorem R05p02_row_18 : pack 32 (R05p02_digit 18)=R05p02_rowCode 18 := by decide +kernel

private theorem R05p02_row_19 : pack 32 (R05p02_digit 19)=R05p02_rowCode 19 := by decide +kernel

private theorem R05p02_row_20 : pack 32 (R05p02_digit 20)=R05p02_rowCode 20 := by decide +kernel

private theorem R05p02_row_21 : pack 32 (R05p02_digit 21)=R05p02_rowCode 21 := by decide +kernel

theorem R05p02_row_binding : ∀ i : Fin 22,pack 32 (R05p02_digit i)=R05p02_rowCode i := by
  intro i
  fin_cases i
  · exact R05p02_row_00
  · exact R05p02_row_01
  · exact R05p02_row_02
  · exact R05p02_row_03
  · exact R05p02_row_04
  · exact R05p02_row_05
  · exact R05p02_row_06
  · exact R05p02_row_07
  · exact R05p02_row_08
  · exact R05p02_row_09
  · exact R05p02_row_10
  · exact R05p02_row_11
  · exact R05p02_row_12
  · exact R05p02_row_13
  · exact R05p02_row_14
  · exact R05p02_row_15
  · exact R05p02_row_16
  · exact R05p02_row_17
  · exact R05p02_row_18
  · exact R05p02_row_19
  · exact R05p02_row_20
  · exact R05p02_row_21

private theorem R05p02_column_00 : reversePack 32 (fun j : Fin 22 => R05p02_digit j 0)=R05p02_columnCode 0 := by decide +kernel

private theorem R05p02_column_01 : reversePack 32 (fun j : Fin 22 => R05p02_digit j 1)=R05p02_columnCode 1 := by decide +kernel

private theorem R05p02_column_02 : reversePack 32 (fun j : Fin 22 => R05p02_digit j 2)=R05p02_columnCode 2 := by decide +kernel

private theorem R05p02_column_03 : reversePack 32 (fun j : Fin 22 => R05p02_digit j 3)=R05p02_columnCode 3 := by decide +kernel

private theorem R05p02_column_04 : reversePack 32 (fun j : Fin 22 => R05p02_digit j 4)=R05p02_columnCode 4 := by decide +kernel

private theorem R05p02_column_05 : reversePack 32 (fun j : Fin 22 => R05p02_digit j 5)=R05p02_columnCode 5 := by decide +kernel

private theorem R05p02_column_06 : reversePack 32 (fun j : Fin 22 => R05p02_digit j 6)=R05p02_columnCode 6 := by decide +kernel

private theorem R05p02_column_07 : reversePack 32 (fun j : Fin 22 => R05p02_digit j 7)=R05p02_columnCode 7 := by decide +kernel

private theorem R05p02_column_08 : reversePack 32 (fun j : Fin 22 => R05p02_digit j 8)=R05p02_columnCode 8 := by decide +kernel

private theorem R05p02_column_09 : reversePack 32 (fun j : Fin 22 => R05p02_digit j 9)=R05p02_columnCode 9 := by decide +kernel

private theorem R05p02_column_10 : reversePack 32 (fun j : Fin 22 => R05p02_digit j 10)=R05p02_columnCode 10 := by decide +kernel

private theorem R05p02_column_11 : reversePack 32 (fun j : Fin 22 => R05p02_digit j 11)=R05p02_columnCode 11 := by decide +kernel

private theorem R05p02_column_12 : reversePack 32 (fun j : Fin 22 => R05p02_digit j 12)=R05p02_columnCode 12 := by decide +kernel

private theorem R05p02_column_13 : reversePack 32 (fun j : Fin 22 => R05p02_digit j 13)=R05p02_columnCode 13 := by decide +kernel

private theorem R05p02_column_14 : reversePack 32 (fun j : Fin 22 => R05p02_digit j 14)=R05p02_columnCode 14 := by decide +kernel

private theorem R05p02_column_15 : reversePack 32 (fun j : Fin 22 => R05p02_digit j 15)=R05p02_columnCode 15 := by decide +kernel

private theorem R05p02_column_16 : reversePack 32 (fun j : Fin 22 => R05p02_digit j 16)=R05p02_columnCode 16 := by decide +kernel

private theorem R05p02_column_17 : reversePack 32 (fun j : Fin 22 => R05p02_digit j 17)=R05p02_columnCode 17 := by decide +kernel

private theorem R05p02_column_18 : reversePack 32 (fun j : Fin 22 => R05p02_digit j 18)=R05p02_columnCode 18 := by decide +kernel

private theorem R05p02_column_19 : reversePack 32 (fun j : Fin 22 => R05p02_digit j 19)=R05p02_columnCode 19 := by decide +kernel

private theorem R05p02_column_20 : reversePack 32 (fun j : Fin 22 => R05p02_digit j 20)=R05p02_columnCode 20 := by decide +kernel

private theorem R05p02_column_21 : reversePack 32 (fun j : Fin 22 => R05p02_digit j 21)=R05p02_columnCode 21 := by decide +kernel

theorem R05p02_column_binding : ∀ i : Fin 22,reversePack 32 (fun j : Fin 22 => R05p02_digit j i)=R05p02_columnCode i := by
  intro i
  fin_cases i
  · exact R05p02_column_00
  · exact R05p02_column_01
  · exact R05p02_column_02
  · exact R05p02_column_03
  · exact R05p02_column_04
  · exact R05p02_column_05
  · exact R05p02_column_06
  · exact R05p02_column_07
  · exact R05p02_column_08
  · exact R05p02_column_09
  · exact R05p02_column_10
  · exact R05p02_column_11
  · exact R05p02_column_12
  · exact R05p02_column_13
  · exact R05p02_column_14
  · exact R05p02_column_15
  · exact R05p02_column_16
  · exact R05p02_column_17
  · exact R05p02_column_18
  · exact R05p02_column_19
  · exact R05p02_column_20
  · exact R05p02_column_21

def R05p02_data : PackedData 22 2 32 where
  raw := R05p02_digit
  digit_lt := R05p02_bound
  rowCode := R05p02_rowCode
  columnCode := R05p02_columnCode
  row_binding := R05p02_row_binding
  column_binding := R05p02_column_binding

def R05p03_lowColumnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 3389316
  | 1 => 548040
  | 2 => 2878279
  | 3 => 3325604
  | 4 => 3658998
  | 5 => 3200144
  | 6 => 2418224
  | 7 => 1546639
  | 8 => 3150496
  | 9 => 2543657
  | 10 => 2276000
  | 11 => 2048
  | 12 => 2783919
  | 13 => 2503318
  | 14 => 2813375
  | 15 => 2932384
  | 16 => 3416064
  | 17 => 182032
  | 18 => 262144
  | 19 => 2423216
  | 20 => 3307952
  | 21 => 2148112
  | _ => 0

def R05p03_rowCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1181744577440749978624
  | 1 => 1218638030403798041600
  | 2 => 1218638030403798074369
  | 3 => 1181744577440749977632
  | 4 => 41872122575632415195187507101696
  | 5 => 1307264720446039137657520422912
  | 6 => 1049632
  | 7 => 1307264720482932590653886988321
  | 8 => 41872122575595521707073339393025
  | 9 => 40564857930746547915637773075457
  | 10 => 40564857931889091999703774560289
  | 11 => 1307264720446075130203940619296
  | 12 => 1307264719302341005120847773729
  | 13 => 1307265929408752204150229468161
  | 14 => 41872122575596674663729066935328
  | 15 => 40604472013146225329619185206273
  | 16 => 34360787969
  | 17 => 1267689287073096261118370808833
  | 18 => 40853268038062550025233235968
  | 19 => 38960676405179179861024
  | 20 => 1267651809154049017259783913473
  | 21 => 41872085136712093088328650359809
  | _ => 0

def R05p03_columnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 39614082475806264248220254241
  | 1 => 1237978998846053865129772032
  | 2 => 41872083926605681817832051966977
  | 3 => 39615291364733516629849145377
  | 4 => 1307304614996968400747672666145
  | 5 => 38686806855352867826434081
  | 6 => 39894553236234199336255489
  | 7 => 41873321830045474068413094592544
  | 8 => 1210107564192035564945441
  | 9 => 40566058356268445878018383052801
  | 10 => 1210107565319036058206209
  | 11 => 1125899906842624
  | 12 => 41873323038935553117532221080577
  | 13 => 1307303368293333816932968726529
  | 14 => 41873361724597557345922344551425
  | 15 => 1210107601347833076155393
  | 16 => 1099511660577
  | 17 => 38685664310106618070040576
  | 18 => 32768
  | 19 => 39895769533553846819782657
  | 20 => 39895769533553845747056673
  | 21 => 38685664310106618068992001
  | _ => 0

def R05p03_digit (i j : Fin 22) : ℕ := packedDigit 1 (R05p03_lowColumnCode j) i.val

private theorem R05p03_bound_00 : ∀ j : Fin 22,R05p03_digit 0 j<2 := by decide +kernel

private theorem R05p03_bound_01 : ∀ j : Fin 22,R05p03_digit 1 j<2 := by decide +kernel

private theorem R05p03_bound_02 : ∀ j : Fin 22,R05p03_digit 2 j<2 := by decide +kernel

private theorem R05p03_bound_03 : ∀ j : Fin 22,R05p03_digit 3 j<2 := by decide +kernel

private theorem R05p03_bound_04 : ∀ j : Fin 22,R05p03_digit 4 j<2 := by decide +kernel

private theorem R05p03_bound_05 : ∀ j : Fin 22,R05p03_digit 5 j<2 := by decide +kernel

private theorem R05p03_bound_06 : ∀ j : Fin 22,R05p03_digit 6 j<2 := by decide +kernel

private theorem R05p03_bound_07 : ∀ j : Fin 22,R05p03_digit 7 j<2 := by decide +kernel

private theorem R05p03_bound_08 : ∀ j : Fin 22,R05p03_digit 8 j<2 := by decide +kernel

private theorem R05p03_bound_09 : ∀ j : Fin 22,R05p03_digit 9 j<2 := by decide +kernel

private theorem R05p03_bound_10 : ∀ j : Fin 22,R05p03_digit 10 j<2 := by decide +kernel

private theorem R05p03_bound_11 : ∀ j : Fin 22,R05p03_digit 11 j<2 := by decide +kernel

private theorem R05p03_bound_12 : ∀ j : Fin 22,R05p03_digit 12 j<2 := by decide +kernel

private theorem R05p03_bound_13 : ∀ j : Fin 22,R05p03_digit 13 j<2 := by decide +kernel

private theorem R05p03_bound_14 : ∀ j : Fin 22,R05p03_digit 14 j<2 := by decide +kernel

private theorem R05p03_bound_15 : ∀ j : Fin 22,R05p03_digit 15 j<2 := by decide +kernel

private theorem R05p03_bound_16 : ∀ j : Fin 22,R05p03_digit 16 j<2 := by decide +kernel

private theorem R05p03_bound_17 : ∀ j : Fin 22,R05p03_digit 17 j<2 := by decide +kernel

private theorem R05p03_bound_18 : ∀ j : Fin 22,R05p03_digit 18 j<2 := by decide +kernel

private theorem R05p03_bound_19 : ∀ j : Fin 22,R05p03_digit 19 j<2 := by decide +kernel

private theorem R05p03_bound_20 : ∀ j : Fin 22,R05p03_digit 20 j<2 := by decide +kernel

private theorem R05p03_bound_21 : ∀ j : Fin 22,R05p03_digit 21 j<2 := by decide +kernel

theorem R05p03_bound : ∀ i j : Fin 22,R05p03_digit i j<2 := by
  intro i j
  fin_cases i
  · exact R05p03_bound_00 j
  · exact R05p03_bound_01 j
  · exact R05p03_bound_02 j
  · exact R05p03_bound_03 j
  · exact R05p03_bound_04 j
  · exact R05p03_bound_05 j
  · exact R05p03_bound_06 j
  · exact R05p03_bound_07 j
  · exact R05p03_bound_08 j
  · exact R05p03_bound_09 j
  · exact R05p03_bound_10 j
  · exact R05p03_bound_11 j
  · exact R05p03_bound_12 j
  · exact R05p03_bound_13 j
  · exact R05p03_bound_14 j
  · exact R05p03_bound_15 j
  · exact R05p03_bound_16 j
  · exact R05p03_bound_17 j
  · exact R05p03_bound_18 j
  · exact R05p03_bound_19 j
  · exact R05p03_bound_20 j
  · exact R05p03_bound_21 j

private theorem R05p03_row_00 : pack 32 (R05p03_digit 0)=R05p03_rowCode 0 := by decide +kernel

private theorem R05p03_row_01 : pack 32 (R05p03_digit 1)=R05p03_rowCode 1 := by decide +kernel

private theorem R05p03_row_02 : pack 32 (R05p03_digit 2)=R05p03_rowCode 2 := by decide +kernel

private theorem R05p03_row_03 : pack 32 (R05p03_digit 3)=R05p03_rowCode 3 := by decide +kernel

private theorem R05p03_row_04 : pack 32 (R05p03_digit 4)=R05p03_rowCode 4 := by decide +kernel

private theorem R05p03_row_05 : pack 32 (R05p03_digit 5)=R05p03_rowCode 5 := by decide +kernel

private theorem R05p03_row_06 : pack 32 (R05p03_digit 6)=R05p03_rowCode 6 := by decide +kernel

private theorem R05p03_row_07 : pack 32 (R05p03_digit 7)=R05p03_rowCode 7 := by decide +kernel

private theorem R05p03_row_08 : pack 32 (R05p03_digit 8)=R05p03_rowCode 8 := by decide +kernel

private theorem R05p03_row_09 : pack 32 (R05p03_digit 9)=R05p03_rowCode 9 := by decide +kernel

private theorem R05p03_row_10 : pack 32 (R05p03_digit 10)=R05p03_rowCode 10 := by decide +kernel

private theorem R05p03_row_11 : pack 32 (R05p03_digit 11)=R05p03_rowCode 11 := by decide +kernel

private theorem R05p03_row_12 : pack 32 (R05p03_digit 12)=R05p03_rowCode 12 := by decide +kernel

private theorem R05p03_row_13 : pack 32 (R05p03_digit 13)=R05p03_rowCode 13 := by decide +kernel

private theorem R05p03_row_14 : pack 32 (R05p03_digit 14)=R05p03_rowCode 14 := by decide +kernel

private theorem R05p03_row_15 : pack 32 (R05p03_digit 15)=R05p03_rowCode 15 := by decide +kernel

private theorem R05p03_row_16 : pack 32 (R05p03_digit 16)=R05p03_rowCode 16 := by decide +kernel

private theorem R05p03_row_17 : pack 32 (R05p03_digit 17)=R05p03_rowCode 17 := by decide +kernel

private theorem R05p03_row_18 : pack 32 (R05p03_digit 18)=R05p03_rowCode 18 := by decide +kernel

private theorem R05p03_row_19 : pack 32 (R05p03_digit 19)=R05p03_rowCode 19 := by decide +kernel

private theorem R05p03_row_20 : pack 32 (R05p03_digit 20)=R05p03_rowCode 20 := by decide +kernel

private theorem R05p03_row_21 : pack 32 (R05p03_digit 21)=R05p03_rowCode 21 := by decide +kernel

theorem R05p03_row_binding : ∀ i : Fin 22,pack 32 (R05p03_digit i)=R05p03_rowCode i := by
  intro i
  fin_cases i
  · exact R05p03_row_00
  · exact R05p03_row_01
  · exact R05p03_row_02
  · exact R05p03_row_03
  · exact R05p03_row_04
  · exact R05p03_row_05
  · exact R05p03_row_06
  · exact R05p03_row_07
  · exact R05p03_row_08
  · exact R05p03_row_09
  · exact R05p03_row_10
  · exact R05p03_row_11
  · exact R05p03_row_12
  · exact R05p03_row_13
  · exact R05p03_row_14
  · exact R05p03_row_15
  · exact R05p03_row_16
  · exact R05p03_row_17
  · exact R05p03_row_18
  · exact R05p03_row_19
  · exact R05p03_row_20
  · exact R05p03_row_21

private theorem R05p03_column_00 : reversePack 32 (fun j : Fin 22 => R05p03_digit j 0)=R05p03_columnCode 0 := by decide +kernel

private theorem R05p03_column_01 : reversePack 32 (fun j : Fin 22 => R05p03_digit j 1)=R05p03_columnCode 1 := by decide +kernel

private theorem R05p03_column_02 : reversePack 32 (fun j : Fin 22 => R05p03_digit j 2)=R05p03_columnCode 2 := by decide +kernel

private theorem R05p03_column_03 : reversePack 32 (fun j : Fin 22 => R05p03_digit j 3)=R05p03_columnCode 3 := by decide +kernel

private theorem R05p03_column_04 : reversePack 32 (fun j : Fin 22 => R05p03_digit j 4)=R05p03_columnCode 4 := by decide +kernel

private theorem R05p03_column_05 : reversePack 32 (fun j : Fin 22 => R05p03_digit j 5)=R05p03_columnCode 5 := by decide +kernel

private theorem R05p03_column_06 : reversePack 32 (fun j : Fin 22 => R05p03_digit j 6)=R05p03_columnCode 6 := by decide +kernel

private theorem R05p03_column_07 : reversePack 32 (fun j : Fin 22 => R05p03_digit j 7)=R05p03_columnCode 7 := by decide +kernel

private theorem R05p03_column_08 : reversePack 32 (fun j : Fin 22 => R05p03_digit j 8)=R05p03_columnCode 8 := by decide +kernel

private theorem R05p03_column_09 : reversePack 32 (fun j : Fin 22 => R05p03_digit j 9)=R05p03_columnCode 9 := by decide +kernel

private theorem R05p03_column_10 : reversePack 32 (fun j : Fin 22 => R05p03_digit j 10)=R05p03_columnCode 10 := by decide +kernel

private theorem R05p03_column_11 : reversePack 32 (fun j : Fin 22 => R05p03_digit j 11)=R05p03_columnCode 11 := by decide +kernel

private theorem R05p03_column_12 : reversePack 32 (fun j : Fin 22 => R05p03_digit j 12)=R05p03_columnCode 12 := by decide +kernel

private theorem R05p03_column_13 : reversePack 32 (fun j : Fin 22 => R05p03_digit j 13)=R05p03_columnCode 13 := by decide +kernel

private theorem R05p03_column_14 : reversePack 32 (fun j : Fin 22 => R05p03_digit j 14)=R05p03_columnCode 14 := by decide +kernel

private theorem R05p03_column_15 : reversePack 32 (fun j : Fin 22 => R05p03_digit j 15)=R05p03_columnCode 15 := by decide +kernel

private theorem R05p03_column_16 : reversePack 32 (fun j : Fin 22 => R05p03_digit j 16)=R05p03_columnCode 16 := by decide +kernel

private theorem R05p03_column_17 : reversePack 32 (fun j : Fin 22 => R05p03_digit j 17)=R05p03_columnCode 17 := by decide +kernel

private theorem R05p03_column_18 : reversePack 32 (fun j : Fin 22 => R05p03_digit j 18)=R05p03_columnCode 18 := by decide +kernel

private theorem R05p03_column_19 : reversePack 32 (fun j : Fin 22 => R05p03_digit j 19)=R05p03_columnCode 19 := by decide +kernel

private theorem R05p03_column_20 : reversePack 32 (fun j : Fin 22 => R05p03_digit j 20)=R05p03_columnCode 20 := by decide +kernel

private theorem R05p03_column_21 : reversePack 32 (fun j : Fin 22 => R05p03_digit j 21)=R05p03_columnCode 21 := by decide +kernel

theorem R05p03_column_binding : ∀ i : Fin 22,reversePack 32 (fun j : Fin 22 => R05p03_digit j i)=R05p03_columnCode i := by
  intro i
  fin_cases i
  · exact R05p03_column_00
  · exact R05p03_column_01
  · exact R05p03_column_02
  · exact R05p03_column_03
  · exact R05p03_column_04
  · exact R05p03_column_05
  · exact R05p03_column_06
  · exact R05p03_column_07
  · exact R05p03_column_08
  · exact R05p03_column_09
  · exact R05p03_column_10
  · exact R05p03_column_11
  · exact R05p03_column_12
  · exact R05p03_column_13
  · exact R05p03_column_14
  · exact R05p03_column_15
  · exact R05p03_column_16
  · exact R05p03_column_17
  · exact R05p03_column_18
  · exact R05p03_column_19
  · exact R05p03_column_20
  · exact R05p03_column_21

def R05p03_data : PackedData 22 2 32 where
  raw := R05p03_digit
  digit_lt := R05p03_bound
  rowCode := R05p03_rowCode
  columnCode := R05p03_columnCode
  row_binding := R05p03_row_binding
  column_binding := R05p03_column_binding

end SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoCaches02
