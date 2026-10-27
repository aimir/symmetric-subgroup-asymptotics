import SymmetricSubgroupAsymptotics.MatrixKroneckerProductReflection
import Mathlib.Tactic.FinCases

/-! Fixed Co2 binary22 shared caches. Every digit and pack binding is kernel checked. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoCaches13
open MatrixKroneckerProductReflection MatrixKroneckerDotReflection
open MatrixNaturalRowDotReflection SmallNaturalMatrixProductReflection

def Wp03_lowColumnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 2367499
  | 1 => 3964104
  | 2 => 1358530
  | 3 => 3471792
  | 4 => 3471291
  | 5 => 2293001
  | 6 => 2270496
  | 7 => 497540
  | 8 => 2147088
  | 9 => 3037071
  | 10 => 3601574
  | 11 => 665263
  | 12 => 2659200
  | 13 => 1179936
  | 14 => 12960
  | 15 => 3576708
  | 16 => 1474560
  | 17 => 3424128
  | 18 => 1370896
  | 19 => 1104304
  | 20 => 2148112
  | 21 => 3416064
  | _ => 0

def Wp03_rowCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 36063981425655809
  | 1 => 37189881298945025
  | 2 => 37778969052872819343360
  | 3 => 36063981425655841
  | 4 => 1308502621524646951667887013888
  | 5 => 39614082474654432359603011584
  | 6 => 1056
  | 7 => 39652805844073432025201148960
  | 8 => 1308541344967852927630504394752
  | 9 => 1268927264854454920199636255744
  | 10 => 1267689285854494259547059781664
  | 11 => 40890706922645217205295285280
  | 12 => 39652805844037403228215739424
  | 13 => 40566095834149482671718437782561
  | 14 => 1308502621524648112752199499808
  | 15 => 1308503868230552476694204154880
  | 16 => 34359738368
  | 17 => 1246741682155650520449024
  | 18 => 40566097079673606535007968461857
  | 19 => 1188985485997899808
  | 20 => 40605711160967632156733427713056
  | 21 => 41832508530937883864171463868449
  | _ => 0

def Wp03_columnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 41833707747570855630765616562177
  | 1 => 1237978998846054964641432609
  | 2 => 1267650639188906968860747399200
  | 3 => 39895769533553846819782689
  | 4 => 41833747643341577007914643652641
  | 5 => 40566057147379556907333064851457
  | 6 => 1208962749132674199191553
  | 7 => 39614082475806263148708659200
  | 8 => 38685664274077821050028033
  | 9 => 41873321830046661892848066003969
  | 10 => 1307265891591808870756398432289
  | 11 => 41873323038935587985210601374720
  | 12 => 1218638065554883085313
  | 13 => 1208962713102776594858016
  | 14 => 1210107564193135076573184
  | 15 => 39614082475770234351656140833
  | 16 => 1074823200
  | 17 => 1218675221350246809633
  | 18 => 38685664275204820468531232
  | 19 => 39895769533552747308122144
  | 20 => 38685664310106618068992001
  | 21 => 1099511660577
  | _ => 0

def Wp03_digit (i j : Fin 22) : ℕ := packedDigit 1 (Wp03_lowColumnCode j) i.val

private theorem Wp03_bound_00 : ∀ j : Fin 22,Wp03_digit 0 j<2 := by decide +kernel

private theorem Wp03_bound_01 : ∀ j : Fin 22,Wp03_digit 1 j<2 := by decide +kernel

private theorem Wp03_bound_02 : ∀ j : Fin 22,Wp03_digit 2 j<2 := by decide +kernel

private theorem Wp03_bound_03 : ∀ j : Fin 22,Wp03_digit 3 j<2 := by decide +kernel

private theorem Wp03_bound_04 : ∀ j : Fin 22,Wp03_digit 4 j<2 := by decide +kernel

private theorem Wp03_bound_05 : ∀ j : Fin 22,Wp03_digit 5 j<2 := by decide +kernel

private theorem Wp03_bound_06 : ∀ j : Fin 22,Wp03_digit 6 j<2 := by decide +kernel

private theorem Wp03_bound_07 : ∀ j : Fin 22,Wp03_digit 7 j<2 := by decide +kernel

private theorem Wp03_bound_08 : ∀ j : Fin 22,Wp03_digit 8 j<2 := by decide +kernel

private theorem Wp03_bound_09 : ∀ j : Fin 22,Wp03_digit 9 j<2 := by decide +kernel

private theorem Wp03_bound_10 : ∀ j : Fin 22,Wp03_digit 10 j<2 := by decide +kernel

private theorem Wp03_bound_11 : ∀ j : Fin 22,Wp03_digit 11 j<2 := by decide +kernel

private theorem Wp03_bound_12 : ∀ j : Fin 22,Wp03_digit 12 j<2 := by decide +kernel

private theorem Wp03_bound_13 : ∀ j : Fin 22,Wp03_digit 13 j<2 := by decide +kernel

private theorem Wp03_bound_14 : ∀ j : Fin 22,Wp03_digit 14 j<2 := by decide +kernel

private theorem Wp03_bound_15 : ∀ j : Fin 22,Wp03_digit 15 j<2 := by decide +kernel

private theorem Wp03_bound_16 : ∀ j : Fin 22,Wp03_digit 16 j<2 := by decide +kernel

private theorem Wp03_bound_17 : ∀ j : Fin 22,Wp03_digit 17 j<2 := by decide +kernel

private theorem Wp03_bound_18 : ∀ j : Fin 22,Wp03_digit 18 j<2 := by decide +kernel

private theorem Wp03_bound_19 : ∀ j : Fin 22,Wp03_digit 19 j<2 := by decide +kernel

private theorem Wp03_bound_20 : ∀ j : Fin 22,Wp03_digit 20 j<2 := by decide +kernel

private theorem Wp03_bound_21 : ∀ j : Fin 22,Wp03_digit 21 j<2 := by decide +kernel

theorem Wp03_bound : ∀ i j : Fin 22,Wp03_digit i j<2 := by
  intro i j
  fin_cases i
  · exact Wp03_bound_00 j
  · exact Wp03_bound_01 j
  · exact Wp03_bound_02 j
  · exact Wp03_bound_03 j
  · exact Wp03_bound_04 j
  · exact Wp03_bound_05 j
  · exact Wp03_bound_06 j
  · exact Wp03_bound_07 j
  · exact Wp03_bound_08 j
  · exact Wp03_bound_09 j
  · exact Wp03_bound_10 j
  · exact Wp03_bound_11 j
  · exact Wp03_bound_12 j
  · exact Wp03_bound_13 j
  · exact Wp03_bound_14 j
  · exact Wp03_bound_15 j
  · exact Wp03_bound_16 j
  · exact Wp03_bound_17 j
  · exact Wp03_bound_18 j
  · exact Wp03_bound_19 j
  · exact Wp03_bound_20 j
  · exact Wp03_bound_21 j

private theorem Wp03_row_00 : pack 32 (Wp03_digit 0)=Wp03_rowCode 0 := by decide +kernel

private theorem Wp03_row_01 : pack 32 (Wp03_digit 1)=Wp03_rowCode 1 := by decide +kernel

private theorem Wp03_row_02 : pack 32 (Wp03_digit 2)=Wp03_rowCode 2 := by decide +kernel

private theorem Wp03_row_03 : pack 32 (Wp03_digit 3)=Wp03_rowCode 3 := by decide +kernel

private theorem Wp03_row_04 : pack 32 (Wp03_digit 4)=Wp03_rowCode 4 := by decide +kernel

private theorem Wp03_row_05 : pack 32 (Wp03_digit 5)=Wp03_rowCode 5 := by decide +kernel

private theorem Wp03_row_06 : pack 32 (Wp03_digit 6)=Wp03_rowCode 6 := by decide +kernel

private theorem Wp03_row_07 : pack 32 (Wp03_digit 7)=Wp03_rowCode 7 := by decide +kernel

private theorem Wp03_row_08 : pack 32 (Wp03_digit 8)=Wp03_rowCode 8 := by decide +kernel

private theorem Wp03_row_09 : pack 32 (Wp03_digit 9)=Wp03_rowCode 9 := by decide +kernel

private theorem Wp03_row_10 : pack 32 (Wp03_digit 10)=Wp03_rowCode 10 := by decide +kernel

private theorem Wp03_row_11 : pack 32 (Wp03_digit 11)=Wp03_rowCode 11 := by decide +kernel

private theorem Wp03_row_12 : pack 32 (Wp03_digit 12)=Wp03_rowCode 12 := by decide +kernel

private theorem Wp03_row_13 : pack 32 (Wp03_digit 13)=Wp03_rowCode 13 := by decide +kernel

private theorem Wp03_row_14 : pack 32 (Wp03_digit 14)=Wp03_rowCode 14 := by decide +kernel

private theorem Wp03_row_15 : pack 32 (Wp03_digit 15)=Wp03_rowCode 15 := by decide +kernel

private theorem Wp03_row_16 : pack 32 (Wp03_digit 16)=Wp03_rowCode 16 := by decide +kernel

private theorem Wp03_row_17 : pack 32 (Wp03_digit 17)=Wp03_rowCode 17 := by decide +kernel

private theorem Wp03_row_18 : pack 32 (Wp03_digit 18)=Wp03_rowCode 18 := by decide +kernel

private theorem Wp03_row_19 : pack 32 (Wp03_digit 19)=Wp03_rowCode 19 := by decide +kernel

private theorem Wp03_row_20 : pack 32 (Wp03_digit 20)=Wp03_rowCode 20 := by decide +kernel

private theorem Wp03_row_21 : pack 32 (Wp03_digit 21)=Wp03_rowCode 21 := by decide +kernel

theorem Wp03_row_binding : ∀ i : Fin 22,pack 32 (Wp03_digit i)=Wp03_rowCode i := by
  intro i
  fin_cases i
  · exact Wp03_row_00
  · exact Wp03_row_01
  · exact Wp03_row_02
  · exact Wp03_row_03
  · exact Wp03_row_04
  · exact Wp03_row_05
  · exact Wp03_row_06
  · exact Wp03_row_07
  · exact Wp03_row_08
  · exact Wp03_row_09
  · exact Wp03_row_10
  · exact Wp03_row_11
  · exact Wp03_row_12
  · exact Wp03_row_13
  · exact Wp03_row_14
  · exact Wp03_row_15
  · exact Wp03_row_16
  · exact Wp03_row_17
  · exact Wp03_row_18
  · exact Wp03_row_19
  · exact Wp03_row_20
  · exact Wp03_row_21

private theorem Wp03_column_00 : reversePack 32 (fun j : Fin 22 => Wp03_digit j 0)=Wp03_columnCode 0 := by decide +kernel

private theorem Wp03_column_01 : reversePack 32 (fun j : Fin 22 => Wp03_digit j 1)=Wp03_columnCode 1 := by decide +kernel

private theorem Wp03_column_02 : reversePack 32 (fun j : Fin 22 => Wp03_digit j 2)=Wp03_columnCode 2 := by decide +kernel

private theorem Wp03_column_03 : reversePack 32 (fun j : Fin 22 => Wp03_digit j 3)=Wp03_columnCode 3 := by decide +kernel

private theorem Wp03_column_04 : reversePack 32 (fun j : Fin 22 => Wp03_digit j 4)=Wp03_columnCode 4 := by decide +kernel

private theorem Wp03_column_05 : reversePack 32 (fun j : Fin 22 => Wp03_digit j 5)=Wp03_columnCode 5 := by decide +kernel

private theorem Wp03_column_06 : reversePack 32 (fun j : Fin 22 => Wp03_digit j 6)=Wp03_columnCode 6 := by decide +kernel

private theorem Wp03_column_07 : reversePack 32 (fun j : Fin 22 => Wp03_digit j 7)=Wp03_columnCode 7 := by decide +kernel

private theorem Wp03_column_08 : reversePack 32 (fun j : Fin 22 => Wp03_digit j 8)=Wp03_columnCode 8 := by decide +kernel

private theorem Wp03_column_09 : reversePack 32 (fun j : Fin 22 => Wp03_digit j 9)=Wp03_columnCode 9 := by decide +kernel

private theorem Wp03_column_10 : reversePack 32 (fun j : Fin 22 => Wp03_digit j 10)=Wp03_columnCode 10 := by decide +kernel

private theorem Wp03_column_11 : reversePack 32 (fun j : Fin 22 => Wp03_digit j 11)=Wp03_columnCode 11 := by decide +kernel

private theorem Wp03_column_12 : reversePack 32 (fun j : Fin 22 => Wp03_digit j 12)=Wp03_columnCode 12 := by decide +kernel

private theorem Wp03_column_13 : reversePack 32 (fun j : Fin 22 => Wp03_digit j 13)=Wp03_columnCode 13 := by decide +kernel

private theorem Wp03_column_14 : reversePack 32 (fun j : Fin 22 => Wp03_digit j 14)=Wp03_columnCode 14 := by decide +kernel

private theorem Wp03_column_15 : reversePack 32 (fun j : Fin 22 => Wp03_digit j 15)=Wp03_columnCode 15 := by decide +kernel

private theorem Wp03_column_16 : reversePack 32 (fun j : Fin 22 => Wp03_digit j 16)=Wp03_columnCode 16 := by decide +kernel

private theorem Wp03_column_17 : reversePack 32 (fun j : Fin 22 => Wp03_digit j 17)=Wp03_columnCode 17 := by decide +kernel

private theorem Wp03_column_18 : reversePack 32 (fun j : Fin 22 => Wp03_digit j 18)=Wp03_columnCode 18 := by decide +kernel

private theorem Wp03_column_19 : reversePack 32 (fun j : Fin 22 => Wp03_digit j 19)=Wp03_columnCode 19 := by decide +kernel

private theorem Wp03_column_20 : reversePack 32 (fun j : Fin 22 => Wp03_digit j 20)=Wp03_columnCode 20 := by decide +kernel

private theorem Wp03_column_21 : reversePack 32 (fun j : Fin 22 => Wp03_digit j 21)=Wp03_columnCode 21 := by decide +kernel

theorem Wp03_column_binding : ∀ i : Fin 22,reversePack 32 (fun j : Fin 22 => Wp03_digit j i)=Wp03_columnCode i := by
  intro i
  fin_cases i
  · exact Wp03_column_00
  · exact Wp03_column_01
  · exact Wp03_column_02
  · exact Wp03_column_03
  · exact Wp03_column_04
  · exact Wp03_column_05
  · exact Wp03_column_06
  · exact Wp03_column_07
  · exact Wp03_column_08
  · exact Wp03_column_09
  · exact Wp03_column_10
  · exact Wp03_column_11
  · exact Wp03_column_12
  · exact Wp03_column_13
  · exact Wp03_column_14
  · exact Wp03_column_15
  · exact Wp03_column_16
  · exact Wp03_column_17
  · exact Wp03_column_18
  · exact Wp03_column_19
  · exact Wp03_column_20
  · exact Wp03_column_21

def Wp03_data : PackedData 22 2 32 where
  raw := Wp03_digit
  digit_lt := Wp03_bound
  rowCode := Wp03_rowCode
  columnCode := Wp03_columnCode
  row_binding := Wp03_row_binding
  column_binding := Wp03_column_binding

def Wp04_lowColumnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 2505191
  | 1 => 4089124
  | 2 => 1326752
  | 3 => 3440082
  | 4 => 2580923
  | 5 => 3504011
  | 6 => 3224352
  | 7 => 497540
  | 8 => 3623314
  | 9 => 3037071
  | 10 => 3601574
  | 11 => 665263
  | 12 => 2659200
  | 13 => 1477632
  | 14 => 12960
  | 15 => 3149088
  | 16 => 1183008
  | 17 => 3424128
  | 18 => 1370896
  | 19 => 1459988
  | 20 => 2148112
  | 21 => 3416064
  | _ => 0

def Wp04_rowCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 36063981425655809
  | 1 => 37190980844158977
  | 2 => 39614081257169358712429608993
  | 3 => 36063981425655808
  | 4 => 1308502621524646951667887013888
  | 5 => 1247885380253001748317217
  | 6 => 32769
  | 7 => 38686808009401370812646401
  | 8 => 1308542553856779054112259997729
  | 9 => 1308541308332655224940841141248
  | 10 => 1307304613853271394076512519200
  | 11 => 1277872407158015241756902401
  | 12 => 38686807973371475354747905
  | 13 => 40566095834149482671718437782561
  | 14 => 1308502621524648112752199499808
  | 15 => 1268888540305562317357894860800
  | 16 => 1134979710976
  | 17 => 39615290219882462588536094753
  | 18 => 40605709914262880715465368306721
  | 19 => 1188985485997899808
  | 20 => 40605711160967632157834045588512
  | 21 => 41832508530937883864171463868449
  | _ => 0

def Wp04_columnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 41872085136710940166822936215553
  | 1 => 39615290219881301504257197089
  | 2 => 1210107601347832002412576
  | 3 => 1267689324850911232467455213601
  | 4 => 41833747643340388022427606614017
  | 5 => 41833707748789529725150838161441
  | 6 => 1208963866060565117927457
  | 7 => 39614082475806263148708659200
  | 8 => 1267689287071943304429425426465
  | 9 => 41873321830046661892848066003969
  | 10 => 1307265891591808870756398432289
  | 11 => 41873323038935587985210601374720
  | 12 => 1218638065554883085313
  | 13 => 37154698000629792
  | 14 => 1210107564193135076573184
  | 15 => 1208962750257473519616033
  | 16 => 1208962750257473520664608
  | 17 => 1218675221350246809633
  | 18 => 38685664275204820468531232
  | 19 => 39652766921442275413768306720
  | 20 => 38685664310106618068992001
  | 21 => 1099511660577
  | _ => 0

def Wp04_digit (i j : Fin 22) : ℕ := packedDigit 1 (Wp04_lowColumnCode j) i.val

private theorem Wp04_bound_00 : ∀ j : Fin 22,Wp04_digit 0 j<2 := by decide +kernel

private theorem Wp04_bound_01 : ∀ j : Fin 22,Wp04_digit 1 j<2 := by decide +kernel

private theorem Wp04_bound_02 : ∀ j : Fin 22,Wp04_digit 2 j<2 := by decide +kernel

private theorem Wp04_bound_03 : ∀ j : Fin 22,Wp04_digit 3 j<2 := by decide +kernel

private theorem Wp04_bound_04 : ∀ j : Fin 22,Wp04_digit 4 j<2 := by decide +kernel

private theorem Wp04_bound_05 : ∀ j : Fin 22,Wp04_digit 5 j<2 := by decide +kernel

private theorem Wp04_bound_06 : ∀ j : Fin 22,Wp04_digit 6 j<2 := by decide +kernel

private theorem Wp04_bound_07 : ∀ j : Fin 22,Wp04_digit 7 j<2 := by decide +kernel

private theorem Wp04_bound_08 : ∀ j : Fin 22,Wp04_digit 8 j<2 := by decide +kernel

private theorem Wp04_bound_09 : ∀ j : Fin 22,Wp04_digit 9 j<2 := by decide +kernel

private theorem Wp04_bound_10 : ∀ j : Fin 22,Wp04_digit 10 j<2 := by decide +kernel

private theorem Wp04_bound_11 : ∀ j : Fin 22,Wp04_digit 11 j<2 := by decide +kernel

private theorem Wp04_bound_12 : ∀ j : Fin 22,Wp04_digit 12 j<2 := by decide +kernel

private theorem Wp04_bound_13 : ∀ j : Fin 22,Wp04_digit 13 j<2 := by decide +kernel

private theorem Wp04_bound_14 : ∀ j : Fin 22,Wp04_digit 14 j<2 := by decide +kernel

private theorem Wp04_bound_15 : ∀ j : Fin 22,Wp04_digit 15 j<2 := by decide +kernel

private theorem Wp04_bound_16 : ∀ j : Fin 22,Wp04_digit 16 j<2 := by decide +kernel

private theorem Wp04_bound_17 : ∀ j : Fin 22,Wp04_digit 17 j<2 := by decide +kernel

private theorem Wp04_bound_18 : ∀ j : Fin 22,Wp04_digit 18 j<2 := by decide +kernel

private theorem Wp04_bound_19 : ∀ j : Fin 22,Wp04_digit 19 j<2 := by decide +kernel

private theorem Wp04_bound_20 : ∀ j : Fin 22,Wp04_digit 20 j<2 := by decide +kernel

private theorem Wp04_bound_21 : ∀ j : Fin 22,Wp04_digit 21 j<2 := by decide +kernel

theorem Wp04_bound : ∀ i j : Fin 22,Wp04_digit i j<2 := by
  intro i j
  fin_cases i
  · exact Wp04_bound_00 j
  · exact Wp04_bound_01 j
  · exact Wp04_bound_02 j
  · exact Wp04_bound_03 j
  · exact Wp04_bound_04 j
  · exact Wp04_bound_05 j
  · exact Wp04_bound_06 j
  · exact Wp04_bound_07 j
  · exact Wp04_bound_08 j
  · exact Wp04_bound_09 j
  · exact Wp04_bound_10 j
  · exact Wp04_bound_11 j
  · exact Wp04_bound_12 j
  · exact Wp04_bound_13 j
  · exact Wp04_bound_14 j
  · exact Wp04_bound_15 j
  · exact Wp04_bound_16 j
  · exact Wp04_bound_17 j
  · exact Wp04_bound_18 j
  · exact Wp04_bound_19 j
  · exact Wp04_bound_20 j
  · exact Wp04_bound_21 j

private theorem Wp04_row_00 : pack 32 (Wp04_digit 0)=Wp04_rowCode 0 := by decide +kernel

private theorem Wp04_row_01 : pack 32 (Wp04_digit 1)=Wp04_rowCode 1 := by decide +kernel

private theorem Wp04_row_02 : pack 32 (Wp04_digit 2)=Wp04_rowCode 2 := by decide +kernel

private theorem Wp04_row_03 : pack 32 (Wp04_digit 3)=Wp04_rowCode 3 := by decide +kernel

private theorem Wp04_row_04 : pack 32 (Wp04_digit 4)=Wp04_rowCode 4 := by decide +kernel

private theorem Wp04_row_05 : pack 32 (Wp04_digit 5)=Wp04_rowCode 5 := by decide +kernel

private theorem Wp04_row_06 : pack 32 (Wp04_digit 6)=Wp04_rowCode 6 := by decide +kernel

private theorem Wp04_row_07 : pack 32 (Wp04_digit 7)=Wp04_rowCode 7 := by decide +kernel

private theorem Wp04_row_08 : pack 32 (Wp04_digit 8)=Wp04_rowCode 8 := by decide +kernel

private theorem Wp04_row_09 : pack 32 (Wp04_digit 9)=Wp04_rowCode 9 := by decide +kernel

private theorem Wp04_row_10 : pack 32 (Wp04_digit 10)=Wp04_rowCode 10 := by decide +kernel

private theorem Wp04_row_11 : pack 32 (Wp04_digit 11)=Wp04_rowCode 11 := by decide +kernel

private theorem Wp04_row_12 : pack 32 (Wp04_digit 12)=Wp04_rowCode 12 := by decide +kernel

private theorem Wp04_row_13 : pack 32 (Wp04_digit 13)=Wp04_rowCode 13 := by decide +kernel

private theorem Wp04_row_14 : pack 32 (Wp04_digit 14)=Wp04_rowCode 14 := by decide +kernel

private theorem Wp04_row_15 : pack 32 (Wp04_digit 15)=Wp04_rowCode 15 := by decide +kernel

private theorem Wp04_row_16 : pack 32 (Wp04_digit 16)=Wp04_rowCode 16 := by decide +kernel

private theorem Wp04_row_17 : pack 32 (Wp04_digit 17)=Wp04_rowCode 17 := by decide +kernel

private theorem Wp04_row_18 : pack 32 (Wp04_digit 18)=Wp04_rowCode 18 := by decide +kernel

private theorem Wp04_row_19 : pack 32 (Wp04_digit 19)=Wp04_rowCode 19 := by decide +kernel

private theorem Wp04_row_20 : pack 32 (Wp04_digit 20)=Wp04_rowCode 20 := by decide +kernel

private theorem Wp04_row_21 : pack 32 (Wp04_digit 21)=Wp04_rowCode 21 := by decide +kernel

theorem Wp04_row_binding : ∀ i : Fin 22,pack 32 (Wp04_digit i)=Wp04_rowCode i := by
  intro i
  fin_cases i
  · exact Wp04_row_00
  · exact Wp04_row_01
  · exact Wp04_row_02
  · exact Wp04_row_03
  · exact Wp04_row_04
  · exact Wp04_row_05
  · exact Wp04_row_06
  · exact Wp04_row_07
  · exact Wp04_row_08
  · exact Wp04_row_09
  · exact Wp04_row_10
  · exact Wp04_row_11
  · exact Wp04_row_12
  · exact Wp04_row_13
  · exact Wp04_row_14
  · exact Wp04_row_15
  · exact Wp04_row_16
  · exact Wp04_row_17
  · exact Wp04_row_18
  · exact Wp04_row_19
  · exact Wp04_row_20
  · exact Wp04_row_21

private theorem Wp04_column_00 : reversePack 32 (fun j : Fin 22 => Wp04_digit j 0)=Wp04_columnCode 0 := by decide +kernel

private theorem Wp04_column_01 : reversePack 32 (fun j : Fin 22 => Wp04_digit j 1)=Wp04_columnCode 1 := by decide +kernel

private theorem Wp04_column_02 : reversePack 32 (fun j : Fin 22 => Wp04_digit j 2)=Wp04_columnCode 2 := by decide +kernel

private theorem Wp04_column_03 : reversePack 32 (fun j : Fin 22 => Wp04_digit j 3)=Wp04_columnCode 3 := by decide +kernel

private theorem Wp04_column_04 : reversePack 32 (fun j : Fin 22 => Wp04_digit j 4)=Wp04_columnCode 4 := by decide +kernel

private theorem Wp04_column_05 : reversePack 32 (fun j : Fin 22 => Wp04_digit j 5)=Wp04_columnCode 5 := by decide +kernel

private theorem Wp04_column_06 : reversePack 32 (fun j : Fin 22 => Wp04_digit j 6)=Wp04_columnCode 6 := by decide +kernel

private theorem Wp04_column_07 : reversePack 32 (fun j : Fin 22 => Wp04_digit j 7)=Wp04_columnCode 7 := by decide +kernel

private theorem Wp04_column_08 : reversePack 32 (fun j : Fin 22 => Wp04_digit j 8)=Wp04_columnCode 8 := by decide +kernel

private theorem Wp04_column_09 : reversePack 32 (fun j : Fin 22 => Wp04_digit j 9)=Wp04_columnCode 9 := by decide +kernel

private theorem Wp04_column_10 : reversePack 32 (fun j : Fin 22 => Wp04_digit j 10)=Wp04_columnCode 10 := by decide +kernel

private theorem Wp04_column_11 : reversePack 32 (fun j : Fin 22 => Wp04_digit j 11)=Wp04_columnCode 11 := by decide +kernel

private theorem Wp04_column_12 : reversePack 32 (fun j : Fin 22 => Wp04_digit j 12)=Wp04_columnCode 12 := by decide +kernel

private theorem Wp04_column_13 : reversePack 32 (fun j : Fin 22 => Wp04_digit j 13)=Wp04_columnCode 13 := by decide +kernel

private theorem Wp04_column_14 : reversePack 32 (fun j : Fin 22 => Wp04_digit j 14)=Wp04_columnCode 14 := by decide +kernel

private theorem Wp04_column_15 : reversePack 32 (fun j : Fin 22 => Wp04_digit j 15)=Wp04_columnCode 15 := by decide +kernel

private theorem Wp04_column_16 : reversePack 32 (fun j : Fin 22 => Wp04_digit j 16)=Wp04_columnCode 16 := by decide +kernel

private theorem Wp04_column_17 : reversePack 32 (fun j : Fin 22 => Wp04_digit j 17)=Wp04_columnCode 17 := by decide +kernel

private theorem Wp04_column_18 : reversePack 32 (fun j : Fin 22 => Wp04_digit j 18)=Wp04_columnCode 18 := by decide +kernel

private theorem Wp04_column_19 : reversePack 32 (fun j : Fin 22 => Wp04_digit j 19)=Wp04_columnCode 19 := by decide +kernel

private theorem Wp04_column_20 : reversePack 32 (fun j : Fin 22 => Wp04_digit j 20)=Wp04_columnCode 20 := by decide +kernel

private theorem Wp04_column_21 : reversePack 32 (fun j : Fin 22 => Wp04_digit j 21)=Wp04_columnCode 21 := by decide +kernel

theorem Wp04_column_binding : ∀ i : Fin 22,reversePack 32 (fun j : Fin 22 => Wp04_digit j i)=Wp04_columnCode i := by
  intro i
  fin_cases i
  · exact Wp04_column_00
  · exact Wp04_column_01
  · exact Wp04_column_02
  · exact Wp04_column_03
  · exact Wp04_column_04
  · exact Wp04_column_05
  · exact Wp04_column_06
  · exact Wp04_column_07
  · exact Wp04_column_08
  · exact Wp04_column_09
  · exact Wp04_column_10
  · exact Wp04_column_11
  · exact Wp04_column_12
  · exact Wp04_column_13
  · exact Wp04_column_14
  · exact Wp04_column_15
  · exact Wp04_column_16
  · exact Wp04_column_17
  · exact Wp04_column_18
  · exact Wp04_column_19
  · exact Wp04_column_20
  · exact Wp04_column_21

def Wp04_data : PackedData 22 2 32 where
  raw := Wp04_digit
  digit_lt := Wp04_bound
  rowCode := Wp04_rowCode
  columnCode := Wp04_columnCode
  row_binding := Wp04_row_binding
  column_binding := Wp04_column_binding

def Wp05_lowColumnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 2250299
  | 1 => 2785844
  | 2 => 1811611
  | 3 => 2804272
  | 4 => 2873960
  | 5 => 3298448
  | 6 => 2274176
  | 7 => 3276575
  | 8 => 16032
  | 9 => 3548258
  | 10 => 158480
  | 11 => 1365424
  | 12 => 3616315
  | 13 => 3364912
  | 14 => 3529526
  | 15 => 2887231
  | 16 => 2148112
  | 17 => 2283682
  | 18 => 660495
  | 19 => 172036
  | 20 => 3571716
  | 21 => 3172916
  | _ => 0

def Wp05_rowCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1237977819370164771027420161
  | 1 => 1276664626189488806401410049
  | 2 => 41873321867787511282171809628192
  | 3 => 1237977819370164771028468737
  | 4 => 40564820455226767510581595374625
  | 5 => 40564857931927174474435595894817
  | 6 => 35184373137408
  | 7 => 38685626263698031228486656
  | 8 => 1210106448390078945296384
  | 9 => 40564820455189837994737710170145
  | 10 => 1239186745225844481138361345
  | 11 => 40564857931927139536388471422976
  | 12 => 1276626883034187205318803457
  | 13 => 40604433288561627100415105434624
  | 14 => 40564859103072910394253418463233
  | 15 => 1307304577218036502606105314336
  | 16 => 1218638030403798041600
  | 17 => 1308541307188922189439378162721
  | 18 => 1267650639188941870657274118144
  | 19 => 1237977818217243232061916192
  | 20 => 41832469808750244343776427377664
  | 21 => 41832509741081187460700410249249
  | _ => 0

def Wp05_columnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 41833747642124091897949228892161
  | 1 => 39653975810332373065218917377
  | 2 => 41833746434377710948414745740320
  | 3 => 39894553201330202713523201
  | 4 => 1239186745190940485589402625
  | 5 => 38686806855352866753740833
  | 6 => 1218638066654395760641
  | 7 => 41873360514492299067264769982497
  | 8 => 1210107601347832002379776
  | 9 => 1267651846933016908979571294241
  | 10 => 38685664275204819395805184
  | 11 => 39895769568455644420276256
  | 12 => 41833747642124092989729949122593
  | 13 => 39894552048443881438576673
  | 14 => 1307304576075456423828012433441
  | 15 => 41873361723381225157427174867969
  | 16 => 38685664310106618068992001
  | 17 => 1267651810334641797963002675201
  | 18 => 41873321828828023862444268979200
  | 19 => 39614081257132169897358393344
  | 20 => 39614081257132168797846798369
  | 21 => 39653975810333500097922334753
  | _ => 0

def Wp05_digit (i j : Fin 22) : ℕ := packedDigit 1 (Wp05_lowColumnCode j) i.val

private theorem Wp05_bound_00 : ∀ j : Fin 22,Wp05_digit 0 j<2 := by decide +kernel

private theorem Wp05_bound_01 : ∀ j : Fin 22,Wp05_digit 1 j<2 := by decide +kernel

private theorem Wp05_bound_02 : ∀ j : Fin 22,Wp05_digit 2 j<2 := by decide +kernel

private theorem Wp05_bound_03 : ∀ j : Fin 22,Wp05_digit 3 j<2 := by decide +kernel

private theorem Wp05_bound_04 : ∀ j : Fin 22,Wp05_digit 4 j<2 := by decide +kernel

private theorem Wp05_bound_05 : ∀ j : Fin 22,Wp05_digit 5 j<2 := by decide +kernel

private theorem Wp05_bound_06 : ∀ j : Fin 22,Wp05_digit 6 j<2 := by decide +kernel

private theorem Wp05_bound_07 : ∀ j : Fin 22,Wp05_digit 7 j<2 := by decide +kernel

private theorem Wp05_bound_08 : ∀ j : Fin 22,Wp05_digit 8 j<2 := by decide +kernel

private theorem Wp05_bound_09 : ∀ j : Fin 22,Wp05_digit 9 j<2 := by decide +kernel

private theorem Wp05_bound_10 : ∀ j : Fin 22,Wp05_digit 10 j<2 := by decide +kernel

private theorem Wp05_bound_11 : ∀ j : Fin 22,Wp05_digit 11 j<2 := by decide +kernel

private theorem Wp05_bound_12 : ∀ j : Fin 22,Wp05_digit 12 j<2 := by decide +kernel

private theorem Wp05_bound_13 : ∀ j : Fin 22,Wp05_digit 13 j<2 := by decide +kernel

private theorem Wp05_bound_14 : ∀ j : Fin 22,Wp05_digit 14 j<2 := by decide +kernel

private theorem Wp05_bound_15 : ∀ j : Fin 22,Wp05_digit 15 j<2 := by decide +kernel

private theorem Wp05_bound_16 : ∀ j : Fin 22,Wp05_digit 16 j<2 := by decide +kernel

private theorem Wp05_bound_17 : ∀ j : Fin 22,Wp05_digit 17 j<2 := by decide +kernel

private theorem Wp05_bound_18 : ∀ j : Fin 22,Wp05_digit 18 j<2 := by decide +kernel

private theorem Wp05_bound_19 : ∀ j : Fin 22,Wp05_digit 19 j<2 := by decide +kernel

private theorem Wp05_bound_20 : ∀ j : Fin 22,Wp05_digit 20 j<2 := by decide +kernel

private theorem Wp05_bound_21 : ∀ j : Fin 22,Wp05_digit 21 j<2 := by decide +kernel

theorem Wp05_bound : ∀ i j : Fin 22,Wp05_digit i j<2 := by
  intro i j
  fin_cases i
  · exact Wp05_bound_00 j
  · exact Wp05_bound_01 j
  · exact Wp05_bound_02 j
  · exact Wp05_bound_03 j
  · exact Wp05_bound_04 j
  · exact Wp05_bound_05 j
  · exact Wp05_bound_06 j
  · exact Wp05_bound_07 j
  · exact Wp05_bound_08 j
  · exact Wp05_bound_09 j
  · exact Wp05_bound_10 j
  · exact Wp05_bound_11 j
  · exact Wp05_bound_12 j
  · exact Wp05_bound_13 j
  · exact Wp05_bound_14 j
  · exact Wp05_bound_15 j
  · exact Wp05_bound_16 j
  · exact Wp05_bound_17 j
  · exact Wp05_bound_18 j
  · exact Wp05_bound_19 j
  · exact Wp05_bound_20 j
  · exact Wp05_bound_21 j

private theorem Wp05_row_00 : pack 32 (Wp05_digit 0)=Wp05_rowCode 0 := by decide +kernel

private theorem Wp05_row_01 : pack 32 (Wp05_digit 1)=Wp05_rowCode 1 := by decide +kernel

private theorem Wp05_row_02 : pack 32 (Wp05_digit 2)=Wp05_rowCode 2 := by decide +kernel

private theorem Wp05_row_03 : pack 32 (Wp05_digit 3)=Wp05_rowCode 3 := by decide +kernel

private theorem Wp05_row_04 : pack 32 (Wp05_digit 4)=Wp05_rowCode 4 := by decide +kernel

private theorem Wp05_row_05 : pack 32 (Wp05_digit 5)=Wp05_rowCode 5 := by decide +kernel

private theorem Wp05_row_06 : pack 32 (Wp05_digit 6)=Wp05_rowCode 6 := by decide +kernel

private theorem Wp05_row_07 : pack 32 (Wp05_digit 7)=Wp05_rowCode 7 := by decide +kernel

private theorem Wp05_row_08 : pack 32 (Wp05_digit 8)=Wp05_rowCode 8 := by decide +kernel

private theorem Wp05_row_09 : pack 32 (Wp05_digit 9)=Wp05_rowCode 9 := by decide +kernel

private theorem Wp05_row_10 : pack 32 (Wp05_digit 10)=Wp05_rowCode 10 := by decide +kernel

private theorem Wp05_row_11 : pack 32 (Wp05_digit 11)=Wp05_rowCode 11 := by decide +kernel

private theorem Wp05_row_12 : pack 32 (Wp05_digit 12)=Wp05_rowCode 12 := by decide +kernel

private theorem Wp05_row_13 : pack 32 (Wp05_digit 13)=Wp05_rowCode 13 := by decide +kernel

private theorem Wp05_row_14 : pack 32 (Wp05_digit 14)=Wp05_rowCode 14 := by decide +kernel

private theorem Wp05_row_15 : pack 32 (Wp05_digit 15)=Wp05_rowCode 15 := by decide +kernel

private theorem Wp05_row_16 : pack 32 (Wp05_digit 16)=Wp05_rowCode 16 := by decide +kernel

private theorem Wp05_row_17 : pack 32 (Wp05_digit 17)=Wp05_rowCode 17 := by decide +kernel

private theorem Wp05_row_18 : pack 32 (Wp05_digit 18)=Wp05_rowCode 18 := by decide +kernel

private theorem Wp05_row_19 : pack 32 (Wp05_digit 19)=Wp05_rowCode 19 := by decide +kernel

private theorem Wp05_row_20 : pack 32 (Wp05_digit 20)=Wp05_rowCode 20 := by decide +kernel

private theorem Wp05_row_21 : pack 32 (Wp05_digit 21)=Wp05_rowCode 21 := by decide +kernel

theorem Wp05_row_binding : ∀ i : Fin 22,pack 32 (Wp05_digit i)=Wp05_rowCode i := by
  intro i
  fin_cases i
  · exact Wp05_row_00
  · exact Wp05_row_01
  · exact Wp05_row_02
  · exact Wp05_row_03
  · exact Wp05_row_04
  · exact Wp05_row_05
  · exact Wp05_row_06
  · exact Wp05_row_07
  · exact Wp05_row_08
  · exact Wp05_row_09
  · exact Wp05_row_10
  · exact Wp05_row_11
  · exact Wp05_row_12
  · exact Wp05_row_13
  · exact Wp05_row_14
  · exact Wp05_row_15
  · exact Wp05_row_16
  · exact Wp05_row_17
  · exact Wp05_row_18
  · exact Wp05_row_19
  · exact Wp05_row_20
  · exact Wp05_row_21

private theorem Wp05_column_00 : reversePack 32 (fun j : Fin 22 => Wp05_digit j 0)=Wp05_columnCode 0 := by decide +kernel

private theorem Wp05_column_01 : reversePack 32 (fun j : Fin 22 => Wp05_digit j 1)=Wp05_columnCode 1 := by decide +kernel

private theorem Wp05_column_02 : reversePack 32 (fun j : Fin 22 => Wp05_digit j 2)=Wp05_columnCode 2 := by decide +kernel

private theorem Wp05_column_03 : reversePack 32 (fun j : Fin 22 => Wp05_digit j 3)=Wp05_columnCode 3 := by decide +kernel

private theorem Wp05_column_04 : reversePack 32 (fun j : Fin 22 => Wp05_digit j 4)=Wp05_columnCode 4 := by decide +kernel

private theorem Wp05_column_05 : reversePack 32 (fun j : Fin 22 => Wp05_digit j 5)=Wp05_columnCode 5 := by decide +kernel

private theorem Wp05_column_06 : reversePack 32 (fun j : Fin 22 => Wp05_digit j 6)=Wp05_columnCode 6 := by decide +kernel

private theorem Wp05_column_07 : reversePack 32 (fun j : Fin 22 => Wp05_digit j 7)=Wp05_columnCode 7 := by decide +kernel

private theorem Wp05_column_08 : reversePack 32 (fun j : Fin 22 => Wp05_digit j 8)=Wp05_columnCode 8 := by decide +kernel

private theorem Wp05_column_09 : reversePack 32 (fun j : Fin 22 => Wp05_digit j 9)=Wp05_columnCode 9 := by decide +kernel

private theorem Wp05_column_10 : reversePack 32 (fun j : Fin 22 => Wp05_digit j 10)=Wp05_columnCode 10 := by decide +kernel

private theorem Wp05_column_11 : reversePack 32 (fun j : Fin 22 => Wp05_digit j 11)=Wp05_columnCode 11 := by decide +kernel

private theorem Wp05_column_12 : reversePack 32 (fun j : Fin 22 => Wp05_digit j 12)=Wp05_columnCode 12 := by decide +kernel

private theorem Wp05_column_13 : reversePack 32 (fun j : Fin 22 => Wp05_digit j 13)=Wp05_columnCode 13 := by decide +kernel

private theorem Wp05_column_14 : reversePack 32 (fun j : Fin 22 => Wp05_digit j 14)=Wp05_columnCode 14 := by decide +kernel

private theorem Wp05_column_15 : reversePack 32 (fun j : Fin 22 => Wp05_digit j 15)=Wp05_columnCode 15 := by decide +kernel

private theorem Wp05_column_16 : reversePack 32 (fun j : Fin 22 => Wp05_digit j 16)=Wp05_columnCode 16 := by decide +kernel

private theorem Wp05_column_17 : reversePack 32 (fun j : Fin 22 => Wp05_digit j 17)=Wp05_columnCode 17 := by decide +kernel

private theorem Wp05_column_18 : reversePack 32 (fun j : Fin 22 => Wp05_digit j 18)=Wp05_columnCode 18 := by decide +kernel

private theorem Wp05_column_19 : reversePack 32 (fun j : Fin 22 => Wp05_digit j 19)=Wp05_columnCode 19 := by decide +kernel

private theorem Wp05_column_20 : reversePack 32 (fun j : Fin 22 => Wp05_digit j 20)=Wp05_columnCode 20 := by decide +kernel

private theorem Wp05_column_21 : reversePack 32 (fun j : Fin 22 => Wp05_digit j 21)=Wp05_columnCode 21 := by decide +kernel

theorem Wp05_column_binding : ∀ i : Fin 22,reversePack 32 (fun j : Fin 22 => Wp05_digit j i)=Wp05_columnCode i := by
  intro i
  fin_cases i
  · exact Wp05_column_00
  · exact Wp05_column_01
  · exact Wp05_column_02
  · exact Wp05_column_03
  · exact Wp05_column_04
  · exact Wp05_column_05
  · exact Wp05_column_06
  · exact Wp05_column_07
  · exact Wp05_column_08
  · exact Wp05_column_09
  · exact Wp05_column_10
  · exact Wp05_column_11
  · exact Wp05_column_12
  · exact Wp05_column_13
  · exact Wp05_column_14
  · exact Wp05_column_15
  · exact Wp05_column_16
  · exact Wp05_column_17
  · exact Wp05_column_18
  · exact Wp05_column_19
  · exact Wp05_column_20
  · exact Wp05_column_21

def Wp05_data : PackedData 22 2 32 where
  raw := Wp05_digit
  digit_lt := Wp05_bound
  rowCode := Wp05_rowCode
  columnCode := Wp05_columnCode
  row_binding := Wp05_row_binding
  column_binding := Wp05_column_binding

def binaryRowCode (i : ℕ) : ℕ :=
  match i with
  | 0 => 299141
  | 1 => 447109
  | 2 => 3981442
  | 3 => 299157
  | 4 => 2227375
  | 5 => 2292507
  | 6 => 528
  | 7 => 133476
  | 8 => 85184
  | 9 => 2217435
  | 10 => 367525
  | 11 => 2291096
  | 12 => 420337
  | 13 => 2627524
  | 14 => 2321593
  | 15 => 1788126
  | 16 => 28820
  | 17 => 1980031
  | 18 => 1104384
  | 19 => 294942
  | 20 => 3177124
  | 21 => 3404539
  | _ => 0

private theorem binary_row_00 : ∀ j : Fin 22,Wp05_digit 0 j=packedDigit 1 (binaryRowCode 0) j.val := by decide +kernel

private theorem binary_row_01 : ∀ j : Fin 22,Wp05_digit 1 j=packedDigit 1 (binaryRowCode 1) j.val := by decide +kernel

private theorem binary_row_02 : ∀ j : Fin 22,Wp05_digit 2 j=packedDigit 1 (binaryRowCode 2) j.val := by decide +kernel

private theorem binary_row_03 : ∀ j : Fin 22,Wp05_digit 3 j=packedDigit 1 (binaryRowCode 3) j.val := by decide +kernel

private theorem binary_row_04 : ∀ j : Fin 22,Wp05_digit 4 j=packedDigit 1 (binaryRowCode 4) j.val := by decide +kernel

private theorem binary_row_05 : ∀ j : Fin 22,Wp05_digit 5 j=packedDigit 1 (binaryRowCode 5) j.val := by decide +kernel

private theorem binary_row_06 : ∀ j : Fin 22,Wp05_digit 6 j=packedDigit 1 (binaryRowCode 6) j.val := by decide +kernel

private theorem binary_row_07 : ∀ j : Fin 22,Wp05_digit 7 j=packedDigit 1 (binaryRowCode 7) j.val := by decide +kernel

private theorem binary_row_08 : ∀ j : Fin 22,Wp05_digit 8 j=packedDigit 1 (binaryRowCode 8) j.val := by decide +kernel

private theorem binary_row_09 : ∀ j : Fin 22,Wp05_digit 9 j=packedDigit 1 (binaryRowCode 9) j.val := by decide +kernel

private theorem binary_row_10 : ∀ j : Fin 22,Wp05_digit 10 j=packedDigit 1 (binaryRowCode 10) j.val := by decide +kernel

private theorem binary_row_11 : ∀ j : Fin 22,Wp05_digit 11 j=packedDigit 1 (binaryRowCode 11) j.val := by decide +kernel

private theorem binary_row_12 : ∀ j : Fin 22,Wp05_digit 12 j=packedDigit 1 (binaryRowCode 12) j.val := by decide +kernel

private theorem binary_row_13 : ∀ j : Fin 22,Wp05_digit 13 j=packedDigit 1 (binaryRowCode 13) j.val := by decide +kernel

private theorem binary_row_14 : ∀ j : Fin 22,Wp05_digit 14 j=packedDigit 1 (binaryRowCode 14) j.val := by decide +kernel

private theorem binary_row_15 : ∀ j : Fin 22,Wp05_digit 15 j=packedDigit 1 (binaryRowCode 15) j.val := by decide +kernel

private theorem binary_row_16 : ∀ j : Fin 22,Wp05_digit 16 j=packedDigit 1 (binaryRowCode 16) j.val := by decide +kernel

private theorem binary_row_17 : ∀ j : Fin 22,Wp05_digit 17 j=packedDigit 1 (binaryRowCode 17) j.val := by decide +kernel

private theorem binary_row_18 : ∀ j : Fin 22,Wp05_digit 18 j=packedDigit 1 (binaryRowCode 18) j.val := by decide +kernel

private theorem binary_row_19 : ∀ j : Fin 22,Wp05_digit 19 j=packedDigit 1 (binaryRowCode 19) j.val := by decide +kernel

private theorem binary_row_20 : ∀ j : Fin 22,Wp05_digit 20 j=packedDigit 1 (binaryRowCode 20) j.val := by decide +kernel

private theorem binary_row_21 : ∀ j : Fin 22,Wp05_digit 21 j=packedDigit 1 (binaryRowCode 21) j.val := by decide +kernel

theorem binary_row_binding : ∀ i j : Fin 22,Wp05_digit i j=packedDigit 1 (binaryRowCode i.val) j.val := by
  intro i j
  fin_cases i
  · exact binary_row_00 j
  · exact binary_row_01 j
  · exact binary_row_02 j
  · exact binary_row_03 j
  · exact binary_row_04 j
  · exact binary_row_05 j
  · exact binary_row_06 j
  · exact binary_row_07 j
  · exact binary_row_08 j
  · exact binary_row_09 j
  · exact binary_row_10 j
  · exact binary_row_11 j
  · exact binary_row_12 j
  · exact binary_row_13 j
  · exact binary_row_14 j
  · exact binary_row_15 j
  · exact binary_row_16 j
  · exact binary_row_17 j
  · exact binary_row_18 j
  · exact binary_row_19 j
  · exact binary_row_20 j
  · exact binary_row_21 j

end SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoCaches13
