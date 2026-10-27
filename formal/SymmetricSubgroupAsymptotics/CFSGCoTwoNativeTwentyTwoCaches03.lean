import SymmetricSubgroupAsymptotics.MatrixKroneckerProductReflection
import Mathlib.Tactic.FinCases

/-! Fixed Co2 binary22 shared caches. Every digit and pack binding is kernel checked. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoCaches03
open MatrixKroneckerProductReflection MatrixKroneckerDotReflection
open MatrixNaturalRowDotReflection SmallNaturalMatrixProductReflection

def R05e02_lowColumnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 828872
  | 1 => 466203
  | 2 => 3183755
  | 3 => 3689464
  | 4 => 3736310
  | 5 => 3956937
  | 6 => 511094
  | 7 => 223023
  | 8 => 3758393
  | 9 => 3929088
  | 10 => 222127
  | 11 => 2048
  | 12 => 227247
  | 13 => 1008358
  | 14 => 401279
  | 15 => 255919
  | 16 => 3181622
  | 17 => 473296
  | 18 => 262144
  | 19 => 941951
  | 20 => 1466239
  | 21 => 2439376
  | _ => 0

def R05e02_rowCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1307264720446039102506466804768
  | 1 => 1307265929408752204184590222368
  | 2 => 1307265929408752204184590221312
  | 3 => 1307264720446039102506466837537
  | 4 => 41872123784521341322768740810784
  | 5 => 1307265929408752205284101881856
  | 6 => 41872122575632415195187507134465
  | 7 => 40564857930746547914537222308865
  | 8 => 1307264720446039102506433282081
  | 9 => 1307264720482932589554341806080
  | 10 => 1307265929371857625321635316769
  | 11 => 41872123784521377351565758726176
  | 12 => 41872122575596674664827470218272
  | 13 => 40564857930746547949755953053697
  | 14 => 1307264719302341005121920466944
  | 15 => 1246704751512771782247425
  | 16 => 40564857930746547950856505917472
  | 17 => 1307303406109160292873377153056
  | 18 => 41873360515671700575462405177377
  | 19 => 39614081294025693228109430785
  | 20 => 1267651809154049052409796264960
  | 21 => 40564820416229160498807595631616
  | _ => 0

def R05e02_columnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1237979035738381994495607808
  | 1 => 41833746433234013975828447133696
  | 2 => 41833707748751483314365980999713
  | 3 => 1277873588903682298529973281
  | 4 => 1307304614998085258235453899809
  | 5 => 40566057186302149712977846109217
  | 6 => 1307304613816377870745796116480
  | 7 => 41873323037791889852675002466304
  | 8 => 40566097041931568160198258328609
  | 9 => 36065116370764833
  | 10 => 41873323038972445444595394805760
  | 11 => 1125899906842624
  | 12 => 41873323038972481508576785858560
  | 13 => 1307265929371857591235735749632
  | 14 => 41873361761197050543716128817152
  | 15 => 41873323038972481473393487511552
  | 16 => 1307304576037446007754240032801
  | 17 => 38724585752313991988805632
  | 18 => 32768
  | 19 => 41873361761197050543750488556544
  | 20 => 41873361761197050543750488555552
  | 21 => 38724585752313991987757057
  | _ => 0

def R05e02_digit (i j : Fin 22) : ℕ := packedDigit 1 (R05e02_lowColumnCode j) i.val

private theorem R05e02_bound_00 : ∀ j : Fin 22,R05e02_digit 0 j<2 := by decide +kernel

private theorem R05e02_bound_01 : ∀ j : Fin 22,R05e02_digit 1 j<2 := by decide +kernel

private theorem R05e02_bound_02 : ∀ j : Fin 22,R05e02_digit 2 j<2 := by decide +kernel

private theorem R05e02_bound_03 : ∀ j : Fin 22,R05e02_digit 3 j<2 := by decide +kernel

private theorem R05e02_bound_04 : ∀ j : Fin 22,R05e02_digit 4 j<2 := by decide +kernel

private theorem R05e02_bound_05 : ∀ j : Fin 22,R05e02_digit 5 j<2 := by decide +kernel

private theorem R05e02_bound_06 : ∀ j : Fin 22,R05e02_digit 6 j<2 := by decide +kernel

private theorem R05e02_bound_07 : ∀ j : Fin 22,R05e02_digit 7 j<2 := by decide +kernel

private theorem R05e02_bound_08 : ∀ j : Fin 22,R05e02_digit 8 j<2 := by decide +kernel

private theorem R05e02_bound_09 : ∀ j : Fin 22,R05e02_digit 9 j<2 := by decide +kernel

private theorem R05e02_bound_10 : ∀ j : Fin 22,R05e02_digit 10 j<2 := by decide +kernel

private theorem R05e02_bound_11 : ∀ j : Fin 22,R05e02_digit 11 j<2 := by decide +kernel

private theorem R05e02_bound_12 : ∀ j : Fin 22,R05e02_digit 12 j<2 := by decide +kernel

private theorem R05e02_bound_13 : ∀ j : Fin 22,R05e02_digit 13 j<2 := by decide +kernel

private theorem R05e02_bound_14 : ∀ j : Fin 22,R05e02_digit 14 j<2 := by decide +kernel

private theorem R05e02_bound_15 : ∀ j : Fin 22,R05e02_digit 15 j<2 := by decide +kernel

private theorem R05e02_bound_16 : ∀ j : Fin 22,R05e02_digit 16 j<2 := by decide +kernel

private theorem R05e02_bound_17 : ∀ j : Fin 22,R05e02_digit 17 j<2 := by decide +kernel

private theorem R05e02_bound_18 : ∀ j : Fin 22,R05e02_digit 18 j<2 := by decide +kernel

private theorem R05e02_bound_19 : ∀ j : Fin 22,R05e02_digit 19 j<2 := by decide +kernel

private theorem R05e02_bound_20 : ∀ j : Fin 22,R05e02_digit 20 j<2 := by decide +kernel

private theorem R05e02_bound_21 : ∀ j : Fin 22,R05e02_digit 21 j<2 := by decide +kernel

theorem R05e02_bound : ∀ i j : Fin 22,R05e02_digit i j<2 := by
  intro i j
  fin_cases i
  · exact R05e02_bound_00 j
  · exact R05e02_bound_01 j
  · exact R05e02_bound_02 j
  · exact R05e02_bound_03 j
  · exact R05e02_bound_04 j
  · exact R05e02_bound_05 j
  · exact R05e02_bound_06 j
  · exact R05e02_bound_07 j
  · exact R05e02_bound_08 j
  · exact R05e02_bound_09 j
  · exact R05e02_bound_10 j
  · exact R05e02_bound_11 j
  · exact R05e02_bound_12 j
  · exact R05e02_bound_13 j
  · exact R05e02_bound_14 j
  · exact R05e02_bound_15 j
  · exact R05e02_bound_16 j
  · exact R05e02_bound_17 j
  · exact R05e02_bound_18 j
  · exact R05e02_bound_19 j
  · exact R05e02_bound_20 j
  · exact R05e02_bound_21 j

private theorem R05e02_row_00 : pack 32 (R05e02_digit 0)=R05e02_rowCode 0 := by decide +kernel

private theorem R05e02_row_01 : pack 32 (R05e02_digit 1)=R05e02_rowCode 1 := by decide +kernel

private theorem R05e02_row_02 : pack 32 (R05e02_digit 2)=R05e02_rowCode 2 := by decide +kernel

private theorem R05e02_row_03 : pack 32 (R05e02_digit 3)=R05e02_rowCode 3 := by decide +kernel

private theorem R05e02_row_04 : pack 32 (R05e02_digit 4)=R05e02_rowCode 4 := by decide +kernel

private theorem R05e02_row_05 : pack 32 (R05e02_digit 5)=R05e02_rowCode 5 := by decide +kernel

private theorem R05e02_row_06 : pack 32 (R05e02_digit 6)=R05e02_rowCode 6 := by decide +kernel

private theorem R05e02_row_07 : pack 32 (R05e02_digit 7)=R05e02_rowCode 7 := by decide +kernel

private theorem R05e02_row_08 : pack 32 (R05e02_digit 8)=R05e02_rowCode 8 := by decide +kernel

private theorem R05e02_row_09 : pack 32 (R05e02_digit 9)=R05e02_rowCode 9 := by decide +kernel

private theorem R05e02_row_10 : pack 32 (R05e02_digit 10)=R05e02_rowCode 10 := by decide +kernel

private theorem R05e02_row_11 : pack 32 (R05e02_digit 11)=R05e02_rowCode 11 := by decide +kernel

private theorem R05e02_row_12 : pack 32 (R05e02_digit 12)=R05e02_rowCode 12 := by decide +kernel

private theorem R05e02_row_13 : pack 32 (R05e02_digit 13)=R05e02_rowCode 13 := by decide +kernel

private theorem R05e02_row_14 : pack 32 (R05e02_digit 14)=R05e02_rowCode 14 := by decide +kernel

private theorem R05e02_row_15 : pack 32 (R05e02_digit 15)=R05e02_rowCode 15 := by decide +kernel

private theorem R05e02_row_16 : pack 32 (R05e02_digit 16)=R05e02_rowCode 16 := by decide +kernel

private theorem R05e02_row_17 : pack 32 (R05e02_digit 17)=R05e02_rowCode 17 := by decide +kernel

private theorem R05e02_row_18 : pack 32 (R05e02_digit 18)=R05e02_rowCode 18 := by decide +kernel

private theorem R05e02_row_19 : pack 32 (R05e02_digit 19)=R05e02_rowCode 19 := by decide +kernel

private theorem R05e02_row_20 : pack 32 (R05e02_digit 20)=R05e02_rowCode 20 := by decide +kernel

private theorem R05e02_row_21 : pack 32 (R05e02_digit 21)=R05e02_rowCode 21 := by decide +kernel

theorem R05e02_row_binding : ∀ i : Fin 22,pack 32 (R05e02_digit i)=R05e02_rowCode i := by
  intro i
  fin_cases i
  · exact R05e02_row_00
  · exact R05e02_row_01
  · exact R05e02_row_02
  · exact R05e02_row_03
  · exact R05e02_row_04
  · exact R05e02_row_05
  · exact R05e02_row_06
  · exact R05e02_row_07
  · exact R05e02_row_08
  · exact R05e02_row_09
  · exact R05e02_row_10
  · exact R05e02_row_11
  · exact R05e02_row_12
  · exact R05e02_row_13
  · exact R05e02_row_14
  · exact R05e02_row_15
  · exact R05e02_row_16
  · exact R05e02_row_17
  · exact R05e02_row_18
  · exact R05e02_row_19
  · exact R05e02_row_20
  · exact R05e02_row_21

private theorem R05e02_column_00 : reversePack 32 (fun j : Fin 22 => R05e02_digit j 0)=R05e02_columnCode 0 := by decide +kernel

private theorem R05e02_column_01 : reversePack 32 (fun j : Fin 22 => R05e02_digit j 1)=R05e02_columnCode 1 := by decide +kernel

private theorem R05e02_column_02 : reversePack 32 (fun j : Fin 22 => R05e02_digit j 2)=R05e02_columnCode 2 := by decide +kernel

private theorem R05e02_column_03 : reversePack 32 (fun j : Fin 22 => R05e02_digit j 3)=R05e02_columnCode 3 := by decide +kernel

private theorem R05e02_column_04 : reversePack 32 (fun j : Fin 22 => R05e02_digit j 4)=R05e02_columnCode 4 := by decide +kernel

private theorem R05e02_column_05 : reversePack 32 (fun j : Fin 22 => R05e02_digit j 5)=R05e02_columnCode 5 := by decide +kernel

private theorem R05e02_column_06 : reversePack 32 (fun j : Fin 22 => R05e02_digit j 6)=R05e02_columnCode 6 := by decide +kernel

private theorem R05e02_column_07 : reversePack 32 (fun j : Fin 22 => R05e02_digit j 7)=R05e02_columnCode 7 := by decide +kernel

private theorem R05e02_column_08 : reversePack 32 (fun j : Fin 22 => R05e02_digit j 8)=R05e02_columnCode 8 := by decide +kernel

private theorem R05e02_column_09 : reversePack 32 (fun j : Fin 22 => R05e02_digit j 9)=R05e02_columnCode 9 := by decide +kernel

private theorem R05e02_column_10 : reversePack 32 (fun j : Fin 22 => R05e02_digit j 10)=R05e02_columnCode 10 := by decide +kernel

private theorem R05e02_column_11 : reversePack 32 (fun j : Fin 22 => R05e02_digit j 11)=R05e02_columnCode 11 := by decide +kernel

private theorem R05e02_column_12 : reversePack 32 (fun j : Fin 22 => R05e02_digit j 12)=R05e02_columnCode 12 := by decide +kernel

private theorem R05e02_column_13 : reversePack 32 (fun j : Fin 22 => R05e02_digit j 13)=R05e02_columnCode 13 := by decide +kernel

private theorem R05e02_column_14 : reversePack 32 (fun j : Fin 22 => R05e02_digit j 14)=R05e02_columnCode 14 := by decide +kernel

private theorem R05e02_column_15 : reversePack 32 (fun j : Fin 22 => R05e02_digit j 15)=R05e02_columnCode 15 := by decide +kernel

private theorem R05e02_column_16 : reversePack 32 (fun j : Fin 22 => R05e02_digit j 16)=R05e02_columnCode 16 := by decide +kernel

private theorem R05e02_column_17 : reversePack 32 (fun j : Fin 22 => R05e02_digit j 17)=R05e02_columnCode 17 := by decide +kernel

private theorem R05e02_column_18 : reversePack 32 (fun j : Fin 22 => R05e02_digit j 18)=R05e02_columnCode 18 := by decide +kernel

private theorem R05e02_column_19 : reversePack 32 (fun j : Fin 22 => R05e02_digit j 19)=R05e02_columnCode 19 := by decide +kernel

private theorem R05e02_column_20 : reversePack 32 (fun j : Fin 22 => R05e02_digit j 20)=R05e02_columnCode 20 := by decide +kernel

private theorem R05e02_column_21 : reversePack 32 (fun j : Fin 22 => R05e02_digit j 21)=R05e02_columnCode 21 := by decide +kernel

theorem R05e02_column_binding : ∀ i : Fin 22,reversePack 32 (fun j : Fin 22 => R05e02_digit j i)=R05e02_columnCode i := by
  intro i
  fin_cases i
  · exact R05e02_column_00
  · exact R05e02_column_01
  · exact R05e02_column_02
  · exact R05e02_column_03
  · exact R05e02_column_04
  · exact R05e02_column_05
  · exact R05e02_column_06
  · exact R05e02_column_07
  · exact R05e02_column_08
  · exact R05e02_column_09
  · exact R05e02_column_10
  · exact R05e02_column_11
  · exact R05e02_column_12
  · exact R05e02_column_13
  · exact R05e02_column_14
  · exact R05e02_column_15
  · exact R05e02_column_16
  · exact R05e02_column_17
  · exact R05e02_column_18
  · exact R05e02_column_19
  · exact R05e02_column_20
  · exact R05e02_column_21

def R05e02_data : PackedData 22 2 32 where
  raw := R05e02_digit
  digit_lt := R05e02_bound
  rowCode := R05e02_rowCode
  columnCode := R05e02_columnCode
  row_binding := R05e02_row_binding
  column_binding := R05e02_column_binding

def R06p03_lowColumnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 3568010
  | 1 => 393899
  | 2 => 4079159
  | 3 => 972836
  | 4 => 3449511
  | 5 => 445110
  | 6 => 1914900
  | 7 => 3555489
  | 8 => 787110
  | 9 => 580278
  | 10 => 2766864
  | 11 => 967334
  | 12 => 3340982
  | 13 => 2814496
  | 14 => 3072674
  | 15 => 3574340
  | 16 => 3571716
  | 17 => 559796
  | 18 => 1849910
  | 19 => 281140
  | 20 => 3416064
  | 21 => 1231408
  | _ => 0

def R06p03_rowCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 34360788000
  | 1 => 1237941221065987577854559265
  | 2 => 40891953628585681378216018944
  | 3 => 33
  | 4 => 40605709914227140147689757344768
  | 5 => 40605709915444660160584498578464
  | 6 => 37778931862957161709568
  | 7 => 38686808008275470905770017
  | 8 => 1
  | 9 => 40605709953223592023507300516896
  | 10 => 1024
  | 11 => 40605709952006072010646919087104
  | 12 => 1237940077332951012277781505
  | 13 => 1268888541486153938042021217281
  | 14 => 40604433289779147111076496179201
  | 15 => 40564859140852994087965292527616
  | 16 => 1073741824
  | 17 => 40564820455226767510581595374625
  | 18 => 1308503869410026078804120732705
  | 19 => 1276626883035348255203427328
  | 20 => 41833708994276760028792482694145
  | 21 => 1267651848151620035386744505345
  | _ => 0

def R06p03_columnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1268888541484999926954677272609
  | 1 => 41833708957678419786517298839552
  | 2 => 41872123783341939813436160508961
  | 3 => 39615290182952944545660175360
  | 4 => 41872085098896266576139756011553
  | 5 => 1307304577219154521213600038912
  | 6 => 39652766883360999114186720288
  | 7 => 40564820417409752083275449401377
  | 8 => 1307265891592925727144668070912
  | 9 => 1307304577219154556397971047424
  | 10 => 38685626228830317382206465
  | 11 => 1307265891592925727180102599680
  | 12 => 1307304577219154557497483722785
  | 13 => 1208926972572453099799553
  | 14 => 1267651810335793559482842252289
  | 15 => 39614119037218079159522197537
  | 16 => 39614081257132168797846798369
  | 17 => 39653976990925119682536014848
  | 18 => 1307304576038562936744637924384
  | 19 => 39653975810333498998410739712
  | 20 => 1099511660577
  | 21 => 39894553201330202713522208
  | _ => 0

def R06p03_digit (i j : Fin 22) : ℕ := packedDigit 1 (R06p03_lowColumnCode j) i.val

private theorem R06p03_bound_00 : ∀ j : Fin 22,R06p03_digit 0 j<2 := by decide +kernel

private theorem R06p03_bound_01 : ∀ j : Fin 22,R06p03_digit 1 j<2 := by decide +kernel

private theorem R06p03_bound_02 : ∀ j : Fin 22,R06p03_digit 2 j<2 := by decide +kernel

private theorem R06p03_bound_03 : ∀ j : Fin 22,R06p03_digit 3 j<2 := by decide +kernel

private theorem R06p03_bound_04 : ∀ j : Fin 22,R06p03_digit 4 j<2 := by decide +kernel

private theorem R06p03_bound_05 : ∀ j : Fin 22,R06p03_digit 5 j<2 := by decide +kernel

private theorem R06p03_bound_06 : ∀ j : Fin 22,R06p03_digit 6 j<2 := by decide +kernel

private theorem R06p03_bound_07 : ∀ j : Fin 22,R06p03_digit 7 j<2 := by decide +kernel

private theorem R06p03_bound_08 : ∀ j : Fin 22,R06p03_digit 8 j<2 := by decide +kernel

private theorem R06p03_bound_09 : ∀ j : Fin 22,R06p03_digit 9 j<2 := by decide +kernel

private theorem R06p03_bound_10 : ∀ j : Fin 22,R06p03_digit 10 j<2 := by decide +kernel

private theorem R06p03_bound_11 : ∀ j : Fin 22,R06p03_digit 11 j<2 := by decide +kernel

private theorem R06p03_bound_12 : ∀ j : Fin 22,R06p03_digit 12 j<2 := by decide +kernel

private theorem R06p03_bound_13 : ∀ j : Fin 22,R06p03_digit 13 j<2 := by decide +kernel

private theorem R06p03_bound_14 : ∀ j : Fin 22,R06p03_digit 14 j<2 := by decide +kernel

private theorem R06p03_bound_15 : ∀ j : Fin 22,R06p03_digit 15 j<2 := by decide +kernel

private theorem R06p03_bound_16 : ∀ j : Fin 22,R06p03_digit 16 j<2 := by decide +kernel

private theorem R06p03_bound_17 : ∀ j : Fin 22,R06p03_digit 17 j<2 := by decide +kernel

private theorem R06p03_bound_18 : ∀ j : Fin 22,R06p03_digit 18 j<2 := by decide +kernel

private theorem R06p03_bound_19 : ∀ j : Fin 22,R06p03_digit 19 j<2 := by decide +kernel

private theorem R06p03_bound_20 : ∀ j : Fin 22,R06p03_digit 20 j<2 := by decide +kernel

private theorem R06p03_bound_21 : ∀ j : Fin 22,R06p03_digit 21 j<2 := by decide +kernel

theorem R06p03_bound : ∀ i j : Fin 22,R06p03_digit i j<2 := by
  intro i j
  fin_cases i
  · exact R06p03_bound_00 j
  · exact R06p03_bound_01 j
  · exact R06p03_bound_02 j
  · exact R06p03_bound_03 j
  · exact R06p03_bound_04 j
  · exact R06p03_bound_05 j
  · exact R06p03_bound_06 j
  · exact R06p03_bound_07 j
  · exact R06p03_bound_08 j
  · exact R06p03_bound_09 j
  · exact R06p03_bound_10 j
  · exact R06p03_bound_11 j
  · exact R06p03_bound_12 j
  · exact R06p03_bound_13 j
  · exact R06p03_bound_14 j
  · exact R06p03_bound_15 j
  · exact R06p03_bound_16 j
  · exact R06p03_bound_17 j
  · exact R06p03_bound_18 j
  · exact R06p03_bound_19 j
  · exact R06p03_bound_20 j
  · exact R06p03_bound_21 j

private theorem R06p03_row_00 : pack 32 (R06p03_digit 0)=R06p03_rowCode 0 := by decide +kernel

private theorem R06p03_row_01 : pack 32 (R06p03_digit 1)=R06p03_rowCode 1 := by decide +kernel

private theorem R06p03_row_02 : pack 32 (R06p03_digit 2)=R06p03_rowCode 2 := by decide +kernel

private theorem R06p03_row_03 : pack 32 (R06p03_digit 3)=R06p03_rowCode 3 := by decide +kernel

private theorem R06p03_row_04 : pack 32 (R06p03_digit 4)=R06p03_rowCode 4 := by decide +kernel

private theorem R06p03_row_05 : pack 32 (R06p03_digit 5)=R06p03_rowCode 5 := by decide +kernel

private theorem R06p03_row_06 : pack 32 (R06p03_digit 6)=R06p03_rowCode 6 := by decide +kernel

private theorem R06p03_row_07 : pack 32 (R06p03_digit 7)=R06p03_rowCode 7 := by decide +kernel

private theorem R06p03_row_08 : pack 32 (R06p03_digit 8)=R06p03_rowCode 8 := by decide +kernel

private theorem R06p03_row_09 : pack 32 (R06p03_digit 9)=R06p03_rowCode 9 := by decide +kernel

private theorem R06p03_row_10 : pack 32 (R06p03_digit 10)=R06p03_rowCode 10 := by decide +kernel

private theorem R06p03_row_11 : pack 32 (R06p03_digit 11)=R06p03_rowCode 11 := by decide +kernel

private theorem R06p03_row_12 : pack 32 (R06p03_digit 12)=R06p03_rowCode 12 := by decide +kernel

private theorem R06p03_row_13 : pack 32 (R06p03_digit 13)=R06p03_rowCode 13 := by decide +kernel

private theorem R06p03_row_14 : pack 32 (R06p03_digit 14)=R06p03_rowCode 14 := by decide +kernel

private theorem R06p03_row_15 : pack 32 (R06p03_digit 15)=R06p03_rowCode 15 := by decide +kernel

private theorem R06p03_row_16 : pack 32 (R06p03_digit 16)=R06p03_rowCode 16 := by decide +kernel

private theorem R06p03_row_17 : pack 32 (R06p03_digit 17)=R06p03_rowCode 17 := by decide +kernel

private theorem R06p03_row_18 : pack 32 (R06p03_digit 18)=R06p03_rowCode 18 := by decide +kernel

private theorem R06p03_row_19 : pack 32 (R06p03_digit 19)=R06p03_rowCode 19 := by decide +kernel

private theorem R06p03_row_20 : pack 32 (R06p03_digit 20)=R06p03_rowCode 20 := by decide +kernel

private theorem R06p03_row_21 : pack 32 (R06p03_digit 21)=R06p03_rowCode 21 := by decide +kernel

theorem R06p03_row_binding : ∀ i : Fin 22,pack 32 (R06p03_digit i)=R06p03_rowCode i := by
  intro i
  fin_cases i
  · exact R06p03_row_00
  · exact R06p03_row_01
  · exact R06p03_row_02
  · exact R06p03_row_03
  · exact R06p03_row_04
  · exact R06p03_row_05
  · exact R06p03_row_06
  · exact R06p03_row_07
  · exact R06p03_row_08
  · exact R06p03_row_09
  · exact R06p03_row_10
  · exact R06p03_row_11
  · exact R06p03_row_12
  · exact R06p03_row_13
  · exact R06p03_row_14
  · exact R06p03_row_15
  · exact R06p03_row_16
  · exact R06p03_row_17
  · exact R06p03_row_18
  · exact R06p03_row_19
  · exact R06p03_row_20
  · exact R06p03_row_21

private theorem R06p03_column_00 : reversePack 32 (fun j : Fin 22 => R06p03_digit j 0)=R06p03_columnCode 0 := by decide +kernel

private theorem R06p03_column_01 : reversePack 32 (fun j : Fin 22 => R06p03_digit j 1)=R06p03_columnCode 1 := by decide +kernel

private theorem R06p03_column_02 : reversePack 32 (fun j : Fin 22 => R06p03_digit j 2)=R06p03_columnCode 2 := by decide +kernel

private theorem R06p03_column_03 : reversePack 32 (fun j : Fin 22 => R06p03_digit j 3)=R06p03_columnCode 3 := by decide +kernel

private theorem R06p03_column_04 : reversePack 32 (fun j : Fin 22 => R06p03_digit j 4)=R06p03_columnCode 4 := by decide +kernel

private theorem R06p03_column_05 : reversePack 32 (fun j : Fin 22 => R06p03_digit j 5)=R06p03_columnCode 5 := by decide +kernel

private theorem R06p03_column_06 : reversePack 32 (fun j : Fin 22 => R06p03_digit j 6)=R06p03_columnCode 6 := by decide +kernel

private theorem R06p03_column_07 : reversePack 32 (fun j : Fin 22 => R06p03_digit j 7)=R06p03_columnCode 7 := by decide +kernel

private theorem R06p03_column_08 : reversePack 32 (fun j : Fin 22 => R06p03_digit j 8)=R06p03_columnCode 8 := by decide +kernel

private theorem R06p03_column_09 : reversePack 32 (fun j : Fin 22 => R06p03_digit j 9)=R06p03_columnCode 9 := by decide +kernel

private theorem R06p03_column_10 : reversePack 32 (fun j : Fin 22 => R06p03_digit j 10)=R06p03_columnCode 10 := by decide +kernel

private theorem R06p03_column_11 : reversePack 32 (fun j : Fin 22 => R06p03_digit j 11)=R06p03_columnCode 11 := by decide +kernel

private theorem R06p03_column_12 : reversePack 32 (fun j : Fin 22 => R06p03_digit j 12)=R06p03_columnCode 12 := by decide +kernel

private theorem R06p03_column_13 : reversePack 32 (fun j : Fin 22 => R06p03_digit j 13)=R06p03_columnCode 13 := by decide +kernel

private theorem R06p03_column_14 : reversePack 32 (fun j : Fin 22 => R06p03_digit j 14)=R06p03_columnCode 14 := by decide +kernel

private theorem R06p03_column_15 : reversePack 32 (fun j : Fin 22 => R06p03_digit j 15)=R06p03_columnCode 15 := by decide +kernel

private theorem R06p03_column_16 : reversePack 32 (fun j : Fin 22 => R06p03_digit j 16)=R06p03_columnCode 16 := by decide +kernel

private theorem R06p03_column_17 : reversePack 32 (fun j : Fin 22 => R06p03_digit j 17)=R06p03_columnCode 17 := by decide +kernel

private theorem R06p03_column_18 : reversePack 32 (fun j : Fin 22 => R06p03_digit j 18)=R06p03_columnCode 18 := by decide +kernel

private theorem R06p03_column_19 : reversePack 32 (fun j : Fin 22 => R06p03_digit j 19)=R06p03_columnCode 19 := by decide +kernel

private theorem R06p03_column_20 : reversePack 32 (fun j : Fin 22 => R06p03_digit j 20)=R06p03_columnCode 20 := by decide +kernel

private theorem R06p03_column_21 : reversePack 32 (fun j : Fin 22 => R06p03_digit j 21)=R06p03_columnCode 21 := by decide +kernel

theorem R06p03_column_binding : ∀ i : Fin 22,reversePack 32 (fun j : Fin 22 => R06p03_digit j i)=R06p03_columnCode i := by
  intro i
  fin_cases i
  · exact R06p03_column_00
  · exact R06p03_column_01
  · exact R06p03_column_02
  · exact R06p03_column_03
  · exact R06p03_column_04
  · exact R06p03_column_05
  · exact R06p03_column_06
  · exact R06p03_column_07
  · exact R06p03_column_08
  · exact R06p03_column_09
  · exact R06p03_column_10
  · exact R06p03_column_11
  · exact R06p03_column_12
  · exact R06p03_column_13
  · exact R06p03_column_14
  · exact R06p03_column_15
  · exact R06p03_column_16
  · exact R06p03_column_17
  · exact R06p03_column_18
  · exact R06p03_column_19
  · exact R06p03_column_20
  · exact R06p03_column_21

def R06p03_data : PackedData 22 2 32 where
  raw := R06p03_digit
  digit_lt := R06p03_bound
  rowCode := R06p03_rowCode
  columnCode := R06p03_columnCode
  row_binding := R06p03_row_binding
  column_binding := R06p03_column_binding

def R06p04_lowColumnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 3338383
  | 1 => 164782
  | 2 => 3864612
  | 3 => 663095
  | 4 => 2953861
  | 5 => 2525239
  | 6 => 297014
  | 7 => 3555489
  | 8 => 2900007
  | 9 => 580278
  | 10 => 2766864
  | 11 => 967334
  | 12 => 3340982
  | 13 => 806914
  | 14 => 3072674
  | 15 => 1112758
  | 16 => 1057318
  | 17 => 559796
  | 18 => 1849910
  | 19 => 2243270
  | 20 => 3416064
  | 21 => 1231408
  | _ => 0

def R06p04_rowCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1133906001921
  | 1 => 40853269219843122109454778401
  | 2 => 40891953628585681378216018977
  | 3 => 33
  | 4 => 40566095870748939841850147110912
  | 5 => 40566097080855385981227716609056
  | 6 => 39614081257132168796771975168
  | 7 => 39652805844072306125294272545
  | 8 => 32
  | 9 => 40605711162112518148889510969376
  | 10 => 32768
  | 11 => 40605709952006072010646919087104
  | 12 => 40852059113396982765138772993
  | 13 => 1308503869411144096276635714561
  | 14 => 40564819246300946806336363955201
  | 15 => 40564857931890280985189771379745
  | 16 => 1048576
  | 17 => 40604433289742254713644611830817
  | 18 => 1268888541485035920568431411200
  | 19 => 1276626883035348254130734080
  | 20 => 41833708994276760028791407903745
  | 21 => 1307264682667107239549306143745
  | _ => 0

def R06p04_columnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 41873321830008579455499606425633
  | 1 => 1308503831669104595568061054976
  | 2 => 39615290182952945645171770401
  | 3 => 41872123783341939812336648848384
  | 4 => 40604433289742217594097698374657
  | 5 => 41872123783340750826851724722177
  | 6 => 1307304576037409978957221101568
  | 7 => 40564820417409752083275449401377
  | 8 => 41872085097714522032851512230913
  | 9 => 1307304577219154556397971047424
  | 10 => 38685626228830317382206465
  | 11 => 1307265891592925727180102599680
  | 12 => 1307304577219154557497483722785
  | 13 => 1267650600228229436715435066368
  | 14 => 1267651810335793559482842252289
  | 15 => 1307304577219154557497482674208
  | 16 => 1307265890412334107526768361504
  | 17 => 39653976990925119682536014848
  | 18 => 1307304576038562936744637924384
  | 19 => 1307264720446039137656446648321
  | 20 => 1099511660577
  | 21 => 39894553201330202713522208
  | _ => 0

def R06p04_digit (i j : Fin 22) : ℕ := packedDigit 1 (R06p04_lowColumnCode j) i.val

private theorem R06p04_bound_00 : ∀ j : Fin 22,R06p04_digit 0 j<2 := by decide +kernel

private theorem R06p04_bound_01 : ∀ j : Fin 22,R06p04_digit 1 j<2 := by decide +kernel

private theorem R06p04_bound_02 : ∀ j : Fin 22,R06p04_digit 2 j<2 := by decide +kernel

private theorem R06p04_bound_03 : ∀ j : Fin 22,R06p04_digit 3 j<2 := by decide +kernel

private theorem R06p04_bound_04 : ∀ j : Fin 22,R06p04_digit 4 j<2 := by decide +kernel

private theorem R06p04_bound_05 : ∀ j : Fin 22,R06p04_digit 5 j<2 := by decide +kernel

private theorem R06p04_bound_06 : ∀ j : Fin 22,R06p04_digit 6 j<2 := by decide +kernel

private theorem R06p04_bound_07 : ∀ j : Fin 22,R06p04_digit 7 j<2 := by decide +kernel

private theorem R06p04_bound_08 : ∀ j : Fin 22,R06p04_digit 8 j<2 := by decide +kernel

private theorem R06p04_bound_09 : ∀ j : Fin 22,R06p04_digit 9 j<2 := by decide +kernel

private theorem R06p04_bound_10 : ∀ j : Fin 22,R06p04_digit 10 j<2 := by decide +kernel

private theorem R06p04_bound_11 : ∀ j : Fin 22,R06p04_digit 11 j<2 := by decide +kernel

private theorem R06p04_bound_12 : ∀ j : Fin 22,R06p04_digit 12 j<2 := by decide +kernel

private theorem R06p04_bound_13 : ∀ j : Fin 22,R06p04_digit 13 j<2 := by decide +kernel

private theorem R06p04_bound_14 : ∀ j : Fin 22,R06p04_digit 14 j<2 := by decide +kernel

private theorem R06p04_bound_15 : ∀ j : Fin 22,R06p04_digit 15 j<2 := by decide +kernel

private theorem R06p04_bound_16 : ∀ j : Fin 22,R06p04_digit 16 j<2 := by decide +kernel

private theorem R06p04_bound_17 : ∀ j : Fin 22,R06p04_digit 17 j<2 := by decide +kernel

private theorem R06p04_bound_18 : ∀ j : Fin 22,R06p04_digit 18 j<2 := by decide +kernel

private theorem R06p04_bound_19 : ∀ j : Fin 22,R06p04_digit 19 j<2 := by decide +kernel

private theorem R06p04_bound_20 : ∀ j : Fin 22,R06p04_digit 20 j<2 := by decide +kernel

private theorem R06p04_bound_21 : ∀ j : Fin 22,R06p04_digit 21 j<2 := by decide +kernel

theorem R06p04_bound : ∀ i j : Fin 22,R06p04_digit i j<2 := by
  intro i j
  fin_cases i
  · exact R06p04_bound_00 j
  · exact R06p04_bound_01 j
  · exact R06p04_bound_02 j
  · exact R06p04_bound_03 j
  · exact R06p04_bound_04 j
  · exact R06p04_bound_05 j
  · exact R06p04_bound_06 j
  · exact R06p04_bound_07 j
  · exact R06p04_bound_08 j
  · exact R06p04_bound_09 j
  · exact R06p04_bound_10 j
  · exact R06p04_bound_11 j
  · exact R06p04_bound_12 j
  · exact R06p04_bound_13 j
  · exact R06p04_bound_14 j
  · exact R06p04_bound_15 j
  · exact R06p04_bound_16 j
  · exact R06p04_bound_17 j
  · exact R06p04_bound_18 j
  · exact R06p04_bound_19 j
  · exact R06p04_bound_20 j
  · exact R06p04_bound_21 j

private theorem R06p04_row_00 : pack 32 (R06p04_digit 0)=R06p04_rowCode 0 := by decide +kernel

private theorem R06p04_row_01 : pack 32 (R06p04_digit 1)=R06p04_rowCode 1 := by decide +kernel

private theorem R06p04_row_02 : pack 32 (R06p04_digit 2)=R06p04_rowCode 2 := by decide +kernel

private theorem R06p04_row_03 : pack 32 (R06p04_digit 3)=R06p04_rowCode 3 := by decide +kernel

private theorem R06p04_row_04 : pack 32 (R06p04_digit 4)=R06p04_rowCode 4 := by decide +kernel

private theorem R06p04_row_05 : pack 32 (R06p04_digit 5)=R06p04_rowCode 5 := by decide +kernel

private theorem R06p04_row_06 : pack 32 (R06p04_digit 6)=R06p04_rowCode 6 := by decide +kernel

private theorem R06p04_row_07 : pack 32 (R06p04_digit 7)=R06p04_rowCode 7 := by decide +kernel

private theorem R06p04_row_08 : pack 32 (R06p04_digit 8)=R06p04_rowCode 8 := by decide +kernel

private theorem R06p04_row_09 : pack 32 (R06p04_digit 9)=R06p04_rowCode 9 := by decide +kernel

private theorem R06p04_row_10 : pack 32 (R06p04_digit 10)=R06p04_rowCode 10 := by decide +kernel

private theorem R06p04_row_11 : pack 32 (R06p04_digit 11)=R06p04_rowCode 11 := by decide +kernel

private theorem R06p04_row_12 : pack 32 (R06p04_digit 12)=R06p04_rowCode 12 := by decide +kernel

private theorem R06p04_row_13 : pack 32 (R06p04_digit 13)=R06p04_rowCode 13 := by decide +kernel

private theorem R06p04_row_14 : pack 32 (R06p04_digit 14)=R06p04_rowCode 14 := by decide +kernel

private theorem R06p04_row_15 : pack 32 (R06p04_digit 15)=R06p04_rowCode 15 := by decide +kernel

private theorem R06p04_row_16 : pack 32 (R06p04_digit 16)=R06p04_rowCode 16 := by decide +kernel

private theorem R06p04_row_17 : pack 32 (R06p04_digit 17)=R06p04_rowCode 17 := by decide +kernel

private theorem R06p04_row_18 : pack 32 (R06p04_digit 18)=R06p04_rowCode 18 := by decide +kernel

private theorem R06p04_row_19 : pack 32 (R06p04_digit 19)=R06p04_rowCode 19 := by decide +kernel

private theorem R06p04_row_20 : pack 32 (R06p04_digit 20)=R06p04_rowCode 20 := by decide +kernel

private theorem R06p04_row_21 : pack 32 (R06p04_digit 21)=R06p04_rowCode 21 := by decide +kernel

theorem R06p04_row_binding : ∀ i : Fin 22,pack 32 (R06p04_digit i)=R06p04_rowCode i := by
  intro i
  fin_cases i
  · exact R06p04_row_00
  · exact R06p04_row_01
  · exact R06p04_row_02
  · exact R06p04_row_03
  · exact R06p04_row_04
  · exact R06p04_row_05
  · exact R06p04_row_06
  · exact R06p04_row_07
  · exact R06p04_row_08
  · exact R06p04_row_09
  · exact R06p04_row_10
  · exact R06p04_row_11
  · exact R06p04_row_12
  · exact R06p04_row_13
  · exact R06p04_row_14
  · exact R06p04_row_15
  · exact R06p04_row_16
  · exact R06p04_row_17
  · exact R06p04_row_18
  · exact R06p04_row_19
  · exact R06p04_row_20
  · exact R06p04_row_21

private theorem R06p04_column_00 : reversePack 32 (fun j : Fin 22 => R06p04_digit j 0)=R06p04_columnCode 0 := by decide +kernel

private theorem R06p04_column_01 : reversePack 32 (fun j : Fin 22 => R06p04_digit j 1)=R06p04_columnCode 1 := by decide +kernel

private theorem R06p04_column_02 : reversePack 32 (fun j : Fin 22 => R06p04_digit j 2)=R06p04_columnCode 2 := by decide +kernel

private theorem R06p04_column_03 : reversePack 32 (fun j : Fin 22 => R06p04_digit j 3)=R06p04_columnCode 3 := by decide +kernel

private theorem R06p04_column_04 : reversePack 32 (fun j : Fin 22 => R06p04_digit j 4)=R06p04_columnCode 4 := by decide +kernel

private theorem R06p04_column_05 : reversePack 32 (fun j : Fin 22 => R06p04_digit j 5)=R06p04_columnCode 5 := by decide +kernel

private theorem R06p04_column_06 : reversePack 32 (fun j : Fin 22 => R06p04_digit j 6)=R06p04_columnCode 6 := by decide +kernel

private theorem R06p04_column_07 : reversePack 32 (fun j : Fin 22 => R06p04_digit j 7)=R06p04_columnCode 7 := by decide +kernel

private theorem R06p04_column_08 : reversePack 32 (fun j : Fin 22 => R06p04_digit j 8)=R06p04_columnCode 8 := by decide +kernel

private theorem R06p04_column_09 : reversePack 32 (fun j : Fin 22 => R06p04_digit j 9)=R06p04_columnCode 9 := by decide +kernel

private theorem R06p04_column_10 : reversePack 32 (fun j : Fin 22 => R06p04_digit j 10)=R06p04_columnCode 10 := by decide +kernel

private theorem R06p04_column_11 : reversePack 32 (fun j : Fin 22 => R06p04_digit j 11)=R06p04_columnCode 11 := by decide +kernel

private theorem R06p04_column_12 : reversePack 32 (fun j : Fin 22 => R06p04_digit j 12)=R06p04_columnCode 12 := by decide +kernel

private theorem R06p04_column_13 : reversePack 32 (fun j : Fin 22 => R06p04_digit j 13)=R06p04_columnCode 13 := by decide +kernel

private theorem R06p04_column_14 : reversePack 32 (fun j : Fin 22 => R06p04_digit j 14)=R06p04_columnCode 14 := by decide +kernel

private theorem R06p04_column_15 : reversePack 32 (fun j : Fin 22 => R06p04_digit j 15)=R06p04_columnCode 15 := by decide +kernel

private theorem R06p04_column_16 : reversePack 32 (fun j : Fin 22 => R06p04_digit j 16)=R06p04_columnCode 16 := by decide +kernel

private theorem R06p04_column_17 : reversePack 32 (fun j : Fin 22 => R06p04_digit j 17)=R06p04_columnCode 17 := by decide +kernel

private theorem R06p04_column_18 : reversePack 32 (fun j : Fin 22 => R06p04_digit j 18)=R06p04_columnCode 18 := by decide +kernel

private theorem R06p04_column_19 : reversePack 32 (fun j : Fin 22 => R06p04_digit j 19)=R06p04_columnCode 19 := by decide +kernel

private theorem R06p04_column_20 : reversePack 32 (fun j : Fin 22 => R06p04_digit j 20)=R06p04_columnCode 20 := by decide +kernel

private theorem R06p04_column_21 : reversePack 32 (fun j : Fin 22 => R06p04_digit j 21)=R06p04_columnCode 21 := by decide +kernel

theorem R06p04_column_binding : ∀ i : Fin 22,reversePack 32 (fun j : Fin 22 => R06p04_digit j i)=R06p04_columnCode i := by
  intro i
  fin_cases i
  · exact R06p04_column_00
  · exact R06p04_column_01
  · exact R06p04_column_02
  · exact R06p04_column_03
  · exact R06p04_column_04
  · exact R06p04_column_05
  · exact R06p04_column_06
  · exact R06p04_column_07
  · exact R06p04_column_08
  · exact R06p04_column_09
  · exact R06p04_column_10
  · exact R06p04_column_11
  · exact R06p04_column_12
  · exact R06p04_column_13
  · exact R06p04_column_14
  · exact R06p04_column_15
  · exact R06p04_column_16
  · exact R06p04_column_17
  · exact R06p04_column_18
  · exact R06p04_column_19
  · exact R06p04_column_20
  · exact R06p04_column_21

def R06p04_data : PackedData 22 2 32 where
  raw := R06p04_digit
  digit_lt := R06p04_bound
  rowCode := R06p04_rowCode
  columnCode := R06p04_columnCode
  row_binding := R06p04_row_binding
  column_binding := R06p04_column_binding

def R06p05_lowColumnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 2394769
  | 1 => 1067422
  | 2 => 1374640
  | 3 => 3455682
  | 4 => 3950707
  | 5 => 3038787
  | 6 => 2797682
  | 7 => 2859730
  | 8 => 2935488
  | 9 => 182339
  | 10 => 2017458
  | 11 => 2273313
  | 12 => 2923202
  | 13 => 1196626
  | 14 => 12960
  | 15 => 1489602
  | 16 => 1231408
  | 17 => 3418688
  | 18 => 1106514
  | 19 => 3207414
  | 20 => 2151120
  | 21 => 3416064
  | _ => 0

def R06p05_rowCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 36063981425655809
  | 1 => 40852059113396982800605806624
  | 2 => 39614081257132168796771975200
  | 3 => 32
  | 4 => 1308503830487361179280309486625
  | 5 => 39615291363580558841358582784
  | 6 => 1308541344967852927630504394752
  | 7 => 1307264720446039102506433283105
  | 8 => 1056
  | 9 => 1268928473817131958994871549953
  | 10 => 33554432
  | 11 => 39932332133229408359056417
  | 12 => 1307264720446074004270781334528
  | 13 => 40605709953185545577606789760000
  | 14 => 1308503830487361215528793277472
  | 15 => 1308503868230588540675560604673
  | 16 => 34359738368
  | 17 => 1246741682155650520449024
  | 18 => 40564857930709654427489314833409
  | 19 => 1154048539493400576
  | 20 => 40605711160967632156733427713056
  | 21 => 41872122574416119037758173904897
  | _ => 0

def R06p05_columnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 40564857894111314184151091937281
  | 1 => 1308541308368360853501061890080
  | 2 => 39895769533553846819782688
  | 3 => 1267650639188906968860747399201
  | 4 => 41832509739862550521045399405601
  | 5 => 41832469845311692223768633050113
  | 6 => 1267690532559208583501588726785
  | 7 => 1267689324815133475910093636609
  | 8 => 38960677531114520216577
  | 9 => 41832469845310503238283708858368
  | 10 => 1267690495960869430912221217824
  | 11 => 40564820416229160498808635785217
  | 12 => 1267650639188906967761235772417
  | 13 => 1267689323634541854126423146528
  | 14 => 1210107564193135076573184
  | 15 => 1267650639188906968860748447776
  | 16 => 39894553201330202713522208
  | 17 => 37780085911461187059745
  | 18 => 1267689323634541855227007467552
  | 19 => 1307304614996932373050130694177
  | 20 => 38724586904108532576026625
  | 21 => 1099511660577
  | _ => 0

def R06p05_digit (i j : Fin 22) : ℕ := packedDigit 1 (R06p05_lowColumnCode j) i.val

private theorem R06p05_bound_00 : ∀ j : Fin 22,R06p05_digit 0 j<2 := by decide +kernel

private theorem R06p05_bound_01 : ∀ j : Fin 22,R06p05_digit 1 j<2 := by decide +kernel

private theorem R06p05_bound_02 : ∀ j : Fin 22,R06p05_digit 2 j<2 := by decide +kernel

private theorem R06p05_bound_03 : ∀ j : Fin 22,R06p05_digit 3 j<2 := by decide +kernel

private theorem R06p05_bound_04 : ∀ j : Fin 22,R06p05_digit 4 j<2 := by decide +kernel

private theorem R06p05_bound_05 : ∀ j : Fin 22,R06p05_digit 5 j<2 := by decide +kernel

private theorem R06p05_bound_06 : ∀ j : Fin 22,R06p05_digit 6 j<2 := by decide +kernel

private theorem R06p05_bound_07 : ∀ j : Fin 22,R06p05_digit 7 j<2 := by decide +kernel

private theorem R06p05_bound_08 : ∀ j : Fin 22,R06p05_digit 8 j<2 := by decide +kernel

private theorem R06p05_bound_09 : ∀ j : Fin 22,R06p05_digit 9 j<2 := by decide +kernel

private theorem R06p05_bound_10 : ∀ j : Fin 22,R06p05_digit 10 j<2 := by decide +kernel

private theorem R06p05_bound_11 : ∀ j : Fin 22,R06p05_digit 11 j<2 := by decide +kernel

private theorem R06p05_bound_12 : ∀ j : Fin 22,R06p05_digit 12 j<2 := by decide +kernel

private theorem R06p05_bound_13 : ∀ j : Fin 22,R06p05_digit 13 j<2 := by decide +kernel

private theorem R06p05_bound_14 : ∀ j : Fin 22,R06p05_digit 14 j<2 := by decide +kernel

private theorem R06p05_bound_15 : ∀ j : Fin 22,R06p05_digit 15 j<2 := by decide +kernel

private theorem R06p05_bound_16 : ∀ j : Fin 22,R06p05_digit 16 j<2 := by decide +kernel

private theorem R06p05_bound_17 : ∀ j : Fin 22,R06p05_digit 17 j<2 := by decide +kernel

private theorem R06p05_bound_18 : ∀ j : Fin 22,R06p05_digit 18 j<2 := by decide +kernel

private theorem R06p05_bound_19 : ∀ j : Fin 22,R06p05_digit 19 j<2 := by decide +kernel

private theorem R06p05_bound_20 : ∀ j : Fin 22,R06p05_digit 20 j<2 := by decide +kernel

private theorem R06p05_bound_21 : ∀ j : Fin 22,R06p05_digit 21 j<2 := by decide +kernel

theorem R06p05_bound : ∀ i j : Fin 22,R06p05_digit i j<2 := by
  intro i j
  fin_cases i
  · exact R06p05_bound_00 j
  · exact R06p05_bound_01 j
  · exact R06p05_bound_02 j
  · exact R06p05_bound_03 j
  · exact R06p05_bound_04 j
  · exact R06p05_bound_05 j
  · exact R06p05_bound_06 j
  · exact R06p05_bound_07 j
  · exact R06p05_bound_08 j
  · exact R06p05_bound_09 j
  · exact R06p05_bound_10 j
  · exact R06p05_bound_11 j
  · exact R06p05_bound_12 j
  · exact R06p05_bound_13 j
  · exact R06p05_bound_14 j
  · exact R06p05_bound_15 j
  · exact R06p05_bound_16 j
  · exact R06p05_bound_17 j
  · exact R06p05_bound_18 j
  · exact R06p05_bound_19 j
  · exact R06p05_bound_20 j
  · exact R06p05_bound_21 j

private theorem R06p05_row_00 : pack 32 (R06p05_digit 0)=R06p05_rowCode 0 := by decide +kernel

private theorem R06p05_row_01 : pack 32 (R06p05_digit 1)=R06p05_rowCode 1 := by decide +kernel

private theorem R06p05_row_02 : pack 32 (R06p05_digit 2)=R06p05_rowCode 2 := by decide +kernel

private theorem R06p05_row_03 : pack 32 (R06p05_digit 3)=R06p05_rowCode 3 := by decide +kernel

private theorem R06p05_row_04 : pack 32 (R06p05_digit 4)=R06p05_rowCode 4 := by decide +kernel

private theorem R06p05_row_05 : pack 32 (R06p05_digit 5)=R06p05_rowCode 5 := by decide +kernel

private theorem R06p05_row_06 : pack 32 (R06p05_digit 6)=R06p05_rowCode 6 := by decide +kernel

private theorem R06p05_row_07 : pack 32 (R06p05_digit 7)=R06p05_rowCode 7 := by decide +kernel

private theorem R06p05_row_08 : pack 32 (R06p05_digit 8)=R06p05_rowCode 8 := by decide +kernel

private theorem R06p05_row_09 : pack 32 (R06p05_digit 9)=R06p05_rowCode 9 := by decide +kernel

private theorem R06p05_row_10 : pack 32 (R06p05_digit 10)=R06p05_rowCode 10 := by decide +kernel

private theorem R06p05_row_11 : pack 32 (R06p05_digit 11)=R06p05_rowCode 11 := by decide +kernel

private theorem R06p05_row_12 : pack 32 (R06p05_digit 12)=R06p05_rowCode 12 := by decide +kernel

private theorem R06p05_row_13 : pack 32 (R06p05_digit 13)=R06p05_rowCode 13 := by decide +kernel

private theorem R06p05_row_14 : pack 32 (R06p05_digit 14)=R06p05_rowCode 14 := by decide +kernel

private theorem R06p05_row_15 : pack 32 (R06p05_digit 15)=R06p05_rowCode 15 := by decide +kernel

private theorem R06p05_row_16 : pack 32 (R06p05_digit 16)=R06p05_rowCode 16 := by decide +kernel

private theorem R06p05_row_17 : pack 32 (R06p05_digit 17)=R06p05_rowCode 17 := by decide +kernel

private theorem R06p05_row_18 : pack 32 (R06p05_digit 18)=R06p05_rowCode 18 := by decide +kernel

private theorem R06p05_row_19 : pack 32 (R06p05_digit 19)=R06p05_rowCode 19 := by decide +kernel

private theorem R06p05_row_20 : pack 32 (R06p05_digit 20)=R06p05_rowCode 20 := by decide +kernel

private theorem R06p05_row_21 : pack 32 (R06p05_digit 21)=R06p05_rowCode 21 := by decide +kernel

theorem R06p05_row_binding : ∀ i : Fin 22,pack 32 (R06p05_digit i)=R06p05_rowCode i := by
  intro i
  fin_cases i
  · exact R06p05_row_00
  · exact R06p05_row_01
  · exact R06p05_row_02
  · exact R06p05_row_03
  · exact R06p05_row_04
  · exact R06p05_row_05
  · exact R06p05_row_06
  · exact R06p05_row_07
  · exact R06p05_row_08
  · exact R06p05_row_09
  · exact R06p05_row_10
  · exact R06p05_row_11
  · exact R06p05_row_12
  · exact R06p05_row_13
  · exact R06p05_row_14
  · exact R06p05_row_15
  · exact R06p05_row_16
  · exact R06p05_row_17
  · exact R06p05_row_18
  · exact R06p05_row_19
  · exact R06p05_row_20
  · exact R06p05_row_21

private theorem R06p05_column_00 : reversePack 32 (fun j : Fin 22 => R06p05_digit j 0)=R06p05_columnCode 0 := by decide +kernel

private theorem R06p05_column_01 : reversePack 32 (fun j : Fin 22 => R06p05_digit j 1)=R06p05_columnCode 1 := by decide +kernel

private theorem R06p05_column_02 : reversePack 32 (fun j : Fin 22 => R06p05_digit j 2)=R06p05_columnCode 2 := by decide +kernel

private theorem R06p05_column_03 : reversePack 32 (fun j : Fin 22 => R06p05_digit j 3)=R06p05_columnCode 3 := by decide +kernel

private theorem R06p05_column_04 : reversePack 32 (fun j : Fin 22 => R06p05_digit j 4)=R06p05_columnCode 4 := by decide +kernel

private theorem R06p05_column_05 : reversePack 32 (fun j : Fin 22 => R06p05_digit j 5)=R06p05_columnCode 5 := by decide +kernel

private theorem R06p05_column_06 : reversePack 32 (fun j : Fin 22 => R06p05_digit j 6)=R06p05_columnCode 6 := by decide +kernel

private theorem R06p05_column_07 : reversePack 32 (fun j : Fin 22 => R06p05_digit j 7)=R06p05_columnCode 7 := by decide +kernel

private theorem R06p05_column_08 : reversePack 32 (fun j : Fin 22 => R06p05_digit j 8)=R06p05_columnCode 8 := by decide +kernel

private theorem R06p05_column_09 : reversePack 32 (fun j : Fin 22 => R06p05_digit j 9)=R06p05_columnCode 9 := by decide +kernel

private theorem R06p05_column_10 : reversePack 32 (fun j : Fin 22 => R06p05_digit j 10)=R06p05_columnCode 10 := by decide +kernel

private theorem R06p05_column_11 : reversePack 32 (fun j : Fin 22 => R06p05_digit j 11)=R06p05_columnCode 11 := by decide +kernel

private theorem R06p05_column_12 : reversePack 32 (fun j : Fin 22 => R06p05_digit j 12)=R06p05_columnCode 12 := by decide +kernel

private theorem R06p05_column_13 : reversePack 32 (fun j : Fin 22 => R06p05_digit j 13)=R06p05_columnCode 13 := by decide +kernel

private theorem R06p05_column_14 : reversePack 32 (fun j : Fin 22 => R06p05_digit j 14)=R06p05_columnCode 14 := by decide +kernel

private theorem R06p05_column_15 : reversePack 32 (fun j : Fin 22 => R06p05_digit j 15)=R06p05_columnCode 15 := by decide +kernel

private theorem R06p05_column_16 : reversePack 32 (fun j : Fin 22 => R06p05_digit j 16)=R06p05_columnCode 16 := by decide +kernel

private theorem R06p05_column_17 : reversePack 32 (fun j : Fin 22 => R06p05_digit j 17)=R06p05_columnCode 17 := by decide +kernel

private theorem R06p05_column_18 : reversePack 32 (fun j : Fin 22 => R06p05_digit j 18)=R06p05_columnCode 18 := by decide +kernel

private theorem R06p05_column_19 : reversePack 32 (fun j : Fin 22 => R06p05_digit j 19)=R06p05_columnCode 19 := by decide +kernel

private theorem R06p05_column_20 : reversePack 32 (fun j : Fin 22 => R06p05_digit j 20)=R06p05_columnCode 20 := by decide +kernel

private theorem R06p05_column_21 : reversePack 32 (fun j : Fin 22 => R06p05_digit j 21)=R06p05_columnCode 21 := by decide +kernel

theorem R06p05_column_binding : ∀ i : Fin 22,reversePack 32 (fun j : Fin 22 => R06p05_digit j i)=R06p05_columnCode i := by
  intro i
  fin_cases i
  · exact R06p05_column_00
  · exact R06p05_column_01
  · exact R06p05_column_02
  · exact R06p05_column_03
  · exact R06p05_column_04
  · exact R06p05_column_05
  · exact R06p05_column_06
  · exact R06p05_column_07
  · exact R06p05_column_08
  · exact R06p05_column_09
  · exact R06p05_column_10
  · exact R06p05_column_11
  · exact R06p05_column_12
  · exact R06p05_column_13
  · exact R06p05_column_14
  · exact R06p05_column_15
  · exact R06p05_column_16
  · exact R06p05_column_17
  · exact R06p05_column_18
  · exact R06p05_column_19
  · exact R06p05_column_20
  · exact R06p05_column_21

def R06p05_data : PackedData 22 2 32 where
  raw := R06p05_digit
  digit_lt := R06p05_bound
  rowCode := R06p05_rowCode
  columnCode := R06p05_columnCode
  row_binding := R06p05_row_binding
  column_binding := R06p05_column_binding

end SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoCaches03
