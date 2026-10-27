import SymmetricSubgroupAsymptotics.MatrixKroneckerProductReflection
import Mathlib.Tactic.FinCases

/-! Fixed Co2 binary22 shared caches. Every digit and pack binding is kernel checked. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoCaches12
open MatrixKroneckerProductReflection MatrixKroneckerDotReflection
open MatrixNaturalRowDotReflection SmallNaturalMatrixProductReflection

def R10p07_lowColumnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1419045
  | 1 => 1678755
  | 2 => 1429217
  | 3 => 1191434
  | 4 => 1455166
  | 5 => 1060346
  | 6 => 1218486
  | 7 => 1837548
  | 8 => 192226
  | 9 => 332034
  | 10 => 105254
  | 11 => 2158954
  | 12 => 2660943
  | 13 => 1992379
  | 14 => 929145
  | 15 => 564936
  | 16 => 1070254
  | 17 => 1316543
  | 18 => 639045
  | 19 => 1469494
  | 20 => 1136694
  | 21 => 2565712
  | _ => 0

def R10p07_rowCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1276626884151078777926976545
  | 1 => 1307304576075492453690184335392
  | 2 => 1308542516077848280771087826945
  | 3 => 39933549653204920777605120
  | 4 => 41872122575632415195187507101696
  | 5 => 1307304577254931117752976409633
  | 6 => 40566057186303338663279505441792
  | 7 => 39932367872635002324780064
  | 8 => 1180628810634176233505
  | 9 => 40564857930746547915637773075457
  | 10 => 40604473222108937272376651973665
  | 11 => 1307264720446039102506466837536
  | 12 => 1267690532560398658603609751584
  | 13 => 40604433289777994155452670181377
  | 14 => 1308503830487396083241498706944
  | 15 => 1237977819407320534178858017
  | 16 => 41833707747570856790750383834145
  | 17 => 40604433289777958126656691404800
  | 18 => 40604471975404185828908428428289
  | 19 => 1237979036855273635857825824
  | 20 => 1307304576074302341239127704609
  | 21 => 40564819207304529798196128382976
  | _ => 0

def R10p07_columnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 40604434497524375070870113124384
  | 1 => 41832471017674912162767616082976
  | 2 => 40564820455189874022435250012192
  | 3 => 1268888540268704859072647659552
  | 4 => 1308542516076730298412043370528
  | 5 => 1268928473816016192152797184032
  | 6 => 1307304577256082947408143581216
  | 7 => 40853269218655261422744798240
  | 8 => 1267651848114762577136929734656
  | 9 => 1267650600265122924828527984640
  | 10 => 1307265890449228755660062064640
  | 11 => 1268889787009159783824675045377
  | 12 => 41873321866608073744009998107649
  | 13 => 41833747643304683484581779768352
  | 14 => 40566097079710536017833186329600
  | 15 => 1237978999998975336450622464
  | 16 => 1308503831631094249930711105568
  | 17 => 41873361724561815687429051416608
  | 18 => 40604433326339404879683903292416
  | 19 => 1307304576037446008887038738464
  | 20 => 1307304576037410014174912708640
  | 21 => 38723406348482491924381697
  | _ => 0

def R10p07_digit (i j : Fin 22) : ℕ := packedDigit 1 (R10p07_lowColumnCode j) i.val

private theorem R10p07_bound_00 : ∀ j : Fin 22,R10p07_digit 0 j<2 := by decide +kernel

private theorem R10p07_bound_01 : ∀ j : Fin 22,R10p07_digit 1 j<2 := by decide +kernel

private theorem R10p07_bound_02 : ∀ j : Fin 22,R10p07_digit 2 j<2 := by decide +kernel

private theorem R10p07_bound_03 : ∀ j : Fin 22,R10p07_digit 3 j<2 := by decide +kernel

private theorem R10p07_bound_04 : ∀ j : Fin 22,R10p07_digit 4 j<2 := by decide +kernel

private theorem R10p07_bound_05 : ∀ j : Fin 22,R10p07_digit 5 j<2 := by decide +kernel

private theorem R10p07_bound_06 : ∀ j : Fin 22,R10p07_digit 6 j<2 := by decide +kernel

private theorem R10p07_bound_07 : ∀ j : Fin 22,R10p07_digit 7 j<2 := by decide +kernel

private theorem R10p07_bound_08 : ∀ j : Fin 22,R10p07_digit 8 j<2 := by decide +kernel

private theorem R10p07_bound_09 : ∀ j : Fin 22,R10p07_digit 9 j<2 := by decide +kernel

private theorem R10p07_bound_10 : ∀ j : Fin 22,R10p07_digit 10 j<2 := by decide +kernel

private theorem R10p07_bound_11 : ∀ j : Fin 22,R10p07_digit 11 j<2 := by decide +kernel

private theorem R10p07_bound_12 : ∀ j : Fin 22,R10p07_digit 12 j<2 := by decide +kernel

private theorem R10p07_bound_13 : ∀ j : Fin 22,R10p07_digit 13 j<2 := by decide +kernel

private theorem R10p07_bound_14 : ∀ j : Fin 22,R10p07_digit 14 j<2 := by decide +kernel

private theorem R10p07_bound_15 : ∀ j : Fin 22,R10p07_digit 15 j<2 := by decide +kernel

private theorem R10p07_bound_16 : ∀ j : Fin 22,R10p07_digit 16 j<2 := by decide +kernel

private theorem R10p07_bound_17 : ∀ j : Fin 22,R10p07_digit 17 j<2 := by decide +kernel

private theorem R10p07_bound_18 : ∀ j : Fin 22,R10p07_digit 18 j<2 := by decide +kernel

private theorem R10p07_bound_19 : ∀ j : Fin 22,R10p07_digit 19 j<2 := by decide +kernel

private theorem R10p07_bound_20 : ∀ j : Fin 22,R10p07_digit 20 j<2 := by decide +kernel

private theorem R10p07_bound_21 : ∀ j : Fin 22,R10p07_digit 21 j<2 := by decide +kernel

theorem R10p07_bound : ∀ i j : Fin 22,R10p07_digit i j<2 := by
  intro i j
  fin_cases i
  · exact R10p07_bound_00 j
  · exact R10p07_bound_01 j
  · exact R10p07_bound_02 j
  · exact R10p07_bound_03 j
  · exact R10p07_bound_04 j
  · exact R10p07_bound_05 j
  · exact R10p07_bound_06 j
  · exact R10p07_bound_07 j
  · exact R10p07_bound_08 j
  · exact R10p07_bound_09 j
  · exact R10p07_bound_10 j
  · exact R10p07_bound_11 j
  · exact R10p07_bound_12 j
  · exact R10p07_bound_13 j
  · exact R10p07_bound_14 j
  · exact R10p07_bound_15 j
  · exact R10p07_bound_16 j
  · exact R10p07_bound_17 j
  · exact R10p07_bound_18 j
  · exact R10p07_bound_19 j
  · exact R10p07_bound_20 j
  · exact R10p07_bound_21 j

private theorem R10p07_row_00 : pack 32 (R10p07_digit 0)=R10p07_rowCode 0 := by decide +kernel

private theorem R10p07_row_01 : pack 32 (R10p07_digit 1)=R10p07_rowCode 1 := by decide +kernel

private theorem R10p07_row_02 : pack 32 (R10p07_digit 2)=R10p07_rowCode 2 := by decide +kernel

private theorem R10p07_row_03 : pack 32 (R10p07_digit 3)=R10p07_rowCode 3 := by decide +kernel

private theorem R10p07_row_04 : pack 32 (R10p07_digit 4)=R10p07_rowCode 4 := by decide +kernel

private theorem R10p07_row_05 : pack 32 (R10p07_digit 5)=R10p07_rowCode 5 := by decide +kernel

private theorem R10p07_row_06 : pack 32 (R10p07_digit 6)=R10p07_rowCode 6 := by decide +kernel

private theorem R10p07_row_07 : pack 32 (R10p07_digit 7)=R10p07_rowCode 7 := by decide +kernel

private theorem R10p07_row_08 : pack 32 (R10p07_digit 8)=R10p07_rowCode 8 := by decide +kernel

private theorem R10p07_row_09 : pack 32 (R10p07_digit 9)=R10p07_rowCode 9 := by decide +kernel

private theorem R10p07_row_10 : pack 32 (R10p07_digit 10)=R10p07_rowCode 10 := by decide +kernel

private theorem R10p07_row_11 : pack 32 (R10p07_digit 11)=R10p07_rowCode 11 := by decide +kernel

private theorem R10p07_row_12 : pack 32 (R10p07_digit 12)=R10p07_rowCode 12 := by decide +kernel

private theorem R10p07_row_13 : pack 32 (R10p07_digit 13)=R10p07_rowCode 13 := by decide +kernel

private theorem R10p07_row_14 : pack 32 (R10p07_digit 14)=R10p07_rowCode 14 := by decide +kernel

private theorem R10p07_row_15 : pack 32 (R10p07_digit 15)=R10p07_rowCode 15 := by decide +kernel

private theorem R10p07_row_16 : pack 32 (R10p07_digit 16)=R10p07_rowCode 16 := by decide +kernel

private theorem R10p07_row_17 : pack 32 (R10p07_digit 17)=R10p07_rowCode 17 := by decide +kernel

private theorem R10p07_row_18 : pack 32 (R10p07_digit 18)=R10p07_rowCode 18 := by decide +kernel

private theorem R10p07_row_19 : pack 32 (R10p07_digit 19)=R10p07_rowCode 19 := by decide +kernel

private theorem R10p07_row_20 : pack 32 (R10p07_digit 20)=R10p07_rowCode 20 := by decide +kernel

private theorem R10p07_row_21 : pack 32 (R10p07_digit 21)=R10p07_rowCode 21 := by decide +kernel

theorem R10p07_row_binding : ∀ i : Fin 22,pack 32 (R10p07_digit i)=R10p07_rowCode i := by
  intro i
  fin_cases i
  · exact R10p07_row_00
  · exact R10p07_row_01
  · exact R10p07_row_02
  · exact R10p07_row_03
  · exact R10p07_row_04
  · exact R10p07_row_05
  · exact R10p07_row_06
  · exact R10p07_row_07
  · exact R10p07_row_08
  · exact R10p07_row_09
  · exact R10p07_row_10
  · exact R10p07_row_11
  · exact R10p07_row_12
  · exact R10p07_row_13
  · exact R10p07_row_14
  · exact R10p07_row_15
  · exact R10p07_row_16
  · exact R10p07_row_17
  · exact R10p07_row_18
  · exact R10p07_row_19
  · exact R10p07_row_20
  · exact R10p07_row_21

private theorem R10p07_column_00 : reversePack 32 (fun j : Fin 22 => R10p07_digit j 0)=R10p07_columnCode 0 := by decide +kernel

private theorem R10p07_column_01 : reversePack 32 (fun j : Fin 22 => R10p07_digit j 1)=R10p07_columnCode 1 := by decide +kernel

private theorem R10p07_column_02 : reversePack 32 (fun j : Fin 22 => R10p07_digit j 2)=R10p07_columnCode 2 := by decide +kernel

private theorem R10p07_column_03 : reversePack 32 (fun j : Fin 22 => R10p07_digit j 3)=R10p07_columnCode 3 := by decide +kernel

private theorem R10p07_column_04 : reversePack 32 (fun j : Fin 22 => R10p07_digit j 4)=R10p07_columnCode 4 := by decide +kernel

private theorem R10p07_column_05 : reversePack 32 (fun j : Fin 22 => R10p07_digit j 5)=R10p07_columnCode 5 := by decide +kernel

private theorem R10p07_column_06 : reversePack 32 (fun j : Fin 22 => R10p07_digit j 6)=R10p07_columnCode 6 := by decide +kernel

private theorem R10p07_column_07 : reversePack 32 (fun j : Fin 22 => R10p07_digit j 7)=R10p07_columnCode 7 := by decide +kernel

private theorem R10p07_column_08 : reversePack 32 (fun j : Fin 22 => R10p07_digit j 8)=R10p07_columnCode 8 := by decide +kernel

private theorem R10p07_column_09 : reversePack 32 (fun j : Fin 22 => R10p07_digit j 9)=R10p07_columnCode 9 := by decide +kernel

private theorem R10p07_column_10 : reversePack 32 (fun j : Fin 22 => R10p07_digit j 10)=R10p07_columnCode 10 := by decide +kernel

private theorem R10p07_column_11 : reversePack 32 (fun j : Fin 22 => R10p07_digit j 11)=R10p07_columnCode 11 := by decide +kernel

private theorem R10p07_column_12 : reversePack 32 (fun j : Fin 22 => R10p07_digit j 12)=R10p07_columnCode 12 := by decide +kernel

private theorem R10p07_column_13 : reversePack 32 (fun j : Fin 22 => R10p07_digit j 13)=R10p07_columnCode 13 := by decide +kernel

private theorem R10p07_column_14 : reversePack 32 (fun j : Fin 22 => R10p07_digit j 14)=R10p07_columnCode 14 := by decide +kernel

private theorem R10p07_column_15 : reversePack 32 (fun j : Fin 22 => R10p07_digit j 15)=R10p07_columnCode 15 := by decide +kernel

private theorem R10p07_column_16 : reversePack 32 (fun j : Fin 22 => R10p07_digit j 16)=R10p07_columnCode 16 := by decide +kernel

private theorem R10p07_column_17 : reversePack 32 (fun j : Fin 22 => R10p07_digit j 17)=R10p07_columnCode 17 := by decide +kernel

private theorem R10p07_column_18 : reversePack 32 (fun j : Fin 22 => R10p07_digit j 18)=R10p07_columnCode 18 := by decide +kernel

private theorem R10p07_column_19 : reversePack 32 (fun j : Fin 22 => R10p07_digit j 19)=R10p07_columnCode 19 := by decide +kernel

private theorem R10p07_column_20 : reversePack 32 (fun j : Fin 22 => R10p07_digit j 20)=R10p07_columnCode 20 := by decide +kernel

private theorem R10p07_column_21 : reversePack 32 (fun j : Fin 22 => R10p07_digit j 21)=R10p07_columnCode 21 := by decide +kernel

theorem R10p07_column_binding : ∀ i : Fin 22,reversePack 32 (fun j : Fin 22 => R10p07_digit j i)=R10p07_columnCode i := by
  intro i
  fin_cases i
  · exact R10p07_column_00
  · exact R10p07_column_01
  · exact R10p07_column_02
  · exact R10p07_column_03
  · exact R10p07_column_04
  · exact R10p07_column_05
  · exact R10p07_column_06
  · exact R10p07_column_07
  · exact R10p07_column_08
  · exact R10p07_column_09
  · exact R10p07_column_10
  · exact R10p07_column_11
  · exact R10p07_column_12
  · exact R10p07_column_13
  · exact R10p07_column_14
  · exact R10p07_column_15
  · exact R10p07_column_16
  · exact R10p07_column_17
  · exact R10p07_column_18
  · exact R10p07_column_19
  · exact R10p07_column_20
  · exact R10p07_column_21

def R10p07_data : PackedData 22 2 32 where
  raw := R10p07_digit
  digit_lt := R10p07_bound
  rowCode := R10p07_rowCode
  columnCode := R10p07_columnCode
  row_binding := R10p07_row_binding
  column_binding := R10p07_column_binding

def R10e02_lowColumnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 529494
  | 1 => 1375767
  | 2 => 2166951
  | 3 => 3465429
  | 4 => 2330002
  | 5 => 3116564
  | 6 => 3501474
  | 7 => 3520646
  | 8 => 3118840
  | 9 => 2784741
  | 10 => 729115
  | 11 => 1871378
  | 12 => 3007314
  | 13 => 665528
  | 14 => 2449284
  | 15 => 959407
  | 16 => 2370936
  | 17 => 2441821
  | 18 => 1209691
  | 19 => 3663300
  | 20 => 852034
  | 21 => 3468051
  | _ => 0

def R10e02_rowCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 40566095870747786920344432968736
  | 1 => 41833707785350977568860233794593
  | 2 => 39652805842883355823701001249
  | 3 => 1277872407159141141663711232
  | 4 => 40566097041932757076380665020449
  | 5 => 1246741645002018712978432
  | 6 => 1308542516077847191119630204929
  | 7 => 39614120253549176938082370560
  | 8 => 40605672476523147940107394220032
  | 9 => 40564857931927174439251256279072
  | 10 => 40853231439758337647687237665
  | 11 => 40564820417409788147257947717664
  | 12 => 1237941219877037310553883681
  | 13 => 40605672475342557445324248481824
  | 14 => 40605709915407730642507228282912
  | 15 => 40604433326340593831083968069664
  | 16 => 1307303368293334907683970483200
  | 17 => 40852059112244062360077074432
  | 18 => 41872123822301462136061920575520
  | 19 => 1267650638045244865086733942785
  | 20 => 40605671228599794425798626148384
  | 21 => 40604473184294264877995409835008
  | _ => 0

def R10e02_columnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1307303404890557165365618541568
  | 1 => 41872122574416120198842418233376
  | 2 => 41872085098895113688718969405441
  | 3 => 40604472013146224169634383298593
  | 4 => 1267689287071979333193158361089
  | 5 => 39652766884549913133003604993
  | 6 => 1267651810371571280821539078177
  | 7 => 1307264682665954353195784372257
  | 8 => 1277873552045132199343719425
  | 9 => 40604434536482746794157611680769
  | 10 => 41833746433197083298899241731072
  | 11 => 1267689285855647145832900232224
  | 12 => 1267689323671435343374460158977
  | 13 => 1277835810006723303633323008
  | 14 => 39614082475807389081900449793
  | 15 => 41873323038972445444562075288576
  | 16 => 1277872407195169938682707969
  | 17 => 40605709952006070849595926151169
  | 18 => 41833746471012944714019539779616
  | 19 => 39614120253585170550762799137
  | 20 => 1267650638007161264453898503168
  | 21 => 41832508493195845454211674308641
  | _ => 0

def R10e02_digit (i j : Fin 22) : ℕ := packedDigit 1 (R10e02_lowColumnCode j) i.val

private theorem R10e02_bound_00 : ∀ j : Fin 22,R10e02_digit 0 j<2 := by decide +kernel

private theorem R10e02_bound_01 : ∀ j : Fin 22,R10e02_digit 1 j<2 := by decide +kernel

private theorem R10e02_bound_02 : ∀ j : Fin 22,R10e02_digit 2 j<2 := by decide +kernel

private theorem R10e02_bound_03 : ∀ j : Fin 22,R10e02_digit 3 j<2 := by decide +kernel

private theorem R10e02_bound_04 : ∀ j : Fin 22,R10e02_digit 4 j<2 := by decide +kernel

private theorem R10e02_bound_05 : ∀ j : Fin 22,R10e02_digit 5 j<2 := by decide +kernel

private theorem R10e02_bound_06 : ∀ j : Fin 22,R10e02_digit 6 j<2 := by decide +kernel

private theorem R10e02_bound_07 : ∀ j : Fin 22,R10e02_digit 7 j<2 := by decide +kernel

private theorem R10e02_bound_08 : ∀ j : Fin 22,R10e02_digit 8 j<2 := by decide +kernel

private theorem R10e02_bound_09 : ∀ j : Fin 22,R10e02_digit 9 j<2 := by decide +kernel

private theorem R10e02_bound_10 : ∀ j : Fin 22,R10e02_digit 10 j<2 := by decide +kernel

private theorem R10e02_bound_11 : ∀ j : Fin 22,R10e02_digit 11 j<2 := by decide +kernel

private theorem R10e02_bound_12 : ∀ j : Fin 22,R10e02_digit 12 j<2 := by decide +kernel

private theorem R10e02_bound_13 : ∀ j : Fin 22,R10e02_digit 13 j<2 := by decide +kernel

private theorem R10e02_bound_14 : ∀ j : Fin 22,R10e02_digit 14 j<2 := by decide +kernel

private theorem R10e02_bound_15 : ∀ j : Fin 22,R10e02_digit 15 j<2 := by decide +kernel

private theorem R10e02_bound_16 : ∀ j : Fin 22,R10e02_digit 16 j<2 := by decide +kernel

private theorem R10e02_bound_17 : ∀ j : Fin 22,R10e02_digit 17 j<2 := by decide +kernel

private theorem R10e02_bound_18 : ∀ j : Fin 22,R10e02_digit 18 j<2 := by decide +kernel

private theorem R10e02_bound_19 : ∀ j : Fin 22,R10e02_digit 19 j<2 := by decide +kernel

private theorem R10e02_bound_20 : ∀ j : Fin 22,R10e02_digit 20 j<2 := by decide +kernel

private theorem R10e02_bound_21 : ∀ j : Fin 22,R10e02_digit 21 j<2 := by decide +kernel

theorem R10e02_bound : ∀ i j : Fin 22,R10e02_digit i j<2 := by
  intro i j
  fin_cases i
  · exact R10e02_bound_00 j
  · exact R10e02_bound_01 j
  · exact R10e02_bound_02 j
  · exact R10e02_bound_03 j
  · exact R10e02_bound_04 j
  · exact R10e02_bound_05 j
  · exact R10e02_bound_06 j
  · exact R10e02_bound_07 j
  · exact R10e02_bound_08 j
  · exact R10e02_bound_09 j
  · exact R10e02_bound_10 j
  · exact R10e02_bound_11 j
  · exact R10e02_bound_12 j
  · exact R10e02_bound_13 j
  · exact R10e02_bound_14 j
  · exact R10e02_bound_15 j
  · exact R10e02_bound_16 j
  · exact R10e02_bound_17 j
  · exact R10e02_bound_18 j
  · exact R10e02_bound_19 j
  · exact R10e02_bound_20 j
  · exact R10e02_bound_21 j

private theorem R10e02_row_00 : pack 32 (R10e02_digit 0)=R10e02_rowCode 0 := by decide +kernel

private theorem R10e02_row_01 : pack 32 (R10e02_digit 1)=R10e02_rowCode 1 := by decide +kernel

private theorem R10e02_row_02 : pack 32 (R10e02_digit 2)=R10e02_rowCode 2 := by decide +kernel

private theorem R10e02_row_03 : pack 32 (R10e02_digit 3)=R10e02_rowCode 3 := by decide +kernel

private theorem R10e02_row_04 : pack 32 (R10e02_digit 4)=R10e02_rowCode 4 := by decide +kernel

private theorem R10e02_row_05 : pack 32 (R10e02_digit 5)=R10e02_rowCode 5 := by decide +kernel

private theorem R10e02_row_06 : pack 32 (R10e02_digit 6)=R10e02_rowCode 6 := by decide +kernel

private theorem R10e02_row_07 : pack 32 (R10e02_digit 7)=R10e02_rowCode 7 := by decide +kernel

private theorem R10e02_row_08 : pack 32 (R10e02_digit 8)=R10e02_rowCode 8 := by decide +kernel

private theorem R10e02_row_09 : pack 32 (R10e02_digit 9)=R10e02_rowCode 9 := by decide +kernel

private theorem R10e02_row_10 : pack 32 (R10e02_digit 10)=R10e02_rowCode 10 := by decide +kernel

private theorem R10e02_row_11 : pack 32 (R10e02_digit 11)=R10e02_rowCode 11 := by decide +kernel

private theorem R10e02_row_12 : pack 32 (R10e02_digit 12)=R10e02_rowCode 12 := by decide +kernel

private theorem R10e02_row_13 : pack 32 (R10e02_digit 13)=R10e02_rowCode 13 := by decide +kernel

private theorem R10e02_row_14 : pack 32 (R10e02_digit 14)=R10e02_rowCode 14 := by decide +kernel

private theorem R10e02_row_15 : pack 32 (R10e02_digit 15)=R10e02_rowCode 15 := by decide +kernel

private theorem R10e02_row_16 : pack 32 (R10e02_digit 16)=R10e02_rowCode 16 := by decide +kernel

private theorem R10e02_row_17 : pack 32 (R10e02_digit 17)=R10e02_rowCode 17 := by decide +kernel

private theorem R10e02_row_18 : pack 32 (R10e02_digit 18)=R10e02_rowCode 18 := by decide +kernel

private theorem R10e02_row_19 : pack 32 (R10e02_digit 19)=R10e02_rowCode 19 := by decide +kernel

private theorem R10e02_row_20 : pack 32 (R10e02_digit 20)=R10e02_rowCode 20 := by decide +kernel

private theorem R10e02_row_21 : pack 32 (R10e02_digit 21)=R10e02_rowCode 21 := by decide +kernel

theorem R10e02_row_binding : ∀ i : Fin 22,pack 32 (R10e02_digit i)=R10e02_rowCode i := by
  intro i
  fin_cases i
  · exact R10e02_row_00
  · exact R10e02_row_01
  · exact R10e02_row_02
  · exact R10e02_row_03
  · exact R10e02_row_04
  · exact R10e02_row_05
  · exact R10e02_row_06
  · exact R10e02_row_07
  · exact R10e02_row_08
  · exact R10e02_row_09
  · exact R10e02_row_10
  · exact R10e02_row_11
  · exact R10e02_row_12
  · exact R10e02_row_13
  · exact R10e02_row_14
  · exact R10e02_row_15
  · exact R10e02_row_16
  · exact R10e02_row_17
  · exact R10e02_row_18
  · exact R10e02_row_19
  · exact R10e02_row_20
  · exact R10e02_row_21

private theorem R10e02_column_00 : reversePack 32 (fun j : Fin 22 => R10e02_digit j 0)=R10e02_columnCode 0 := by decide +kernel

private theorem R10e02_column_01 : reversePack 32 (fun j : Fin 22 => R10e02_digit j 1)=R10e02_columnCode 1 := by decide +kernel

private theorem R10e02_column_02 : reversePack 32 (fun j : Fin 22 => R10e02_digit j 2)=R10e02_columnCode 2 := by decide +kernel

private theorem R10e02_column_03 : reversePack 32 (fun j : Fin 22 => R10e02_digit j 3)=R10e02_columnCode 3 := by decide +kernel

private theorem R10e02_column_04 : reversePack 32 (fun j : Fin 22 => R10e02_digit j 4)=R10e02_columnCode 4 := by decide +kernel

private theorem R10e02_column_05 : reversePack 32 (fun j : Fin 22 => R10e02_digit j 5)=R10e02_columnCode 5 := by decide +kernel

private theorem R10e02_column_06 : reversePack 32 (fun j : Fin 22 => R10e02_digit j 6)=R10e02_columnCode 6 := by decide +kernel

private theorem R10e02_column_07 : reversePack 32 (fun j : Fin 22 => R10e02_digit j 7)=R10e02_columnCode 7 := by decide +kernel

private theorem R10e02_column_08 : reversePack 32 (fun j : Fin 22 => R10e02_digit j 8)=R10e02_columnCode 8 := by decide +kernel

private theorem R10e02_column_09 : reversePack 32 (fun j : Fin 22 => R10e02_digit j 9)=R10e02_columnCode 9 := by decide +kernel

private theorem R10e02_column_10 : reversePack 32 (fun j : Fin 22 => R10e02_digit j 10)=R10e02_columnCode 10 := by decide +kernel

private theorem R10e02_column_11 : reversePack 32 (fun j : Fin 22 => R10e02_digit j 11)=R10e02_columnCode 11 := by decide +kernel

private theorem R10e02_column_12 : reversePack 32 (fun j : Fin 22 => R10e02_digit j 12)=R10e02_columnCode 12 := by decide +kernel

private theorem R10e02_column_13 : reversePack 32 (fun j : Fin 22 => R10e02_digit j 13)=R10e02_columnCode 13 := by decide +kernel

private theorem R10e02_column_14 : reversePack 32 (fun j : Fin 22 => R10e02_digit j 14)=R10e02_columnCode 14 := by decide +kernel

private theorem R10e02_column_15 : reversePack 32 (fun j : Fin 22 => R10e02_digit j 15)=R10e02_columnCode 15 := by decide +kernel

private theorem R10e02_column_16 : reversePack 32 (fun j : Fin 22 => R10e02_digit j 16)=R10e02_columnCode 16 := by decide +kernel

private theorem R10e02_column_17 : reversePack 32 (fun j : Fin 22 => R10e02_digit j 17)=R10e02_columnCode 17 := by decide +kernel

private theorem R10e02_column_18 : reversePack 32 (fun j : Fin 22 => R10e02_digit j 18)=R10e02_columnCode 18 := by decide +kernel

private theorem R10e02_column_19 : reversePack 32 (fun j : Fin 22 => R10e02_digit j 19)=R10e02_columnCode 19 := by decide +kernel

private theorem R10e02_column_20 : reversePack 32 (fun j : Fin 22 => R10e02_digit j 20)=R10e02_columnCode 20 := by decide +kernel

private theorem R10e02_column_21 : reversePack 32 (fun j : Fin 22 => R10e02_digit j 21)=R10e02_columnCode 21 := by decide +kernel

theorem R10e02_column_binding : ∀ i : Fin 22,reversePack 32 (fun j : Fin 22 => R10e02_digit j i)=R10e02_columnCode i := by
  intro i
  fin_cases i
  · exact R10e02_column_00
  · exact R10e02_column_01
  · exact R10e02_column_02
  · exact R10e02_column_03
  · exact R10e02_column_04
  · exact R10e02_column_05
  · exact R10e02_column_06
  · exact R10e02_column_07
  · exact R10e02_column_08
  · exact R10e02_column_09
  · exact R10e02_column_10
  · exact R10e02_column_11
  · exact R10e02_column_12
  · exact R10e02_column_13
  · exact R10e02_column_14
  · exact R10e02_column_15
  · exact R10e02_column_16
  · exact R10e02_column_17
  · exact R10e02_column_18
  · exact R10e02_column_19
  · exact R10e02_column_20
  · exact R10e02_column_21

def R10e02_data : PackedData 22 2 32 where
  raw := R10e02_digit
  digit_lt := R10e02_bound
  rowCode := R10e02_rowCode
  columnCode := R10e02_columnCode
  row_binding := R10e02_row_binding
  column_binding := R10e02_column_binding

def R10e04_lowColumnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 3287053
  | 1 => 3205440
  | 2 => 1763661
  | 3 => 6622
  | 4 => 119915
  | 5 => 2226655
  | 6 => 1456954
  | 7 => 3804179
  | 8 => 2768861
  | 9 => 1749204
  | 10 => 3615327
  | 11 => 2921243
  | 12 => 1275997
  | 13 => 1773810
  | 14 => 844499
  | 15 => 1216873
  | 16 => 1642480
  | 17 => 431429
  | 18 => 3179830
  | 19 => 940508
  | 20 => 2109010
  | 21 => 2901829
  | _ => 0

def R10e04_rowCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 40564857931890282077038104806401
  | 1 => 1268888541485037045368826658816
  | 2 => 40605709914227140148788195263489
  | 3 => 39614119037254109056086344705
  | 4 => 1308503831669141786583262855168
  | 5 => 1239186780930346009729433600
  | 6 => 41872123822338320756461167215648
  | 7 => 39615291400436928574694391808
  | 8 => 40605711160930773572583738606624
  | 9 => 41832471017638018640535302963200
  | 10 => 41833747642122902913562742620160
  | 11 => 1307265890412335233462142272545
  | 12 => 39652804700374174621561290752
  | 13 => 1267650601409975105903619212321
  | 14 => 40604433289742217558913327301664
  | 15 => 1276664625072596064488391712
  | 16 => 1208963867150181142102016
  | 17 => 39652804700339271758774273025
  | 18 => 40604471975367329460240275996672
  | 19 => 40604434498703813805300542080000
  | 20 => 1239186782084428632973902881
  | 21 => 41833707747570892785496935628833
  | _ => 0

def R10e04_columnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 40605671228599759523965593190433
  | 1 => 37815826478139432763425
  | 2 => 40605671266415584875105607484448
  | 3 => 1308541346147292751608235950080
  | 4 => 41833708994275643171269299404800
  | 5 => 41873360553450633600637717184513
  | 6 => 1268928434857609636370185224224
  | 7 => 41832508493157835072221723231265
  | 8 => 40605709953223593149407173805057
  | 9 => 39652805842883356889894093856
  | 10 => 41873360552234301378057689137185
  | 11 => 41833746433235129742637167313921
  | 12 => 40605709952004919090275110879264
  | 13 => 1267690533739800203118448215072
  | 14 => 41832508532118474323838921376768
  | 15 => 40566058394084271229088604094496
  | 16 => 39933549654330786323629088
  | 17 => 40604433326376334431778321235968
  | 18 => 1307304576074338370001752293409
  | 19 => 40890745919063350145893565440
  | 20 => 1267689323634579009888499793921
  | 21 => 40604433326377487318131840943105
  | _ => 0

def R10e04_digit (i j : Fin 22) : ℕ := packedDigit 1 (R10e04_lowColumnCode j) i.val

private theorem R10e04_bound_00 : ∀ j : Fin 22,R10e04_digit 0 j<2 := by decide +kernel

private theorem R10e04_bound_01 : ∀ j : Fin 22,R10e04_digit 1 j<2 := by decide +kernel

private theorem R10e04_bound_02 : ∀ j : Fin 22,R10e04_digit 2 j<2 := by decide +kernel

private theorem R10e04_bound_03 : ∀ j : Fin 22,R10e04_digit 3 j<2 := by decide +kernel

private theorem R10e04_bound_04 : ∀ j : Fin 22,R10e04_digit 4 j<2 := by decide +kernel

private theorem R10e04_bound_05 : ∀ j : Fin 22,R10e04_digit 5 j<2 := by decide +kernel

private theorem R10e04_bound_06 : ∀ j : Fin 22,R10e04_digit 6 j<2 := by decide +kernel

private theorem R10e04_bound_07 : ∀ j : Fin 22,R10e04_digit 7 j<2 := by decide +kernel

private theorem R10e04_bound_08 : ∀ j : Fin 22,R10e04_digit 8 j<2 := by decide +kernel

private theorem R10e04_bound_09 : ∀ j : Fin 22,R10e04_digit 9 j<2 := by decide +kernel

private theorem R10e04_bound_10 : ∀ j : Fin 22,R10e04_digit 10 j<2 := by decide +kernel

private theorem R10e04_bound_11 : ∀ j : Fin 22,R10e04_digit 11 j<2 := by decide +kernel

private theorem R10e04_bound_12 : ∀ j : Fin 22,R10e04_digit 12 j<2 := by decide +kernel

private theorem R10e04_bound_13 : ∀ j : Fin 22,R10e04_digit 13 j<2 := by decide +kernel

private theorem R10e04_bound_14 : ∀ j : Fin 22,R10e04_digit 14 j<2 := by decide +kernel

private theorem R10e04_bound_15 : ∀ j : Fin 22,R10e04_digit 15 j<2 := by decide +kernel

private theorem R10e04_bound_16 : ∀ j : Fin 22,R10e04_digit 16 j<2 := by decide +kernel

private theorem R10e04_bound_17 : ∀ j : Fin 22,R10e04_digit 17 j<2 := by decide +kernel

private theorem R10e04_bound_18 : ∀ j : Fin 22,R10e04_digit 18 j<2 := by decide +kernel

private theorem R10e04_bound_19 : ∀ j : Fin 22,R10e04_digit 19 j<2 := by decide +kernel

private theorem R10e04_bound_20 : ∀ j : Fin 22,R10e04_digit 20 j<2 := by decide +kernel

private theorem R10e04_bound_21 : ∀ j : Fin 22,R10e04_digit 21 j<2 := by decide +kernel

theorem R10e04_bound : ∀ i j : Fin 22,R10e04_digit i j<2 := by
  intro i j
  fin_cases i
  · exact R10e04_bound_00 j
  · exact R10e04_bound_01 j
  · exact R10e04_bound_02 j
  · exact R10e04_bound_03 j
  · exact R10e04_bound_04 j
  · exact R10e04_bound_05 j
  · exact R10e04_bound_06 j
  · exact R10e04_bound_07 j
  · exact R10e04_bound_08 j
  · exact R10e04_bound_09 j
  · exact R10e04_bound_10 j
  · exact R10e04_bound_11 j
  · exact R10e04_bound_12 j
  · exact R10e04_bound_13 j
  · exact R10e04_bound_14 j
  · exact R10e04_bound_15 j
  · exact R10e04_bound_16 j
  · exact R10e04_bound_17 j
  · exact R10e04_bound_18 j
  · exact R10e04_bound_19 j
  · exact R10e04_bound_20 j
  · exact R10e04_bound_21 j

private theorem R10e04_row_00 : pack 32 (R10e04_digit 0)=R10e04_rowCode 0 := by decide +kernel

private theorem R10e04_row_01 : pack 32 (R10e04_digit 1)=R10e04_rowCode 1 := by decide +kernel

private theorem R10e04_row_02 : pack 32 (R10e04_digit 2)=R10e04_rowCode 2 := by decide +kernel

private theorem R10e04_row_03 : pack 32 (R10e04_digit 3)=R10e04_rowCode 3 := by decide +kernel

private theorem R10e04_row_04 : pack 32 (R10e04_digit 4)=R10e04_rowCode 4 := by decide +kernel

private theorem R10e04_row_05 : pack 32 (R10e04_digit 5)=R10e04_rowCode 5 := by decide +kernel

private theorem R10e04_row_06 : pack 32 (R10e04_digit 6)=R10e04_rowCode 6 := by decide +kernel

private theorem R10e04_row_07 : pack 32 (R10e04_digit 7)=R10e04_rowCode 7 := by decide +kernel

private theorem R10e04_row_08 : pack 32 (R10e04_digit 8)=R10e04_rowCode 8 := by decide +kernel

private theorem R10e04_row_09 : pack 32 (R10e04_digit 9)=R10e04_rowCode 9 := by decide +kernel

private theorem R10e04_row_10 : pack 32 (R10e04_digit 10)=R10e04_rowCode 10 := by decide +kernel

private theorem R10e04_row_11 : pack 32 (R10e04_digit 11)=R10e04_rowCode 11 := by decide +kernel

private theorem R10e04_row_12 : pack 32 (R10e04_digit 12)=R10e04_rowCode 12 := by decide +kernel

private theorem R10e04_row_13 : pack 32 (R10e04_digit 13)=R10e04_rowCode 13 := by decide +kernel

private theorem R10e04_row_14 : pack 32 (R10e04_digit 14)=R10e04_rowCode 14 := by decide +kernel

private theorem R10e04_row_15 : pack 32 (R10e04_digit 15)=R10e04_rowCode 15 := by decide +kernel

private theorem R10e04_row_16 : pack 32 (R10e04_digit 16)=R10e04_rowCode 16 := by decide +kernel

private theorem R10e04_row_17 : pack 32 (R10e04_digit 17)=R10e04_rowCode 17 := by decide +kernel

private theorem R10e04_row_18 : pack 32 (R10e04_digit 18)=R10e04_rowCode 18 := by decide +kernel

private theorem R10e04_row_19 : pack 32 (R10e04_digit 19)=R10e04_rowCode 19 := by decide +kernel

private theorem R10e04_row_20 : pack 32 (R10e04_digit 20)=R10e04_rowCode 20 := by decide +kernel

private theorem R10e04_row_21 : pack 32 (R10e04_digit 21)=R10e04_rowCode 21 := by decide +kernel

theorem R10e04_row_binding : ∀ i : Fin 22,pack 32 (R10e04_digit i)=R10e04_rowCode i := by
  intro i
  fin_cases i
  · exact R10e04_row_00
  · exact R10e04_row_01
  · exact R10e04_row_02
  · exact R10e04_row_03
  · exact R10e04_row_04
  · exact R10e04_row_05
  · exact R10e04_row_06
  · exact R10e04_row_07
  · exact R10e04_row_08
  · exact R10e04_row_09
  · exact R10e04_row_10
  · exact R10e04_row_11
  · exact R10e04_row_12
  · exact R10e04_row_13
  · exact R10e04_row_14
  · exact R10e04_row_15
  · exact R10e04_row_16
  · exact R10e04_row_17
  · exact R10e04_row_18
  · exact R10e04_row_19
  · exact R10e04_row_20
  · exact R10e04_row_21

private theorem R10e04_column_00 : reversePack 32 (fun j : Fin 22 => R10e04_digit j 0)=R10e04_columnCode 0 := by decide +kernel

private theorem R10e04_column_01 : reversePack 32 (fun j : Fin 22 => R10e04_digit j 1)=R10e04_columnCode 1 := by decide +kernel

private theorem R10e04_column_02 : reversePack 32 (fun j : Fin 22 => R10e04_digit j 2)=R10e04_columnCode 2 := by decide +kernel

private theorem R10e04_column_03 : reversePack 32 (fun j : Fin 22 => R10e04_digit j 3)=R10e04_columnCode 3 := by decide +kernel

private theorem R10e04_column_04 : reversePack 32 (fun j : Fin 22 => R10e04_digit j 4)=R10e04_columnCode 4 := by decide +kernel

private theorem R10e04_column_05 : reversePack 32 (fun j : Fin 22 => R10e04_digit j 5)=R10e04_columnCode 5 := by decide +kernel

private theorem R10e04_column_06 : reversePack 32 (fun j : Fin 22 => R10e04_digit j 6)=R10e04_columnCode 6 := by decide +kernel

private theorem R10e04_column_07 : reversePack 32 (fun j : Fin 22 => R10e04_digit j 7)=R10e04_columnCode 7 := by decide +kernel

private theorem R10e04_column_08 : reversePack 32 (fun j : Fin 22 => R10e04_digit j 8)=R10e04_columnCode 8 := by decide +kernel

private theorem R10e04_column_09 : reversePack 32 (fun j : Fin 22 => R10e04_digit j 9)=R10e04_columnCode 9 := by decide +kernel

private theorem R10e04_column_10 : reversePack 32 (fun j : Fin 22 => R10e04_digit j 10)=R10e04_columnCode 10 := by decide +kernel

private theorem R10e04_column_11 : reversePack 32 (fun j : Fin 22 => R10e04_digit j 11)=R10e04_columnCode 11 := by decide +kernel

private theorem R10e04_column_12 : reversePack 32 (fun j : Fin 22 => R10e04_digit j 12)=R10e04_columnCode 12 := by decide +kernel

private theorem R10e04_column_13 : reversePack 32 (fun j : Fin 22 => R10e04_digit j 13)=R10e04_columnCode 13 := by decide +kernel

private theorem R10e04_column_14 : reversePack 32 (fun j : Fin 22 => R10e04_digit j 14)=R10e04_columnCode 14 := by decide +kernel

private theorem R10e04_column_15 : reversePack 32 (fun j : Fin 22 => R10e04_digit j 15)=R10e04_columnCode 15 := by decide +kernel

private theorem R10e04_column_16 : reversePack 32 (fun j : Fin 22 => R10e04_digit j 16)=R10e04_columnCode 16 := by decide +kernel

private theorem R10e04_column_17 : reversePack 32 (fun j : Fin 22 => R10e04_digit j 17)=R10e04_columnCode 17 := by decide +kernel

private theorem R10e04_column_18 : reversePack 32 (fun j : Fin 22 => R10e04_digit j 18)=R10e04_columnCode 18 := by decide +kernel

private theorem R10e04_column_19 : reversePack 32 (fun j : Fin 22 => R10e04_digit j 19)=R10e04_columnCode 19 := by decide +kernel

private theorem R10e04_column_20 : reversePack 32 (fun j : Fin 22 => R10e04_digit j 20)=R10e04_columnCode 20 := by decide +kernel

private theorem R10e04_column_21 : reversePack 32 (fun j : Fin 22 => R10e04_digit j 21)=R10e04_columnCode 21 := by decide +kernel

theorem R10e04_column_binding : ∀ i : Fin 22,reversePack 32 (fun j : Fin 22 => R10e04_digit j i)=R10e04_columnCode i := by
  intro i
  fin_cases i
  · exact R10e04_column_00
  · exact R10e04_column_01
  · exact R10e04_column_02
  · exact R10e04_column_03
  · exact R10e04_column_04
  · exact R10e04_column_05
  · exact R10e04_column_06
  · exact R10e04_column_07
  · exact R10e04_column_08
  · exact R10e04_column_09
  · exact R10e04_column_10
  · exact R10e04_column_11
  · exact R10e04_column_12
  · exact R10e04_column_13
  · exact R10e04_column_14
  · exact R10e04_column_15
  · exact R10e04_column_16
  · exact R10e04_column_17
  · exact R10e04_column_18
  · exact R10e04_column_19
  · exact R10e04_column_20
  · exact R10e04_column_21

def R10e04_data : PackedData 22 2 32 where
  raw := R10e04_digit
  digit_lt := R10e04_bound
  rowCode := R10e04_rowCode
  columnCode := R10e04_columnCode
  row_binding := R10e04_row_binding
  column_binding := R10e04_column_binding

def R10e06_lowColumnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1565826
  | 1 => 1983882
  | 2 => 2485540
  | 3 => 3976555
  | 4 => 1833784
  | 5 => 369861
  | 6 => 2657253
  | 7 => 230674
  | 8 => 2978278
  | 9 => 3442831
  | 10 => 647011
  | 11 => 3954538
  | 12 => 1670671
  | 13 => 934212
  | 14 => 1147934
  | 15 => 164655
  | 16 => 23368
  | 17 => 2926667
  | 18 => 2757419
  | 19 => 908858
  | 20 => 65888
  | 21 => 2524765
  | _ => 0

def R10e06_rowCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 40566095870748939841850147110912
  | 1 => 40890745883358813399610851361
  | 2 => 40564819246300910777506092549120
  | 3 => 40605711162112518148889510969376
  | 4 => 40604433289741064637443046637568
  | 5 => 1308502659303615969323048272896
  | 6 => 41832509702120548176098934947840
  | 7 => 36284991012897
  | 8 => 1268889787009196903337229845536
  | 9 => 40605672475305699950755117531136
  | 10 => 40604433289742254713644611830817
  | 11 => 39653975810333534149497881600
  | 12 => 40853230223427241001891135488
  | 13 => 38685627380590737743709185
  | 14 => 39615290221035348874411115553
  | 15 => 40604472013146225329619185206273
  | 16 => 1307264682667107239549306143745
  | 17 => 40566057185158451579308343296033
  | 18 => 40604471974223630238053220516897
  | 19 => 40890706960728782654799904800
  | 20 => 1181780606203410284577
  | 21 => 40566095832968889961384968750080
  | _ => 0

def R10e06_columnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1267650601408857052146113216544
  | 1 => 1268888541485035919467812520992
  | 2 => 39615290219882427405270286337
  | 3 => 41833708994312537751197371630625
  | 4 => 1277834629380234908949021728
  | 5 => 40604433327520032530263485480960
  | 6 => 40604434536483863650548028802049
  | 7 => 1267689285891386586575840215040
  | 8 => 1307265929407598193062919046145
  | 9 => 41873321830008580545081268797473
  | 10 => 41832471054274405326546333074432
  | 11 => 1268889787010348733025715520545
  | 12 => 41873321828829177910982686540832
  | 13 => 39614119072957519935713608704
  | 14 => 1308541307150910647500091162656
  | 15 => 41873323037791853822745152323584
  | 16 => 1237977856264814002725453824
  | 17 => 41833707785349788619623758857217
  | 18 => 41833708956534721689131678696449
  | 19 => 1268928434820752175955739444224
  | 20 => 1246741644965733789073408
  | 21 => 40605709952006106878359626612737
  | _ => 0

def R10e06_digit (i j : Fin 22) : ℕ := packedDigit 1 (R10e06_lowColumnCode j) i.val

private theorem R10e06_bound_00 : ∀ j : Fin 22,R10e06_digit 0 j<2 := by decide +kernel

private theorem R10e06_bound_01 : ∀ j : Fin 22,R10e06_digit 1 j<2 := by decide +kernel

private theorem R10e06_bound_02 : ∀ j : Fin 22,R10e06_digit 2 j<2 := by decide +kernel

private theorem R10e06_bound_03 : ∀ j : Fin 22,R10e06_digit 3 j<2 := by decide +kernel

private theorem R10e06_bound_04 : ∀ j : Fin 22,R10e06_digit 4 j<2 := by decide +kernel

private theorem R10e06_bound_05 : ∀ j : Fin 22,R10e06_digit 5 j<2 := by decide +kernel

private theorem R10e06_bound_06 : ∀ j : Fin 22,R10e06_digit 6 j<2 := by decide +kernel

private theorem R10e06_bound_07 : ∀ j : Fin 22,R10e06_digit 7 j<2 := by decide +kernel

private theorem R10e06_bound_08 : ∀ j : Fin 22,R10e06_digit 8 j<2 := by decide +kernel

private theorem R10e06_bound_09 : ∀ j : Fin 22,R10e06_digit 9 j<2 := by decide +kernel

private theorem R10e06_bound_10 : ∀ j : Fin 22,R10e06_digit 10 j<2 := by decide +kernel

private theorem R10e06_bound_11 : ∀ j : Fin 22,R10e06_digit 11 j<2 := by decide +kernel

private theorem R10e06_bound_12 : ∀ j : Fin 22,R10e06_digit 12 j<2 := by decide +kernel

private theorem R10e06_bound_13 : ∀ j : Fin 22,R10e06_digit 13 j<2 := by decide +kernel

private theorem R10e06_bound_14 : ∀ j : Fin 22,R10e06_digit 14 j<2 := by decide +kernel

private theorem R10e06_bound_15 : ∀ j : Fin 22,R10e06_digit 15 j<2 := by decide +kernel

private theorem R10e06_bound_16 : ∀ j : Fin 22,R10e06_digit 16 j<2 := by decide +kernel

private theorem R10e06_bound_17 : ∀ j : Fin 22,R10e06_digit 17 j<2 := by decide +kernel

private theorem R10e06_bound_18 : ∀ j : Fin 22,R10e06_digit 18 j<2 := by decide +kernel

private theorem R10e06_bound_19 : ∀ j : Fin 22,R10e06_digit 19 j<2 := by decide +kernel

private theorem R10e06_bound_20 : ∀ j : Fin 22,R10e06_digit 20 j<2 := by decide +kernel

private theorem R10e06_bound_21 : ∀ j : Fin 22,R10e06_digit 21 j<2 := by decide +kernel

theorem R10e06_bound : ∀ i j : Fin 22,R10e06_digit i j<2 := by
  intro i j
  fin_cases i
  · exact R10e06_bound_00 j
  · exact R10e06_bound_01 j
  · exact R10e06_bound_02 j
  · exact R10e06_bound_03 j
  · exact R10e06_bound_04 j
  · exact R10e06_bound_05 j
  · exact R10e06_bound_06 j
  · exact R10e06_bound_07 j
  · exact R10e06_bound_08 j
  · exact R10e06_bound_09 j
  · exact R10e06_bound_10 j
  · exact R10e06_bound_11 j
  · exact R10e06_bound_12 j
  · exact R10e06_bound_13 j
  · exact R10e06_bound_14 j
  · exact R10e06_bound_15 j
  · exact R10e06_bound_16 j
  · exact R10e06_bound_17 j
  · exact R10e06_bound_18 j
  · exact R10e06_bound_19 j
  · exact R10e06_bound_20 j
  · exact R10e06_bound_21 j

private theorem R10e06_row_00 : pack 32 (R10e06_digit 0)=R10e06_rowCode 0 := by decide +kernel

private theorem R10e06_row_01 : pack 32 (R10e06_digit 1)=R10e06_rowCode 1 := by decide +kernel

private theorem R10e06_row_02 : pack 32 (R10e06_digit 2)=R10e06_rowCode 2 := by decide +kernel

private theorem R10e06_row_03 : pack 32 (R10e06_digit 3)=R10e06_rowCode 3 := by decide +kernel

private theorem R10e06_row_04 : pack 32 (R10e06_digit 4)=R10e06_rowCode 4 := by decide +kernel

private theorem R10e06_row_05 : pack 32 (R10e06_digit 5)=R10e06_rowCode 5 := by decide +kernel

private theorem R10e06_row_06 : pack 32 (R10e06_digit 6)=R10e06_rowCode 6 := by decide +kernel

private theorem R10e06_row_07 : pack 32 (R10e06_digit 7)=R10e06_rowCode 7 := by decide +kernel

private theorem R10e06_row_08 : pack 32 (R10e06_digit 8)=R10e06_rowCode 8 := by decide +kernel

private theorem R10e06_row_09 : pack 32 (R10e06_digit 9)=R10e06_rowCode 9 := by decide +kernel

private theorem R10e06_row_10 : pack 32 (R10e06_digit 10)=R10e06_rowCode 10 := by decide +kernel

private theorem R10e06_row_11 : pack 32 (R10e06_digit 11)=R10e06_rowCode 11 := by decide +kernel

private theorem R10e06_row_12 : pack 32 (R10e06_digit 12)=R10e06_rowCode 12 := by decide +kernel

private theorem R10e06_row_13 : pack 32 (R10e06_digit 13)=R10e06_rowCode 13 := by decide +kernel

private theorem R10e06_row_14 : pack 32 (R10e06_digit 14)=R10e06_rowCode 14 := by decide +kernel

private theorem R10e06_row_15 : pack 32 (R10e06_digit 15)=R10e06_rowCode 15 := by decide +kernel

private theorem R10e06_row_16 : pack 32 (R10e06_digit 16)=R10e06_rowCode 16 := by decide +kernel

private theorem R10e06_row_17 : pack 32 (R10e06_digit 17)=R10e06_rowCode 17 := by decide +kernel

private theorem R10e06_row_18 : pack 32 (R10e06_digit 18)=R10e06_rowCode 18 := by decide +kernel

private theorem R10e06_row_19 : pack 32 (R10e06_digit 19)=R10e06_rowCode 19 := by decide +kernel

private theorem R10e06_row_20 : pack 32 (R10e06_digit 20)=R10e06_rowCode 20 := by decide +kernel

private theorem R10e06_row_21 : pack 32 (R10e06_digit 21)=R10e06_rowCode 21 := by decide +kernel

theorem R10e06_row_binding : ∀ i : Fin 22,pack 32 (R10e06_digit i)=R10e06_rowCode i := by
  intro i
  fin_cases i
  · exact R10e06_row_00
  · exact R10e06_row_01
  · exact R10e06_row_02
  · exact R10e06_row_03
  · exact R10e06_row_04
  · exact R10e06_row_05
  · exact R10e06_row_06
  · exact R10e06_row_07
  · exact R10e06_row_08
  · exact R10e06_row_09
  · exact R10e06_row_10
  · exact R10e06_row_11
  · exact R10e06_row_12
  · exact R10e06_row_13
  · exact R10e06_row_14
  · exact R10e06_row_15
  · exact R10e06_row_16
  · exact R10e06_row_17
  · exact R10e06_row_18
  · exact R10e06_row_19
  · exact R10e06_row_20
  · exact R10e06_row_21

private theorem R10e06_column_00 : reversePack 32 (fun j : Fin 22 => R10e06_digit j 0)=R10e06_columnCode 0 := by decide +kernel

private theorem R10e06_column_01 : reversePack 32 (fun j : Fin 22 => R10e06_digit j 1)=R10e06_columnCode 1 := by decide +kernel

private theorem R10e06_column_02 : reversePack 32 (fun j : Fin 22 => R10e06_digit j 2)=R10e06_columnCode 2 := by decide +kernel

private theorem R10e06_column_03 : reversePack 32 (fun j : Fin 22 => R10e06_digit j 3)=R10e06_columnCode 3 := by decide +kernel

private theorem R10e06_column_04 : reversePack 32 (fun j : Fin 22 => R10e06_digit j 4)=R10e06_columnCode 4 := by decide +kernel

private theorem R10e06_column_05 : reversePack 32 (fun j : Fin 22 => R10e06_digit j 5)=R10e06_columnCode 5 := by decide +kernel

private theorem R10e06_column_06 : reversePack 32 (fun j : Fin 22 => R10e06_digit j 6)=R10e06_columnCode 6 := by decide +kernel

private theorem R10e06_column_07 : reversePack 32 (fun j : Fin 22 => R10e06_digit j 7)=R10e06_columnCode 7 := by decide +kernel

private theorem R10e06_column_08 : reversePack 32 (fun j : Fin 22 => R10e06_digit j 8)=R10e06_columnCode 8 := by decide +kernel

private theorem R10e06_column_09 : reversePack 32 (fun j : Fin 22 => R10e06_digit j 9)=R10e06_columnCode 9 := by decide +kernel

private theorem R10e06_column_10 : reversePack 32 (fun j : Fin 22 => R10e06_digit j 10)=R10e06_columnCode 10 := by decide +kernel

private theorem R10e06_column_11 : reversePack 32 (fun j : Fin 22 => R10e06_digit j 11)=R10e06_columnCode 11 := by decide +kernel

private theorem R10e06_column_12 : reversePack 32 (fun j : Fin 22 => R10e06_digit j 12)=R10e06_columnCode 12 := by decide +kernel

private theorem R10e06_column_13 : reversePack 32 (fun j : Fin 22 => R10e06_digit j 13)=R10e06_columnCode 13 := by decide +kernel

private theorem R10e06_column_14 : reversePack 32 (fun j : Fin 22 => R10e06_digit j 14)=R10e06_columnCode 14 := by decide +kernel

private theorem R10e06_column_15 : reversePack 32 (fun j : Fin 22 => R10e06_digit j 15)=R10e06_columnCode 15 := by decide +kernel

private theorem R10e06_column_16 : reversePack 32 (fun j : Fin 22 => R10e06_digit j 16)=R10e06_columnCode 16 := by decide +kernel

private theorem R10e06_column_17 : reversePack 32 (fun j : Fin 22 => R10e06_digit j 17)=R10e06_columnCode 17 := by decide +kernel

private theorem R10e06_column_18 : reversePack 32 (fun j : Fin 22 => R10e06_digit j 18)=R10e06_columnCode 18 := by decide +kernel

private theorem R10e06_column_19 : reversePack 32 (fun j : Fin 22 => R10e06_digit j 19)=R10e06_columnCode 19 := by decide +kernel

private theorem R10e06_column_20 : reversePack 32 (fun j : Fin 22 => R10e06_digit j 20)=R10e06_columnCode 20 := by decide +kernel

private theorem R10e06_column_21 : reversePack 32 (fun j : Fin 22 => R10e06_digit j 21)=R10e06_columnCode 21 := by decide +kernel

theorem R10e06_column_binding : ∀ i : Fin 22,reversePack 32 (fun j : Fin 22 => R10e06_digit j i)=R10e06_columnCode i := by
  intro i
  fin_cases i
  · exact R10e06_column_00
  · exact R10e06_column_01
  · exact R10e06_column_02
  · exact R10e06_column_03
  · exact R10e06_column_04
  · exact R10e06_column_05
  · exact R10e06_column_06
  · exact R10e06_column_07
  · exact R10e06_column_08
  · exact R10e06_column_09
  · exact R10e06_column_10
  · exact R10e06_column_11
  · exact R10e06_column_12
  · exact R10e06_column_13
  · exact R10e06_column_14
  · exact R10e06_column_15
  · exact R10e06_column_16
  · exact R10e06_column_17
  · exact R10e06_column_18
  · exact R10e06_column_19
  · exact R10e06_column_20
  · exact R10e06_column_21

def R10e06_data : PackedData 22 2 32 where
  raw := R10e06_digit
  digit_lt := R10e06_bound
  rowCode := R10e06_rowCode
  columnCode := R10e06_columnCode
  row_binding := R10e06_row_binding
  column_binding := R10e06_column_binding

end SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoCaches12
