import SymmetricSubgroupAsymptotics.MatrixKroneckerProductReflection
import Mathlib.Tactic.FinCases

/-! Fixed Co2 binary22 shared caches. Every digit and pack binding is kernel checked. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoCaches06
open MatrixKroneckerProductReflection MatrixKroneckerDotReflection
open MatrixNaturalRowDotReflection SmallNaturalMatrixProductReflection

def R07p08_lowColumnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 910395
  | 1 => 2958218
  | 2 => 2882331
  | 3 => 4118578
  | 4 => 1390700
  | 5 => 846147
  | 6 => 600167
  | 7 => 2191834
  | 8 => 682087
  | 9 => 830225
  | 10 => 862539
  | 11 => 2123838
  | 12 => 3709417
  | 13 => 1389453
  | 14 => 2537620
  | 15 => 3590816
  | 16 => 2852914
  | 17 => 3412002
  | 18 => 2468797
  | 19 => 2697270
  | 20 => 600118
  | 21 => 3571716
  | _ => 0

def R07p08_rowCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1237940077332952111822930945
  | 1 => 1307304576037446008888144987169
  | 2 => 41873321830045508937225312665600
  | 3 => 1237940077368944658211669025
  | 4 => 1308503831631094249930711139329
  | 5 => 1308542553856815047690513580033
  | 6 => 1154048539493400576
  | 7 => 1237979036855273635857825824
  | 8 => 1237940077332951045597299744
  | 9 => 1237977855110766563852026912
  | 10 => 1
  | 11 => 1308503869411180161358646772736
  | 12 => 38686844865698537388672000
  | 13 => 1308502622742169250449482318881
  | 14 => 37778967892888085627905
  | 15 => 40566058395229122283162161939457
  | 16 => 1308503830487361179280309486625
  | 17 => 40564820455188683947297761952768
  | 18 => 40566095871965272029209297977377
  | 19 => 1307265890412335268612154623009
  | 20 => 40564857930746546788637281910784
  | 21 => 40605711162112518113739497571360
  | _ => 0

def R07p08_columnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 41833747642122938942360867865600
  | 1 => 1268888541486152813240584799233
  | 2 => 41833746433235130869670980092929
  | 3 => 1267690494780277845379182003233
  | 4 => 40853268001170188841831661600
  | 5 => 41832469845347396727530638574592
  | 6 => 41872085135493455022773766194176
  | 7 => 1268927264890159458045462052865
  | 8 => 41872085135493455022808093426688
  | 9 => 40564857892967616052680611365888
  | 10 => 41833707785386682107770137773056
  | 11 => 1308542516076695360364917817345
  | 12 => 40566058395264863975705921192993
  | 13 => 40605671229818396463619528228896
  | 14 => 39652768063952619832639258625
  | 15 => 1210107565282786534260769
  | 16 => 1267690494780277810160483697665
  | 17 => 1267651809154049051310250033185
  | 18 => 40605711124370444837098902028289
  | 19 => 1307304576037409980055692510209
  | 20 => 1307304576037409980055692510208
  | 21 => 39614081257132168797846798369
  | _ => 0

def R07p08_digit (i j : Fin 22) : ℕ := packedDigit 1 (R07p08_lowColumnCode j) i.val

private theorem R07p08_bound_00 : ∀ j : Fin 22,R07p08_digit 0 j<2 := by decide +kernel

private theorem R07p08_bound_01 : ∀ j : Fin 22,R07p08_digit 1 j<2 := by decide +kernel

private theorem R07p08_bound_02 : ∀ j : Fin 22,R07p08_digit 2 j<2 := by decide +kernel

private theorem R07p08_bound_03 : ∀ j : Fin 22,R07p08_digit 3 j<2 := by decide +kernel

private theorem R07p08_bound_04 : ∀ j : Fin 22,R07p08_digit 4 j<2 := by decide +kernel

private theorem R07p08_bound_05 : ∀ j : Fin 22,R07p08_digit 5 j<2 := by decide +kernel

private theorem R07p08_bound_06 : ∀ j : Fin 22,R07p08_digit 6 j<2 := by decide +kernel

private theorem R07p08_bound_07 : ∀ j : Fin 22,R07p08_digit 7 j<2 := by decide +kernel

private theorem R07p08_bound_08 : ∀ j : Fin 22,R07p08_digit 8 j<2 := by decide +kernel

private theorem R07p08_bound_09 : ∀ j : Fin 22,R07p08_digit 9 j<2 := by decide +kernel

private theorem R07p08_bound_10 : ∀ j : Fin 22,R07p08_digit 10 j<2 := by decide +kernel

private theorem R07p08_bound_11 : ∀ j : Fin 22,R07p08_digit 11 j<2 := by decide +kernel

private theorem R07p08_bound_12 : ∀ j : Fin 22,R07p08_digit 12 j<2 := by decide +kernel

private theorem R07p08_bound_13 : ∀ j : Fin 22,R07p08_digit 13 j<2 := by decide +kernel

private theorem R07p08_bound_14 : ∀ j : Fin 22,R07p08_digit 14 j<2 := by decide +kernel

private theorem R07p08_bound_15 : ∀ j : Fin 22,R07p08_digit 15 j<2 := by decide +kernel

private theorem R07p08_bound_16 : ∀ j : Fin 22,R07p08_digit 16 j<2 := by decide +kernel

private theorem R07p08_bound_17 : ∀ j : Fin 22,R07p08_digit 17 j<2 := by decide +kernel

private theorem R07p08_bound_18 : ∀ j : Fin 22,R07p08_digit 18 j<2 := by decide +kernel

private theorem R07p08_bound_19 : ∀ j : Fin 22,R07p08_digit 19 j<2 := by decide +kernel

private theorem R07p08_bound_20 : ∀ j : Fin 22,R07p08_digit 20 j<2 := by decide +kernel

private theorem R07p08_bound_21 : ∀ j : Fin 22,R07p08_digit 21 j<2 := by decide +kernel

theorem R07p08_bound : ∀ i j : Fin 22,R07p08_digit i j<2 := by
  intro i j
  fin_cases i
  · exact R07p08_bound_00 j
  · exact R07p08_bound_01 j
  · exact R07p08_bound_02 j
  · exact R07p08_bound_03 j
  · exact R07p08_bound_04 j
  · exact R07p08_bound_05 j
  · exact R07p08_bound_06 j
  · exact R07p08_bound_07 j
  · exact R07p08_bound_08 j
  · exact R07p08_bound_09 j
  · exact R07p08_bound_10 j
  · exact R07p08_bound_11 j
  · exact R07p08_bound_12 j
  · exact R07p08_bound_13 j
  · exact R07p08_bound_14 j
  · exact R07p08_bound_15 j
  · exact R07p08_bound_16 j
  · exact R07p08_bound_17 j
  · exact R07p08_bound_18 j
  · exact R07p08_bound_19 j
  · exact R07p08_bound_20 j
  · exact R07p08_bound_21 j

private theorem R07p08_row_00 : pack 32 (R07p08_digit 0)=R07p08_rowCode 0 := by decide +kernel

private theorem R07p08_row_01 : pack 32 (R07p08_digit 1)=R07p08_rowCode 1 := by decide +kernel

private theorem R07p08_row_02 : pack 32 (R07p08_digit 2)=R07p08_rowCode 2 := by decide +kernel

private theorem R07p08_row_03 : pack 32 (R07p08_digit 3)=R07p08_rowCode 3 := by decide +kernel

private theorem R07p08_row_04 : pack 32 (R07p08_digit 4)=R07p08_rowCode 4 := by decide +kernel

private theorem R07p08_row_05 : pack 32 (R07p08_digit 5)=R07p08_rowCode 5 := by decide +kernel

private theorem R07p08_row_06 : pack 32 (R07p08_digit 6)=R07p08_rowCode 6 := by decide +kernel

private theorem R07p08_row_07 : pack 32 (R07p08_digit 7)=R07p08_rowCode 7 := by decide +kernel

private theorem R07p08_row_08 : pack 32 (R07p08_digit 8)=R07p08_rowCode 8 := by decide +kernel

private theorem R07p08_row_09 : pack 32 (R07p08_digit 9)=R07p08_rowCode 9 := by decide +kernel

private theorem R07p08_row_10 : pack 32 (R07p08_digit 10)=R07p08_rowCode 10 := by decide +kernel

private theorem R07p08_row_11 : pack 32 (R07p08_digit 11)=R07p08_rowCode 11 := by decide +kernel

private theorem R07p08_row_12 : pack 32 (R07p08_digit 12)=R07p08_rowCode 12 := by decide +kernel

private theorem R07p08_row_13 : pack 32 (R07p08_digit 13)=R07p08_rowCode 13 := by decide +kernel

private theorem R07p08_row_14 : pack 32 (R07p08_digit 14)=R07p08_rowCode 14 := by decide +kernel

private theorem R07p08_row_15 : pack 32 (R07p08_digit 15)=R07p08_rowCode 15 := by decide +kernel

private theorem R07p08_row_16 : pack 32 (R07p08_digit 16)=R07p08_rowCode 16 := by decide +kernel

private theorem R07p08_row_17 : pack 32 (R07p08_digit 17)=R07p08_rowCode 17 := by decide +kernel

private theorem R07p08_row_18 : pack 32 (R07p08_digit 18)=R07p08_rowCode 18 := by decide +kernel

private theorem R07p08_row_19 : pack 32 (R07p08_digit 19)=R07p08_rowCode 19 := by decide +kernel

private theorem R07p08_row_20 : pack 32 (R07p08_digit 20)=R07p08_rowCode 20 := by decide +kernel

private theorem R07p08_row_21 : pack 32 (R07p08_digit 21)=R07p08_rowCode 21 := by decide +kernel

theorem R07p08_row_binding : ∀ i : Fin 22,pack 32 (R07p08_digit i)=R07p08_rowCode i := by
  intro i
  fin_cases i
  · exact R07p08_row_00
  · exact R07p08_row_01
  · exact R07p08_row_02
  · exact R07p08_row_03
  · exact R07p08_row_04
  · exact R07p08_row_05
  · exact R07p08_row_06
  · exact R07p08_row_07
  · exact R07p08_row_08
  · exact R07p08_row_09
  · exact R07p08_row_10
  · exact R07p08_row_11
  · exact R07p08_row_12
  · exact R07p08_row_13
  · exact R07p08_row_14
  · exact R07p08_row_15
  · exact R07p08_row_16
  · exact R07p08_row_17
  · exact R07p08_row_18
  · exact R07p08_row_19
  · exact R07p08_row_20
  · exact R07p08_row_21

private theorem R07p08_column_00 : reversePack 32 (fun j : Fin 22 => R07p08_digit j 0)=R07p08_columnCode 0 := by decide +kernel

private theorem R07p08_column_01 : reversePack 32 (fun j : Fin 22 => R07p08_digit j 1)=R07p08_columnCode 1 := by decide +kernel

private theorem R07p08_column_02 : reversePack 32 (fun j : Fin 22 => R07p08_digit j 2)=R07p08_columnCode 2 := by decide +kernel

private theorem R07p08_column_03 : reversePack 32 (fun j : Fin 22 => R07p08_digit j 3)=R07p08_columnCode 3 := by decide +kernel

private theorem R07p08_column_04 : reversePack 32 (fun j : Fin 22 => R07p08_digit j 4)=R07p08_columnCode 4 := by decide +kernel

private theorem R07p08_column_05 : reversePack 32 (fun j : Fin 22 => R07p08_digit j 5)=R07p08_columnCode 5 := by decide +kernel

private theorem R07p08_column_06 : reversePack 32 (fun j : Fin 22 => R07p08_digit j 6)=R07p08_columnCode 6 := by decide +kernel

private theorem R07p08_column_07 : reversePack 32 (fun j : Fin 22 => R07p08_digit j 7)=R07p08_columnCode 7 := by decide +kernel

private theorem R07p08_column_08 : reversePack 32 (fun j : Fin 22 => R07p08_digit j 8)=R07p08_columnCode 8 := by decide +kernel

private theorem R07p08_column_09 : reversePack 32 (fun j : Fin 22 => R07p08_digit j 9)=R07p08_columnCode 9 := by decide +kernel

private theorem R07p08_column_10 : reversePack 32 (fun j : Fin 22 => R07p08_digit j 10)=R07p08_columnCode 10 := by decide +kernel

private theorem R07p08_column_11 : reversePack 32 (fun j : Fin 22 => R07p08_digit j 11)=R07p08_columnCode 11 := by decide +kernel

private theorem R07p08_column_12 : reversePack 32 (fun j : Fin 22 => R07p08_digit j 12)=R07p08_columnCode 12 := by decide +kernel

private theorem R07p08_column_13 : reversePack 32 (fun j : Fin 22 => R07p08_digit j 13)=R07p08_columnCode 13 := by decide +kernel

private theorem R07p08_column_14 : reversePack 32 (fun j : Fin 22 => R07p08_digit j 14)=R07p08_columnCode 14 := by decide +kernel

private theorem R07p08_column_15 : reversePack 32 (fun j : Fin 22 => R07p08_digit j 15)=R07p08_columnCode 15 := by decide +kernel

private theorem R07p08_column_16 : reversePack 32 (fun j : Fin 22 => R07p08_digit j 16)=R07p08_columnCode 16 := by decide +kernel

private theorem R07p08_column_17 : reversePack 32 (fun j : Fin 22 => R07p08_digit j 17)=R07p08_columnCode 17 := by decide +kernel

private theorem R07p08_column_18 : reversePack 32 (fun j : Fin 22 => R07p08_digit j 18)=R07p08_columnCode 18 := by decide +kernel

private theorem R07p08_column_19 : reversePack 32 (fun j : Fin 22 => R07p08_digit j 19)=R07p08_columnCode 19 := by decide +kernel

private theorem R07p08_column_20 : reversePack 32 (fun j : Fin 22 => R07p08_digit j 20)=R07p08_columnCode 20 := by decide +kernel

private theorem R07p08_column_21 : reversePack 32 (fun j : Fin 22 => R07p08_digit j 21)=R07p08_columnCode 21 := by decide +kernel

theorem R07p08_column_binding : ∀ i : Fin 22,reversePack 32 (fun j : Fin 22 => R07p08_digit j i)=R07p08_columnCode i := by
  intro i
  fin_cases i
  · exact R07p08_column_00
  · exact R07p08_column_01
  · exact R07p08_column_02
  · exact R07p08_column_03
  · exact R07p08_column_04
  · exact R07p08_column_05
  · exact R07p08_column_06
  · exact R07p08_column_07
  · exact R07p08_column_08
  · exact R07p08_column_09
  · exact R07p08_column_10
  · exact R07p08_column_11
  · exact R07p08_column_12
  · exact R07p08_column_13
  · exact R07p08_column_14
  · exact R07p08_column_15
  · exact R07p08_column_16
  · exact R07p08_column_17
  · exact R07p08_column_18
  · exact R07p08_column_19
  · exact R07p08_column_20
  · exact R07p08_column_21

def R07p08_data : PackedData 22 2 32 where
  raw := R07p08_digit
  digit_lt := R07p08_bound
  rowCode := R07p08_rowCode
  columnCode := R07p08_columnCode
  row_binding := R07p08_row_binding
  column_binding := R07p08_column_binding

def R07p09_lowColumnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 2279858
  | 1 => 1215416
  | 2 => 3054562
  | 3 => 3455682
  | 4 => 677871
  | 5 => 3860875
  | 6 => 2171823
  | 7 => 2638707
  | 8 => 3980059
  | 9 => 3341081
  | 10 => 2792383
  | 11 => 1642662
  | 12 => 51816
  | 13 => 2339800
  | 14 => 3821815
  | 15 => 34874
  | 16 => 600118
  | 17 => 957122
  | 18 => 446634
  | 19 => 1474564
  | 20 => 2097152
  | 21 => 3416064
  | _ => 0

def R07p09_rowCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1180592782936669945856
  | 1 => 1277873550893302544142992385
  | 2 => 39615291363580558841358581760
  | 3 => 1237977856264815068985688096
  | 4 => 1247922237748669317120033
  | 5 => 1239187925818554815614026785
  | 6 => 38686844865698537388672000
  | 7 => 1276626883035311971354313761
  | 8 => 36894650366677746721
  | 9 => 38685664275240004841669664
  | 10 => 1048576
  | 11 => 39932332133229408358007841
  | 12 => 1276626883035348254130734080
  | 13 => 40564820416266053986956087427072
  | 14 => 1237941221029957715683704833
  | 15 => 40890744739624651998273504289
  | 16 => 1208962749131574686515200
  | 17 => 40890708140131487154405639201
  | 18 => 40605709914225986066199275930624
  | 19 => 39895732676059311008384000
  | 20 => 40604433289741100702489622118432
  | 21 => 41832469808749056520475293811713
  | _ => 0

def R07p09_columnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1267690495997762919059640287233
  | 1 => 1277835809971819308083314720
  | 2 => 1267651848151620070537830630401
  | 3 => 1267650639188906968860747399201
  | 4 => 41873323076751413370434402386944
  | 5 => 41833707748788341865565788308513
  | 6 => 41873323038972445444561034018817
  | 7 => 41832509739900595804797518480385
  | 8 => 41833746433235130869636585784353
  | 9 => 40566095833006901468174243332129
  | 10 => 41873361724598674272680433157121
  | 11 => 1307265891591772840824466834464
  | 12 => 1239186745190905301182709760
  | 13 => 1276664663082978020080746497
  | 14 => 41872123822300273219844048946209
  | 15 => 1268928434819563190435348217856
  | 16 => 1307304576037409980055692510208
  | 17 => 1267650639188906967761236820992
  | 18 => 1268889750373926052337994989568
  | 19 => 39614081257132168797846798368
  | 20 => 1
  | 21 => 1099511660577
  | _ => 0

def R07p09_digit (i j : Fin 22) : ℕ := packedDigit 1 (R07p09_lowColumnCode j) i.val

private theorem R07p09_bound_00 : ∀ j : Fin 22,R07p09_digit 0 j<2 := by decide +kernel

private theorem R07p09_bound_01 : ∀ j : Fin 22,R07p09_digit 1 j<2 := by decide +kernel

private theorem R07p09_bound_02 : ∀ j : Fin 22,R07p09_digit 2 j<2 := by decide +kernel

private theorem R07p09_bound_03 : ∀ j : Fin 22,R07p09_digit 3 j<2 := by decide +kernel

private theorem R07p09_bound_04 : ∀ j : Fin 22,R07p09_digit 4 j<2 := by decide +kernel

private theorem R07p09_bound_05 : ∀ j : Fin 22,R07p09_digit 5 j<2 := by decide +kernel

private theorem R07p09_bound_06 : ∀ j : Fin 22,R07p09_digit 6 j<2 := by decide +kernel

private theorem R07p09_bound_07 : ∀ j : Fin 22,R07p09_digit 7 j<2 := by decide +kernel

private theorem R07p09_bound_08 : ∀ j : Fin 22,R07p09_digit 8 j<2 := by decide +kernel

private theorem R07p09_bound_09 : ∀ j : Fin 22,R07p09_digit 9 j<2 := by decide +kernel

private theorem R07p09_bound_10 : ∀ j : Fin 22,R07p09_digit 10 j<2 := by decide +kernel

private theorem R07p09_bound_11 : ∀ j : Fin 22,R07p09_digit 11 j<2 := by decide +kernel

private theorem R07p09_bound_12 : ∀ j : Fin 22,R07p09_digit 12 j<2 := by decide +kernel

private theorem R07p09_bound_13 : ∀ j : Fin 22,R07p09_digit 13 j<2 := by decide +kernel

private theorem R07p09_bound_14 : ∀ j : Fin 22,R07p09_digit 14 j<2 := by decide +kernel

private theorem R07p09_bound_15 : ∀ j : Fin 22,R07p09_digit 15 j<2 := by decide +kernel

private theorem R07p09_bound_16 : ∀ j : Fin 22,R07p09_digit 16 j<2 := by decide +kernel

private theorem R07p09_bound_17 : ∀ j : Fin 22,R07p09_digit 17 j<2 := by decide +kernel

private theorem R07p09_bound_18 : ∀ j : Fin 22,R07p09_digit 18 j<2 := by decide +kernel

private theorem R07p09_bound_19 : ∀ j : Fin 22,R07p09_digit 19 j<2 := by decide +kernel

private theorem R07p09_bound_20 : ∀ j : Fin 22,R07p09_digit 20 j<2 := by decide +kernel

private theorem R07p09_bound_21 : ∀ j : Fin 22,R07p09_digit 21 j<2 := by decide +kernel

theorem R07p09_bound : ∀ i j : Fin 22,R07p09_digit i j<2 := by
  intro i j
  fin_cases i
  · exact R07p09_bound_00 j
  · exact R07p09_bound_01 j
  · exact R07p09_bound_02 j
  · exact R07p09_bound_03 j
  · exact R07p09_bound_04 j
  · exact R07p09_bound_05 j
  · exact R07p09_bound_06 j
  · exact R07p09_bound_07 j
  · exact R07p09_bound_08 j
  · exact R07p09_bound_09 j
  · exact R07p09_bound_10 j
  · exact R07p09_bound_11 j
  · exact R07p09_bound_12 j
  · exact R07p09_bound_13 j
  · exact R07p09_bound_14 j
  · exact R07p09_bound_15 j
  · exact R07p09_bound_16 j
  · exact R07p09_bound_17 j
  · exact R07p09_bound_18 j
  · exact R07p09_bound_19 j
  · exact R07p09_bound_20 j
  · exact R07p09_bound_21 j

private theorem R07p09_row_00 : pack 32 (R07p09_digit 0)=R07p09_rowCode 0 := by decide +kernel

private theorem R07p09_row_01 : pack 32 (R07p09_digit 1)=R07p09_rowCode 1 := by decide +kernel

private theorem R07p09_row_02 : pack 32 (R07p09_digit 2)=R07p09_rowCode 2 := by decide +kernel

private theorem R07p09_row_03 : pack 32 (R07p09_digit 3)=R07p09_rowCode 3 := by decide +kernel

private theorem R07p09_row_04 : pack 32 (R07p09_digit 4)=R07p09_rowCode 4 := by decide +kernel

private theorem R07p09_row_05 : pack 32 (R07p09_digit 5)=R07p09_rowCode 5 := by decide +kernel

private theorem R07p09_row_06 : pack 32 (R07p09_digit 6)=R07p09_rowCode 6 := by decide +kernel

private theorem R07p09_row_07 : pack 32 (R07p09_digit 7)=R07p09_rowCode 7 := by decide +kernel

private theorem R07p09_row_08 : pack 32 (R07p09_digit 8)=R07p09_rowCode 8 := by decide +kernel

private theorem R07p09_row_09 : pack 32 (R07p09_digit 9)=R07p09_rowCode 9 := by decide +kernel

private theorem R07p09_row_10 : pack 32 (R07p09_digit 10)=R07p09_rowCode 10 := by decide +kernel

private theorem R07p09_row_11 : pack 32 (R07p09_digit 11)=R07p09_rowCode 11 := by decide +kernel

private theorem R07p09_row_12 : pack 32 (R07p09_digit 12)=R07p09_rowCode 12 := by decide +kernel

private theorem R07p09_row_13 : pack 32 (R07p09_digit 13)=R07p09_rowCode 13 := by decide +kernel

private theorem R07p09_row_14 : pack 32 (R07p09_digit 14)=R07p09_rowCode 14 := by decide +kernel

private theorem R07p09_row_15 : pack 32 (R07p09_digit 15)=R07p09_rowCode 15 := by decide +kernel

private theorem R07p09_row_16 : pack 32 (R07p09_digit 16)=R07p09_rowCode 16 := by decide +kernel

private theorem R07p09_row_17 : pack 32 (R07p09_digit 17)=R07p09_rowCode 17 := by decide +kernel

private theorem R07p09_row_18 : pack 32 (R07p09_digit 18)=R07p09_rowCode 18 := by decide +kernel

private theorem R07p09_row_19 : pack 32 (R07p09_digit 19)=R07p09_rowCode 19 := by decide +kernel

private theorem R07p09_row_20 : pack 32 (R07p09_digit 20)=R07p09_rowCode 20 := by decide +kernel

private theorem R07p09_row_21 : pack 32 (R07p09_digit 21)=R07p09_rowCode 21 := by decide +kernel

theorem R07p09_row_binding : ∀ i : Fin 22,pack 32 (R07p09_digit i)=R07p09_rowCode i := by
  intro i
  fin_cases i
  · exact R07p09_row_00
  · exact R07p09_row_01
  · exact R07p09_row_02
  · exact R07p09_row_03
  · exact R07p09_row_04
  · exact R07p09_row_05
  · exact R07p09_row_06
  · exact R07p09_row_07
  · exact R07p09_row_08
  · exact R07p09_row_09
  · exact R07p09_row_10
  · exact R07p09_row_11
  · exact R07p09_row_12
  · exact R07p09_row_13
  · exact R07p09_row_14
  · exact R07p09_row_15
  · exact R07p09_row_16
  · exact R07p09_row_17
  · exact R07p09_row_18
  · exact R07p09_row_19
  · exact R07p09_row_20
  · exact R07p09_row_21

private theorem R07p09_column_00 : reversePack 32 (fun j : Fin 22 => R07p09_digit j 0)=R07p09_columnCode 0 := by decide +kernel

private theorem R07p09_column_01 : reversePack 32 (fun j : Fin 22 => R07p09_digit j 1)=R07p09_columnCode 1 := by decide +kernel

private theorem R07p09_column_02 : reversePack 32 (fun j : Fin 22 => R07p09_digit j 2)=R07p09_columnCode 2 := by decide +kernel

private theorem R07p09_column_03 : reversePack 32 (fun j : Fin 22 => R07p09_digit j 3)=R07p09_columnCode 3 := by decide +kernel

private theorem R07p09_column_04 : reversePack 32 (fun j : Fin 22 => R07p09_digit j 4)=R07p09_columnCode 4 := by decide +kernel

private theorem R07p09_column_05 : reversePack 32 (fun j : Fin 22 => R07p09_digit j 5)=R07p09_columnCode 5 := by decide +kernel

private theorem R07p09_column_06 : reversePack 32 (fun j : Fin 22 => R07p09_digit j 6)=R07p09_columnCode 6 := by decide +kernel

private theorem R07p09_column_07 : reversePack 32 (fun j : Fin 22 => R07p09_digit j 7)=R07p09_columnCode 7 := by decide +kernel

private theorem R07p09_column_08 : reversePack 32 (fun j : Fin 22 => R07p09_digit j 8)=R07p09_columnCode 8 := by decide +kernel

private theorem R07p09_column_09 : reversePack 32 (fun j : Fin 22 => R07p09_digit j 9)=R07p09_columnCode 9 := by decide +kernel

private theorem R07p09_column_10 : reversePack 32 (fun j : Fin 22 => R07p09_digit j 10)=R07p09_columnCode 10 := by decide +kernel

private theorem R07p09_column_11 : reversePack 32 (fun j : Fin 22 => R07p09_digit j 11)=R07p09_columnCode 11 := by decide +kernel

private theorem R07p09_column_12 : reversePack 32 (fun j : Fin 22 => R07p09_digit j 12)=R07p09_columnCode 12 := by decide +kernel

private theorem R07p09_column_13 : reversePack 32 (fun j : Fin 22 => R07p09_digit j 13)=R07p09_columnCode 13 := by decide +kernel

private theorem R07p09_column_14 : reversePack 32 (fun j : Fin 22 => R07p09_digit j 14)=R07p09_columnCode 14 := by decide +kernel

private theorem R07p09_column_15 : reversePack 32 (fun j : Fin 22 => R07p09_digit j 15)=R07p09_columnCode 15 := by decide +kernel

private theorem R07p09_column_16 : reversePack 32 (fun j : Fin 22 => R07p09_digit j 16)=R07p09_columnCode 16 := by decide +kernel

private theorem R07p09_column_17 : reversePack 32 (fun j : Fin 22 => R07p09_digit j 17)=R07p09_columnCode 17 := by decide +kernel

private theorem R07p09_column_18 : reversePack 32 (fun j : Fin 22 => R07p09_digit j 18)=R07p09_columnCode 18 := by decide +kernel

private theorem R07p09_column_19 : reversePack 32 (fun j : Fin 22 => R07p09_digit j 19)=R07p09_columnCode 19 := by decide +kernel

private theorem R07p09_column_20 : reversePack 32 (fun j : Fin 22 => R07p09_digit j 20)=R07p09_columnCode 20 := by decide +kernel

private theorem R07p09_column_21 : reversePack 32 (fun j : Fin 22 => R07p09_digit j 21)=R07p09_columnCode 21 := by decide +kernel

theorem R07p09_column_binding : ∀ i : Fin 22,reversePack 32 (fun j : Fin 22 => R07p09_digit j i)=R07p09_columnCode i := by
  intro i
  fin_cases i
  · exact R07p09_column_00
  · exact R07p09_column_01
  · exact R07p09_column_02
  · exact R07p09_column_03
  · exact R07p09_column_04
  · exact R07p09_column_05
  · exact R07p09_column_06
  · exact R07p09_column_07
  · exact R07p09_column_08
  · exact R07p09_column_09
  · exact R07p09_column_10
  · exact R07p09_column_11
  · exact R07p09_column_12
  · exact R07p09_column_13
  · exact R07p09_column_14
  · exact R07p09_column_15
  · exact R07p09_column_16
  · exact R07p09_column_17
  · exact R07p09_column_18
  · exact R07p09_column_19
  · exact R07p09_column_20
  · exact R07p09_column_21

def R07p09_data : PackedData 22 2 32 where
  raw := R07p09_digit
  digit_lt := R07p09_bound
  rowCode := R07p09_rowCode
  columnCode := R07p09_columnCode
  row_binding := R07p09_row_binding
  column_binding := R07p09_column_binding

def R07p10_lowColumnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 3014742
  | 1 => 1983068
  | 2 => 1358530
  | 3 => 957410
  | 4 => 2269325
  | 5 => 3336473
  | 6 => 644301
  | 7 => 2638707
  | 8 => 3455881
  | 9 => 3341081
  | 10 => 2792383
  | 11 => 1642662
  | 12 => 51816
  | 13 => 1824924
  | 14 => 3821815
  | 15 => 2017900
  | 16 => 3228530
  | 17 => 957122
  | 18 => 446634
  | 19 => 574034
  | 20 => 2097152
  | 21 => 3416064
  | _ => 0

def R07p10_rowCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1180592782936669945856
  | 1 => 40891917029093607283133285377
  | 2 => 38996454126519992713249
  | 3 => 1237977856264815068985688096
  | 4 => 39615291400438053409449312289
  | 5 => 1239187925818554814539268096
  | 6 => 39654014769855856774150652961
  | 7 => 1276626883035313070832387072
  | 8 => 1208925820776847358590976
  | 9 => 39654013589265398239456166944
  | 10 => 1073741824
  | 11 => 38723443207102926602404864
  | 12 => 1276626883035348255203427328
  | 13 => 40564819207303340884178420892672
  | 14 => 40853269219807092247283892256
  | 15 => 40890744739624651999348294656
  | 16 => 1208962749131574686515200
  | 17 => 1276664661931181314795405345
  | 18 => 40566095870747785760359665665057
  | 19 => 39652805879813963484714008609
  | 20 => 40564820455225613499426605630496
  | 21 => 41832471017637982646955976687617
  | _ => 0

def R07p10_columnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1307303404890521101384228570113
  | 1 => 40890744702730001701391074336
  | 2 => 1267650639188906968860747399200
  | 3 => 1267651848151620070537830630400
  | 4 => 40605671229780350018784171393025
  | 5 => 40566095833005748511485264396321
  | 6 => 40605671267559317944657604772864
  | 7 => 41832509739900595804797518480385
  | 8 => 40566057148561265420723703283745
  | 9 => 40566095833006901468174243332129
  | 10 => 41873361724598674272680433157121
  | 11 => 1307265891591772840824466834464
  | 12 => 1239186745190905301182709760
  | 13 => 40890708103237999042420016160
  | 14 => 41872123822300273219844048946209
  | 15 => 40853268002323074097955767328
  | 16 => 1267690532597254956903049461793
  | 17 => 1267650639188906967761236820992
  | 18 => 1268889750373926052337994989568
  | 19 => 1267689323634541854127495840768
  | 20 => 1
  | 21 => 1099511660577
  | _ => 0

def R07p10_digit (i j : Fin 22) : ℕ := packedDigit 1 (R07p10_lowColumnCode j) i.val

private theorem R07p10_bound_00 : ∀ j : Fin 22,R07p10_digit 0 j<2 := by decide +kernel

private theorem R07p10_bound_01 : ∀ j : Fin 22,R07p10_digit 1 j<2 := by decide +kernel

private theorem R07p10_bound_02 : ∀ j : Fin 22,R07p10_digit 2 j<2 := by decide +kernel

private theorem R07p10_bound_03 : ∀ j : Fin 22,R07p10_digit 3 j<2 := by decide +kernel

private theorem R07p10_bound_04 : ∀ j : Fin 22,R07p10_digit 4 j<2 := by decide +kernel

private theorem R07p10_bound_05 : ∀ j : Fin 22,R07p10_digit 5 j<2 := by decide +kernel

private theorem R07p10_bound_06 : ∀ j : Fin 22,R07p10_digit 6 j<2 := by decide +kernel

private theorem R07p10_bound_07 : ∀ j : Fin 22,R07p10_digit 7 j<2 := by decide +kernel

private theorem R07p10_bound_08 : ∀ j : Fin 22,R07p10_digit 8 j<2 := by decide +kernel

private theorem R07p10_bound_09 : ∀ j : Fin 22,R07p10_digit 9 j<2 := by decide +kernel

private theorem R07p10_bound_10 : ∀ j : Fin 22,R07p10_digit 10 j<2 := by decide +kernel

private theorem R07p10_bound_11 : ∀ j : Fin 22,R07p10_digit 11 j<2 := by decide +kernel

private theorem R07p10_bound_12 : ∀ j : Fin 22,R07p10_digit 12 j<2 := by decide +kernel

private theorem R07p10_bound_13 : ∀ j : Fin 22,R07p10_digit 13 j<2 := by decide +kernel

private theorem R07p10_bound_14 : ∀ j : Fin 22,R07p10_digit 14 j<2 := by decide +kernel

private theorem R07p10_bound_15 : ∀ j : Fin 22,R07p10_digit 15 j<2 := by decide +kernel

private theorem R07p10_bound_16 : ∀ j : Fin 22,R07p10_digit 16 j<2 := by decide +kernel

private theorem R07p10_bound_17 : ∀ j : Fin 22,R07p10_digit 17 j<2 := by decide +kernel

private theorem R07p10_bound_18 : ∀ j : Fin 22,R07p10_digit 18 j<2 := by decide +kernel

private theorem R07p10_bound_19 : ∀ j : Fin 22,R07p10_digit 19 j<2 := by decide +kernel

private theorem R07p10_bound_20 : ∀ j : Fin 22,R07p10_digit 20 j<2 := by decide +kernel

private theorem R07p10_bound_21 : ∀ j : Fin 22,R07p10_digit 21 j<2 := by decide +kernel

theorem R07p10_bound : ∀ i j : Fin 22,R07p10_digit i j<2 := by
  intro i j
  fin_cases i
  · exact R07p10_bound_00 j
  · exact R07p10_bound_01 j
  · exact R07p10_bound_02 j
  · exact R07p10_bound_03 j
  · exact R07p10_bound_04 j
  · exact R07p10_bound_05 j
  · exact R07p10_bound_06 j
  · exact R07p10_bound_07 j
  · exact R07p10_bound_08 j
  · exact R07p10_bound_09 j
  · exact R07p10_bound_10 j
  · exact R07p10_bound_11 j
  · exact R07p10_bound_12 j
  · exact R07p10_bound_13 j
  · exact R07p10_bound_14 j
  · exact R07p10_bound_15 j
  · exact R07p10_bound_16 j
  · exact R07p10_bound_17 j
  · exact R07p10_bound_18 j
  · exact R07p10_bound_19 j
  · exact R07p10_bound_20 j
  · exact R07p10_bound_21 j

private theorem R07p10_row_00 : pack 32 (R07p10_digit 0)=R07p10_rowCode 0 := by decide +kernel

private theorem R07p10_row_01 : pack 32 (R07p10_digit 1)=R07p10_rowCode 1 := by decide +kernel

private theorem R07p10_row_02 : pack 32 (R07p10_digit 2)=R07p10_rowCode 2 := by decide +kernel

private theorem R07p10_row_03 : pack 32 (R07p10_digit 3)=R07p10_rowCode 3 := by decide +kernel

private theorem R07p10_row_04 : pack 32 (R07p10_digit 4)=R07p10_rowCode 4 := by decide +kernel

private theorem R07p10_row_05 : pack 32 (R07p10_digit 5)=R07p10_rowCode 5 := by decide +kernel

private theorem R07p10_row_06 : pack 32 (R07p10_digit 6)=R07p10_rowCode 6 := by decide +kernel

private theorem R07p10_row_07 : pack 32 (R07p10_digit 7)=R07p10_rowCode 7 := by decide +kernel

private theorem R07p10_row_08 : pack 32 (R07p10_digit 8)=R07p10_rowCode 8 := by decide +kernel

private theorem R07p10_row_09 : pack 32 (R07p10_digit 9)=R07p10_rowCode 9 := by decide +kernel

private theorem R07p10_row_10 : pack 32 (R07p10_digit 10)=R07p10_rowCode 10 := by decide +kernel

private theorem R07p10_row_11 : pack 32 (R07p10_digit 11)=R07p10_rowCode 11 := by decide +kernel

private theorem R07p10_row_12 : pack 32 (R07p10_digit 12)=R07p10_rowCode 12 := by decide +kernel

private theorem R07p10_row_13 : pack 32 (R07p10_digit 13)=R07p10_rowCode 13 := by decide +kernel

private theorem R07p10_row_14 : pack 32 (R07p10_digit 14)=R07p10_rowCode 14 := by decide +kernel

private theorem R07p10_row_15 : pack 32 (R07p10_digit 15)=R07p10_rowCode 15 := by decide +kernel

private theorem R07p10_row_16 : pack 32 (R07p10_digit 16)=R07p10_rowCode 16 := by decide +kernel

private theorem R07p10_row_17 : pack 32 (R07p10_digit 17)=R07p10_rowCode 17 := by decide +kernel

private theorem R07p10_row_18 : pack 32 (R07p10_digit 18)=R07p10_rowCode 18 := by decide +kernel

private theorem R07p10_row_19 : pack 32 (R07p10_digit 19)=R07p10_rowCode 19 := by decide +kernel

private theorem R07p10_row_20 : pack 32 (R07p10_digit 20)=R07p10_rowCode 20 := by decide +kernel

private theorem R07p10_row_21 : pack 32 (R07p10_digit 21)=R07p10_rowCode 21 := by decide +kernel

theorem R07p10_row_binding : ∀ i : Fin 22,pack 32 (R07p10_digit i)=R07p10_rowCode i := by
  intro i
  fin_cases i
  · exact R07p10_row_00
  · exact R07p10_row_01
  · exact R07p10_row_02
  · exact R07p10_row_03
  · exact R07p10_row_04
  · exact R07p10_row_05
  · exact R07p10_row_06
  · exact R07p10_row_07
  · exact R07p10_row_08
  · exact R07p10_row_09
  · exact R07p10_row_10
  · exact R07p10_row_11
  · exact R07p10_row_12
  · exact R07p10_row_13
  · exact R07p10_row_14
  · exact R07p10_row_15
  · exact R07p10_row_16
  · exact R07p10_row_17
  · exact R07p10_row_18
  · exact R07p10_row_19
  · exact R07p10_row_20
  · exact R07p10_row_21

private theorem R07p10_column_00 : reversePack 32 (fun j : Fin 22 => R07p10_digit j 0)=R07p10_columnCode 0 := by decide +kernel

private theorem R07p10_column_01 : reversePack 32 (fun j : Fin 22 => R07p10_digit j 1)=R07p10_columnCode 1 := by decide +kernel

private theorem R07p10_column_02 : reversePack 32 (fun j : Fin 22 => R07p10_digit j 2)=R07p10_columnCode 2 := by decide +kernel

private theorem R07p10_column_03 : reversePack 32 (fun j : Fin 22 => R07p10_digit j 3)=R07p10_columnCode 3 := by decide +kernel

private theorem R07p10_column_04 : reversePack 32 (fun j : Fin 22 => R07p10_digit j 4)=R07p10_columnCode 4 := by decide +kernel

private theorem R07p10_column_05 : reversePack 32 (fun j : Fin 22 => R07p10_digit j 5)=R07p10_columnCode 5 := by decide +kernel

private theorem R07p10_column_06 : reversePack 32 (fun j : Fin 22 => R07p10_digit j 6)=R07p10_columnCode 6 := by decide +kernel

private theorem R07p10_column_07 : reversePack 32 (fun j : Fin 22 => R07p10_digit j 7)=R07p10_columnCode 7 := by decide +kernel

private theorem R07p10_column_08 : reversePack 32 (fun j : Fin 22 => R07p10_digit j 8)=R07p10_columnCode 8 := by decide +kernel

private theorem R07p10_column_09 : reversePack 32 (fun j : Fin 22 => R07p10_digit j 9)=R07p10_columnCode 9 := by decide +kernel

private theorem R07p10_column_10 : reversePack 32 (fun j : Fin 22 => R07p10_digit j 10)=R07p10_columnCode 10 := by decide +kernel

private theorem R07p10_column_11 : reversePack 32 (fun j : Fin 22 => R07p10_digit j 11)=R07p10_columnCode 11 := by decide +kernel

private theorem R07p10_column_12 : reversePack 32 (fun j : Fin 22 => R07p10_digit j 12)=R07p10_columnCode 12 := by decide +kernel

private theorem R07p10_column_13 : reversePack 32 (fun j : Fin 22 => R07p10_digit j 13)=R07p10_columnCode 13 := by decide +kernel

private theorem R07p10_column_14 : reversePack 32 (fun j : Fin 22 => R07p10_digit j 14)=R07p10_columnCode 14 := by decide +kernel

private theorem R07p10_column_15 : reversePack 32 (fun j : Fin 22 => R07p10_digit j 15)=R07p10_columnCode 15 := by decide +kernel

private theorem R07p10_column_16 : reversePack 32 (fun j : Fin 22 => R07p10_digit j 16)=R07p10_columnCode 16 := by decide +kernel

private theorem R07p10_column_17 : reversePack 32 (fun j : Fin 22 => R07p10_digit j 17)=R07p10_columnCode 17 := by decide +kernel

private theorem R07p10_column_18 : reversePack 32 (fun j : Fin 22 => R07p10_digit j 18)=R07p10_columnCode 18 := by decide +kernel

private theorem R07p10_column_19 : reversePack 32 (fun j : Fin 22 => R07p10_digit j 19)=R07p10_columnCode 19 := by decide +kernel

private theorem R07p10_column_20 : reversePack 32 (fun j : Fin 22 => R07p10_digit j 20)=R07p10_columnCode 20 := by decide +kernel

private theorem R07p10_column_21 : reversePack 32 (fun j : Fin 22 => R07p10_digit j 21)=R07p10_columnCode 21 := by decide +kernel

theorem R07p10_column_binding : ∀ i : Fin 22,reversePack 32 (fun j : Fin 22 => R07p10_digit j i)=R07p10_columnCode i := by
  intro i
  fin_cases i
  · exact R07p10_column_00
  · exact R07p10_column_01
  · exact R07p10_column_02
  · exact R07p10_column_03
  · exact R07p10_column_04
  · exact R07p10_column_05
  · exact R07p10_column_06
  · exact R07p10_column_07
  · exact R07p10_column_08
  · exact R07p10_column_09
  · exact R07p10_column_10
  · exact R07p10_column_11
  · exact R07p10_column_12
  · exact R07p10_column_13
  · exact R07p10_column_14
  · exact R07p10_column_15
  · exact R07p10_column_16
  · exact R07p10_column_17
  · exact R07p10_column_18
  · exact R07p10_column_19
  · exact R07p10_column_20
  · exact R07p10_column_21

def R07p10_data : PackedData 22 2 32 where
  raw := R07p10_digit
  digit_lt := R07p10_bound
  rowCode := R07p10_rowCode
  columnCode := R07p10_columnCode
  row_binding := R07p10_row_binding
  column_binding := R07p10_column_binding

def R07p11_lowColumnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1860467
  | 1 => 2777692
  | 2 => 2892153
  | 3 => 2777686
  | 4 => 7139
  | 5 => 3814360
  | 6 => 415888
  | 7 => 3539372
  | 8 => 3814136
  | 9 => 409891
  | 10 => 3370511
  | 11 => 412451
  | 12 => 414499
  | 13 => 1631023
  | 14 => 2875404
  | 15 => 3433042
  | 16 => 3416064
  | 17 => 2727948
  | 18 => 3424783
  | 19 => 3990098
  | 20 => 893216
  | 21 => 2097152
  | _ => 0

def R07p11_rowCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1237940077368979808224019457
  | 1 => 40852059113433011562157735937
  | 2 => 1276626882999283207586742304
  | 3 => 1276626882999284307131892768
  | 4 => 39614119036064032854552642593
  | 5 => 1267650600266311876263992624129
  | 6 => 39614119036064032853479949345
  | 7 => 1134979710976
  | 8 => 1267650600266311875164514550785
  | 9 => 40852059113432977477330829345
  | 10 => 1125899906842624
  | 11 => 37154698000596992
  | 12 => 1152922605226819584
  | 13 => 1307304615033826951877684659233
  | 14 => 40852060294024632280641732641
  | 15 => 1307303368329074347291896184832
  | 16 => 1267689287035049816247611949056
  | 17 => 1181781733238294741024
  | 18 => 1308503868230587413676142101505
  | 19 => 1307303368329074348391441400865
  | 20 => 40853268038063641839238381569
  | 21 => 40605711162111330290437323785248
  | _ => 0

def R07p11_columnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 41832509739900595805897030140960
  | 1 => 40890744702730002800902669313
  | 2 => 40566097079710498863136259474433
  | 3 => 1307303404891674024022706750465
  | 4 => 41832471055454960918431258378240
  | 5 => 1276664663082978018973451297
  | 6 => 38686806820449969641652224
  | 7 => 40853231439722272565677293601
  | 8 => 1277873552009104500729054241
  | 9 => 41832471016494283352202160406528
  | 10 => 41873321828829177875798315499553
  | 11 => 41832471016495437399606674096128
  | 12 => 41832471016495436308891139342336
  | 13 => 41873323037791853823879022642208
  | 14 => 40852021296417550206650811393
  | 15 => 1267689323634541855225933758497
  | 16 => 1099511660577
  | 17 => 40852021296417550172290024449
  | 18 => 41873321828829140720001843494945
  | 19 => 1267689323634541855227007501345
  | 20 => 1208962713103877212767232
  | 21 => 1
  | _ => 0

def R07p11_digit (i j : Fin 22) : ℕ := packedDigit 1 (R07p11_lowColumnCode j) i.val

private theorem R07p11_bound_00 : ∀ j : Fin 22,R07p11_digit 0 j<2 := by decide +kernel

private theorem R07p11_bound_01 : ∀ j : Fin 22,R07p11_digit 1 j<2 := by decide +kernel

private theorem R07p11_bound_02 : ∀ j : Fin 22,R07p11_digit 2 j<2 := by decide +kernel

private theorem R07p11_bound_03 : ∀ j : Fin 22,R07p11_digit 3 j<2 := by decide +kernel

private theorem R07p11_bound_04 : ∀ j : Fin 22,R07p11_digit 4 j<2 := by decide +kernel

private theorem R07p11_bound_05 : ∀ j : Fin 22,R07p11_digit 5 j<2 := by decide +kernel

private theorem R07p11_bound_06 : ∀ j : Fin 22,R07p11_digit 6 j<2 := by decide +kernel

private theorem R07p11_bound_07 : ∀ j : Fin 22,R07p11_digit 7 j<2 := by decide +kernel

private theorem R07p11_bound_08 : ∀ j : Fin 22,R07p11_digit 8 j<2 := by decide +kernel

private theorem R07p11_bound_09 : ∀ j : Fin 22,R07p11_digit 9 j<2 := by decide +kernel

private theorem R07p11_bound_10 : ∀ j : Fin 22,R07p11_digit 10 j<2 := by decide +kernel

private theorem R07p11_bound_11 : ∀ j : Fin 22,R07p11_digit 11 j<2 := by decide +kernel

private theorem R07p11_bound_12 : ∀ j : Fin 22,R07p11_digit 12 j<2 := by decide +kernel

private theorem R07p11_bound_13 : ∀ j : Fin 22,R07p11_digit 13 j<2 := by decide +kernel

private theorem R07p11_bound_14 : ∀ j : Fin 22,R07p11_digit 14 j<2 := by decide +kernel

private theorem R07p11_bound_15 : ∀ j : Fin 22,R07p11_digit 15 j<2 := by decide +kernel

private theorem R07p11_bound_16 : ∀ j : Fin 22,R07p11_digit 16 j<2 := by decide +kernel

private theorem R07p11_bound_17 : ∀ j : Fin 22,R07p11_digit 17 j<2 := by decide +kernel

private theorem R07p11_bound_18 : ∀ j : Fin 22,R07p11_digit 18 j<2 := by decide +kernel

private theorem R07p11_bound_19 : ∀ j : Fin 22,R07p11_digit 19 j<2 := by decide +kernel

private theorem R07p11_bound_20 : ∀ j : Fin 22,R07p11_digit 20 j<2 := by decide +kernel

private theorem R07p11_bound_21 : ∀ j : Fin 22,R07p11_digit 21 j<2 := by decide +kernel

theorem R07p11_bound : ∀ i j : Fin 22,R07p11_digit i j<2 := by
  intro i j
  fin_cases i
  · exact R07p11_bound_00 j
  · exact R07p11_bound_01 j
  · exact R07p11_bound_02 j
  · exact R07p11_bound_03 j
  · exact R07p11_bound_04 j
  · exact R07p11_bound_05 j
  · exact R07p11_bound_06 j
  · exact R07p11_bound_07 j
  · exact R07p11_bound_08 j
  · exact R07p11_bound_09 j
  · exact R07p11_bound_10 j
  · exact R07p11_bound_11 j
  · exact R07p11_bound_12 j
  · exact R07p11_bound_13 j
  · exact R07p11_bound_14 j
  · exact R07p11_bound_15 j
  · exact R07p11_bound_16 j
  · exact R07p11_bound_17 j
  · exact R07p11_bound_18 j
  · exact R07p11_bound_19 j
  · exact R07p11_bound_20 j
  · exact R07p11_bound_21 j

private theorem R07p11_row_00 : pack 32 (R07p11_digit 0)=R07p11_rowCode 0 := by decide +kernel

private theorem R07p11_row_01 : pack 32 (R07p11_digit 1)=R07p11_rowCode 1 := by decide +kernel

private theorem R07p11_row_02 : pack 32 (R07p11_digit 2)=R07p11_rowCode 2 := by decide +kernel

private theorem R07p11_row_03 : pack 32 (R07p11_digit 3)=R07p11_rowCode 3 := by decide +kernel

private theorem R07p11_row_04 : pack 32 (R07p11_digit 4)=R07p11_rowCode 4 := by decide +kernel

private theorem R07p11_row_05 : pack 32 (R07p11_digit 5)=R07p11_rowCode 5 := by decide +kernel

private theorem R07p11_row_06 : pack 32 (R07p11_digit 6)=R07p11_rowCode 6 := by decide +kernel

private theorem R07p11_row_07 : pack 32 (R07p11_digit 7)=R07p11_rowCode 7 := by decide +kernel

private theorem R07p11_row_08 : pack 32 (R07p11_digit 8)=R07p11_rowCode 8 := by decide +kernel

private theorem R07p11_row_09 : pack 32 (R07p11_digit 9)=R07p11_rowCode 9 := by decide +kernel

private theorem R07p11_row_10 : pack 32 (R07p11_digit 10)=R07p11_rowCode 10 := by decide +kernel

private theorem R07p11_row_11 : pack 32 (R07p11_digit 11)=R07p11_rowCode 11 := by decide +kernel

private theorem R07p11_row_12 : pack 32 (R07p11_digit 12)=R07p11_rowCode 12 := by decide +kernel

private theorem R07p11_row_13 : pack 32 (R07p11_digit 13)=R07p11_rowCode 13 := by decide +kernel

private theorem R07p11_row_14 : pack 32 (R07p11_digit 14)=R07p11_rowCode 14 := by decide +kernel

private theorem R07p11_row_15 : pack 32 (R07p11_digit 15)=R07p11_rowCode 15 := by decide +kernel

private theorem R07p11_row_16 : pack 32 (R07p11_digit 16)=R07p11_rowCode 16 := by decide +kernel

private theorem R07p11_row_17 : pack 32 (R07p11_digit 17)=R07p11_rowCode 17 := by decide +kernel

private theorem R07p11_row_18 : pack 32 (R07p11_digit 18)=R07p11_rowCode 18 := by decide +kernel

private theorem R07p11_row_19 : pack 32 (R07p11_digit 19)=R07p11_rowCode 19 := by decide +kernel

private theorem R07p11_row_20 : pack 32 (R07p11_digit 20)=R07p11_rowCode 20 := by decide +kernel

private theorem R07p11_row_21 : pack 32 (R07p11_digit 21)=R07p11_rowCode 21 := by decide +kernel

theorem R07p11_row_binding : ∀ i : Fin 22,pack 32 (R07p11_digit i)=R07p11_rowCode i := by
  intro i
  fin_cases i
  · exact R07p11_row_00
  · exact R07p11_row_01
  · exact R07p11_row_02
  · exact R07p11_row_03
  · exact R07p11_row_04
  · exact R07p11_row_05
  · exact R07p11_row_06
  · exact R07p11_row_07
  · exact R07p11_row_08
  · exact R07p11_row_09
  · exact R07p11_row_10
  · exact R07p11_row_11
  · exact R07p11_row_12
  · exact R07p11_row_13
  · exact R07p11_row_14
  · exact R07p11_row_15
  · exact R07p11_row_16
  · exact R07p11_row_17
  · exact R07p11_row_18
  · exact R07p11_row_19
  · exact R07p11_row_20
  · exact R07p11_row_21

private theorem R07p11_column_00 : reversePack 32 (fun j : Fin 22 => R07p11_digit j 0)=R07p11_columnCode 0 := by decide +kernel

private theorem R07p11_column_01 : reversePack 32 (fun j : Fin 22 => R07p11_digit j 1)=R07p11_columnCode 1 := by decide +kernel

private theorem R07p11_column_02 : reversePack 32 (fun j : Fin 22 => R07p11_digit j 2)=R07p11_columnCode 2 := by decide +kernel

private theorem R07p11_column_03 : reversePack 32 (fun j : Fin 22 => R07p11_digit j 3)=R07p11_columnCode 3 := by decide +kernel

private theorem R07p11_column_04 : reversePack 32 (fun j : Fin 22 => R07p11_digit j 4)=R07p11_columnCode 4 := by decide +kernel

private theorem R07p11_column_05 : reversePack 32 (fun j : Fin 22 => R07p11_digit j 5)=R07p11_columnCode 5 := by decide +kernel

private theorem R07p11_column_06 : reversePack 32 (fun j : Fin 22 => R07p11_digit j 6)=R07p11_columnCode 6 := by decide +kernel

private theorem R07p11_column_07 : reversePack 32 (fun j : Fin 22 => R07p11_digit j 7)=R07p11_columnCode 7 := by decide +kernel

private theorem R07p11_column_08 : reversePack 32 (fun j : Fin 22 => R07p11_digit j 8)=R07p11_columnCode 8 := by decide +kernel

private theorem R07p11_column_09 : reversePack 32 (fun j : Fin 22 => R07p11_digit j 9)=R07p11_columnCode 9 := by decide +kernel

private theorem R07p11_column_10 : reversePack 32 (fun j : Fin 22 => R07p11_digit j 10)=R07p11_columnCode 10 := by decide +kernel

private theorem R07p11_column_11 : reversePack 32 (fun j : Fin 22 => R07p11_digit j 11)=R07p11_columnCode 11 := by decide +kernel

private theorem R07p11_column_12 : reversePack 32 (fun j : Fin 22 => R07p11_digit j 12)=R07p11_columnCode 12 := by decide +kernel

private theorem R07p11_column_13 : reversePack 32 (fun j : Fin 22 => R07p11_digit j 13)=R07p11_columnCode 13 := by decide +kernel

private theorem R07p11_column_14 : reversePack 32 (fun j : Fin 22 => R07p11_digit j 14)=R07p11_columnCode 14 := by decide +kernel

private theorem R07p11_column_15 : reversePack 32 (fun j : Fin 22 => R07p11_digit j 15)=R07p11_columnCode 15 := by decide +kernel

private theorem R07p11_column_16 : reversePack 32 (fun j : Fin 22 => R07p11_digit j 16)=R07p11_columnCode 16 := by decide +kernel

private theorem R07p11_column_17 : reversePack 32 (fun j : Fin 22 => R07p11_digit j 17)=R07p11_columnCode 17 := by decide +kernel

private theorem R07p11_column_18 : reversePack 32 (fun j : Fin 22 => R07p11_digit j 18)=R07p11_columnCode 18 := by decide +kernel

private theorem R07p11_column_19 : reversePack 32 (fun j : Fin 22 => R07p11_digit j 19)=R07p11_columnCode 19 := by decide +kernel

private theorem R07p11_column_20 : reversePack 32 (fun j : Fin 22 => R07p11_digit j 20)=R07p11_columnCode 20 := by decide +kernel

private theorem R07p11_column_21 : reversePack 32 (fun j : Fin 22 => R07p11_digit j 21)=R07p11_columnCode 21 := by decide +kernel

theorem R07p11_column_binding : ∀ i : Fin 22,reversePack 32 (fun j : Fin 22 => R07p11_digit j i)=R07p11_columnCode i := by
  intro i
  fin_cases i
  · exact R07p11_column_00
  · exact R07p11_column_01
  · exact R07p11_column_02
  · exact R07p11_column_03
  · exact R07p11_column_04
  · exact R07p11_column_05
  · exact R07p11_column_06
  · exact R07p11_column_07
  · exact R07p11_column_08
  · exact R07p11_column_09
  · exact R07p11_column_10
  · exact R07p11_column_11
  · exact R07p11_column_12
  · exact R07p11_column_13
  · exact R07p11_column_14
  · exact R07p11_column_15
  · exact R07p11_column_16
  · exact R07p11_column_17
  · exact R07p11_column_18
  · exact R07p11_column_19
  · exact R07p11_column_20
  · exact R07p11_column_21

def R07p11_data : PackedData 22 2 32 where
  raw := R07p11_digit
  digit_lt := R07p11_bound
  rowCode := R07p11_rowCode
  columnCode := R07p11_columnCode
  row_binding := R07p11_row_binding
  column_binding := R07p11_column_binding

end SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoCaches06
