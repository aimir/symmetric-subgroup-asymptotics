import SymmetricSubgroupAsymptotics.MatrixKroneckerProductReflection
import Mathlib.Tactic.FinCases

/-! Fixed Co2 binary22 shared caches. Every digit and pack binding is kernel checked. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoCaches08
open MatrixKroneckerProductReflection MatrixKroneckerDotReflection
open MatrixNaturalRowDotReflection SmallNaturalMatrixProductReflection

def R08p06_lowColumnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 2177157
  | 1 => 2173530
  | 2 => 996087
  | 3 => 1767478
  | 4 => 1651132
  | 5 => 2369919
  | 6 => 2482457
  | 7 => 2191834
  | 8 => 2531609
  | 9 => 2369631
  | 10 => 361283
  | 11 => 522
  | 12 => 3439057
  | 13 => 1956599
  | 14 => 447136
  | 15 => 1763894
  | 16 => 1026102
  | 17 => 1846326
  | 18 => 90705
  | 19 => 2697270
  | 20 => 600118
  | 21 => 1220608
  | _ => 0

def R08p06_rowCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1237940077332952111822930945
  | 1 => 1307304613853271394076512519200
  | 2 => 1307304613853234239345228022785
  | 3 => 36065116370763808
  | 4 => 1308542553893672542259679101984
  | 5 => 1307304615033825824878267237376
  | 6 => 1237940077332951045597299744
  | 7 => 1218638030403798041601
  | 8 => 1154048539493400576
  | 9 => 1237979035739506793817048096
  | 10 => 38685626227668133590597632
  | 11 => 1307304613854387160849833820193
  | 12 => 1218638030403798074369
  | 13 => 41873361761160119902006762570785
  | 14 => 1237979036855273636931600384
  | 15 => 40564820455225578561346161639424
  | 16 => 1308503830487361179280309486625
  | 17 => 40564820455188683947297761952768
  | 18 => 39895770686475317100413952
  | 19 => 1307304613853234204160822379520
  | 20 => 40564857930746546788637281910784
  | 21 => 39614081258285126620729573409
  | _ => 0

def R08p06_columnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 40604433289741065799592509964289
  | 1 => 1268927263673828361366413508609
  | 2 => 41872123822301426142413841269760
  | 3 => 1307304576037410015275465573408
  | 4 => 40891917065949976983184081952
  | 5 => 41873361761195861559329641496577
  | 6 => 40566095833005747385585390092289
  | 7 => 1268927264890159458045462052865
  | 8 => 40566095833005747385550997848065
  | 9 => 41873360552233148456553047687169
  | 10 => 41832469845348548522001500766208
  | 11 => 1268888540268667703276209176576
  | 12 => 40564857931925986650068235616289
  | 13 => 41872123822301427267249668916256
  | 14 => 1210107564192070999506944
  | 15 => 1307304576038562901595700331552
  | 16 => 1307304576037409980056767333376
  | 17 => 1307304576037446008852677952544
  | 18 => 40564857930709653301623766646784
  | 19 => 1307304576037409980055692510209
  | 20 => 1307304576037409980055692510208
  | 21 => 1100586418208
  | _ => 0

def R08p06_digit (i j : Fin 22) : ℕ := packedDigit 1 (R08p06_lowColumnCode j) i.val

private theorem R08p06_bound_00 : ∀ j : Fin 22,R08p06_digit 0 j<2 := by decide +kernel

private theorem R08p06_bound_01 : ∀ j : Fin 22,R08p06_digit 1 j<2 := by decide +kernel

private theorem R08p06_bound_02 : ∀ j : Fin 22,R08p06_digit 2 j<2 := by decide +kernel

private theorem R08p06_bound_03 : ∀ j : Fin 22,R08p06_digit 3 j<2 := by decide +kernel

private theorem R08p06_bound_04 : ∀ j : Fin 22,R08p06_digit 4 j<2 := by decide +kernel

private theorem R08p06_bound_05 : ∀ j : Fin 22,R08p06_digit 5 j<2 := by decide +kernel

private theorem R08p06_bound_06 : ∀ j : Fin 22,R08p06_digit 6 j<2 := by decide +kernel

private theorem R08p06_bound_07 : ∀ j : Fin 22,R08p06_digit 7 j<2 := by decide +kernel

private theorem R08p06_bound_08 : ∀ j : Fin 22,R08p06_digit 8 j<2 := by decide +kernel

private theorem R08p06_bound_09 : ∀ j : Fin 22,R08p06_digit 9 j<2 := by decide +kernel

private theorem R08p06_bound_10 : ∀ j : Fin 22,R08p06_digit 10 j<2 := by decide +kernel

private theorem R08p06_bound_11 : ∀ j : Fin 22,R08p06_digit 11 j<2 := by decide +kernel

private theorem R08p06_bound_12 : ∀ j : Fin 22,R08p06_digit 12 j<2 := by decide +kernel

private theorem R08p06_bound_13 : ∀ j : Fin 22,R08p06_digit 13 j<2 := by decide +kernel

private theorem R08p06_bound_14 : ∀ j : Fin 22,R08p06_digit 14 j<2 := by decide +kernel

private theorem R08p06_bound_15 : ∀ j : Fin 22,R08p06_digit 15 j<2 := by decide +kernel

private theorem R08p06_bound_16 : ∀ j : Fin 22,R08p06_digit 16 j<2 := by decide +kernel

private theorem R08p06_bound_17 : ∀ j : Fin 22,R08p06_digit 17 j<2 := by decide +kernel

private theorem R08p06_bound_18 : ∀ j : Fin 22,R08p06_digit 18 j<2 := by decide +kernel

private theorem R08p06_bound_19 : ∀ j : Fin 22,R08p06_digit 19 j<2 := by decide +kernel

private theorem R08p06_bound_20 : ∀ j : Fin 22,R08p06_digit 20 j<2 := by decide +kernel

private theorem R08p06_bound_21 : ∀ j : Fin 22,R08p06_digit 21 j<2 := by decide +kernel

theorem R08p06_bound : ∀ i j : Fin 22,R08p06_digit i j<2 := by
  intro i j
  fin_cases i
  · exact R08p06_bound_00 j
  · exact R08p06_bound_01 j
  · exact R08p06_bound_02 j
  · exact R08p06_bound_03 j
  · exact R08p06_bound_04 j
  · exact R08p06_bound_05 j
  · exact R08p06_bound_06 j
  · exact R08p06_bound_07 j
  · exact R08p06_bound_08 j
  · exact R08p06_bound_09 j
  · exact R08p06_bound_10 j
  · exact R08p06_bound_11 j
  · exact R08p06_bound_12 j
  · exact R08p06_bound_13 j
  · exact R08p06_bound_14 j
  · exact R08p06_bound_15 j
  · exact R08p06_bound_16 j
  · exact R08p06_bound_17 j
  · exact R08p06_bound_18 j
  · exact R08p06_bound_19 j
  · exact R08p06_bound_20 j
  · exact R08p06_bound_21 j

private theorem R08p06_row_00 : pack 32 (R08p06_digit 0)=R08p06_rowCode 0 := by decide +kernel

private theorem R08p06_row_01 : pack 32 (R08p06_digit 1)=R08p06_rowCode 1 := by decide +kernel

private theorem R08p06_row_02 : pack 32 (R08p06_digit 2)=R08p06_rowCode 2 := by decide +kernel

private theorem R08p06_row_03 : pack 32 (R08p06_digit 3)=R08p06_rowCode 3 := by decide +kernel

private theorem R08p06_row_04 : pack 32 (R08p06_digit 4)=R08p06_rowCode 4 := by decide +kernel

private theorem R08p06_row_05 : pack 32 (R08p06_digit 5)=R08p06_rowCode 5 := by decide +kernel

private theorem R08p06_row_06 : pack 32 (R08p06_digit 6)=R08p06_rowCode 6 := by decide +kernel

private theorem R08p06_row_07 : pack 32 (R08p06_digit 7)=R08p06_rowCode 7 := by decide +kernel

private theorem R08p06_row_08 : pack 32 (R08p06_digit 8)=R08p06_rowCode 8 := by decide +kernel

private theorem R08p06_row_09 : pack 32 (R08p06_digit 9)=R08p06_rowCode 9 := by decide +kernel

private theorem R08p06_row_10 : pack 32 (R08p06_digit 10)=R08p06_rowCode 10 := by decide +kernel

private theorem R08p06_row_11 : pack 32 (R08p06_digit 11)=R08p06_rowCode 11 := by decide +kernel

private theorem R08p06_row_12 : pack 32 (R08p06_digit 12)=R08p06_rowCode 12 := by decide +kernel

private theorem R08p06_row_13 : pack 32 (R08p06_digit 13)=R08p06_rowCode 13 := by decide +kernel

private theorem R08p06_row_14 : pack 32 (R08p06_digit 14)=R08p06_rowCode 14 := by decide +kernel

private theorem R08p06_row_15 : pack 32 (R08p06_digit 15)=R08p06_rowCode 15 := by decide +kernel

private theorem R08p06_row_16 : pack 32 (R08p06_digit 16)=R08p06_rowCode 16 := by decide +kernel

private theorem R08p06_row_17 : pack 32 (R08p06_digit 17)=R08p06_rowCode 17 := by decide +kernel

private theorem R08p06_row_18 : pack 32 (R08p06_digit 18)=R08p06_rowCode 18 := by decide +kernel

private theorem R08p06_row_19 : pack 32 (R08p06_digit 19)=R08p06_rowCode 19 := by decide +kernel

private theorem R08p06_row_20 : pack 32 (R08p06_digit 20)=R08p06_rowCode 20 := by decide +kernel

private theorem R08p06_row_21 : pack 32 (R08p06_digit 21)=R08p06_rowCode 21 := by decide +kernel

theorem R08p06_row_binding : ∀ i : Fin 22,pack 32 (R08p06_digit i)=R08p06_rowCode i := by
  intro i
  fin_cases i
  · exact R08p06_row_00
  · exact R08p06_row_01
  · exact R08p06_row_02
  · exact R08p06_row_03
  · exact R08p06_row_04
  · exact R08p06_row_05
  · exact R08p06_row_06
  · exact R08p06_row_07
  · exact R08p06_row_08
  · exact R08p06_row_09
  · exact R08p06_row_10
  · exact R08p06_row_11
  · exact R08p06_row_12
  · exact R08p06_row_13
  · exact R08p06_row_14
  · exact R08p06_row_15
  · exact R08p06_row_16
  · exact R08p06_row_17
  · exact R08p06_row_18
  · exact R08p06_row_19
  · exact R08p06_row_20
  · exact R08p06_row_21

private theorem R08p06_column_00 : reversePack 32 (fun j : Fin 22 => R08p06_digit j 0)=R08p06_columnCode 0 := by decide +kernel

private theorem R08p06_column_01 : reversePack 32 (fun j : Fin 22 => R08p06_digit j 1)=R08p06_columnCode 1 := by decide +kernel

private theorem R08p06_column_02 : reversePack 32 (fun j : Fin 22 => R08p06_digit j 2)=R08p06_columnCode 2 := by decide +kernel

private theorem R08p06_column_03 : reversePack 32 (fun j : Fin 22 => R08p06_digit j 3)=R08p06_columnCode 3 := by decide +kernel

private theorem R08p06_column_04 : reversePack 32 (fun j : Fin 22 => R08p06_digit j 4)=R08p06_columnCode 4 := by decide +kernel

private theorem R08p06_column_05 : reversePack 32 (fun j : Fin 22 => R08p06_digit j 5)=R08p06_columnCode 5 := by decide +kernel

private theorem R08p06_column_06 : reversePack 32 (fun j : Fin 22 => R08p06_digit j 6)=R08p06_columnCode 6 := by decide +kernel

private theorem R08p06_column_07 : reversePack 32 (fun j : Fin 22 => R08p06_digit j 7)=R08p06_columnCode 7 := by decide +kernel

private theorem R08p06_column_08 : reversePack 32 (fun j : Fin 22 => R08p06_digit j 8)=R08p06_columnCode 8 := by decide +kernel

private theorem R08p06_column_09 : reversePack 32 (fun j : Fin 22 => R08p06_digit j 9)=R08p06_columnCode 9 := by decide +kernel

private theorem R08p06_column_10 : reversePack 32 (fun j : Fin 22 => R08p06_digit j 10)=R08p06_columnCode 10 := by decide +kernel

private theorem R08p06_column_11 : reversePack 32 (fun j : Fin 22 => R08p06_digit j 11)=R08p06_columnCode 11 := by decide +kernel

private theorem R08p06_column_12 : reversePack 32 (fun j : Fin 22 => R08p06_digit j 12)=R08p06_columnCode 12 := by decide +kernel

private theorem R08p06_column_13 : reversePack 32 (fun j : Fin 22 => R08p06_digit j 13)=R08p06_columnCode 13 := by decide +kernel

private theorem R08p06_column_14 : reversePack 32 (fun j : Fin 22 => R08p06_digit j 14)=R08p06_columnCode 14 := by decide +kernel

private theorem R08p06_column_15 : reversePack 32 (fun j : Fin 22 => R08p06_digit j 15)=R08p06_columnCode 15 := by decide +kernel

private theorem R08p06_column_16 : reversePack 32 (fun j : Fin 22 => R08p06_digit j 16)=R08p06_columnCode 16 := by decide +kernel

private theorem R08p06_column_17 : reversePack 32 (fun j : Fin 22 => R08p06_digit j 17)=R08p06_columnCode 17 := by decide +kernel

private theorem R08p06_column_18 : reversePack 32 (fun j : Fin 22 => R08p06_digit j 18)=R08p06_columnCode 18 := by decide +kernel

private theorem R08p06_column_19 : reversePack 32 (fun j : Fin 22 => R08p06_digit j 19)=R08p06_columnCode 19 := by decide +kernel

private theorem R08p06_column_20 : reversePack 32 (fun j : Fin 22 => R08p06_digit j 20)=R08p06_columnCode 20 := by decide +kernel

private theorem R08p06_column_21 : reversePack 32 (fun j : Fin 22 => R08p06_digit j 21)=R08p06_columnCode 21 := by decide +kernel

theorem R08p06_column_binding : ∀ i : Fin 22,reversePack 32 (fun j : Fin 22 => R08p06_digit j i)=R08p06_columnCode i := by
  intro i
  fin_cases i
  · exact R08p06_column_00
  · exact R08p06_column_01
  · exact R08p06_column_02
  · exact R08p06_column_03
  · exact R08p06_column_04
  · exact R08p06_column_05
  · exact R08p06_column_06
  · exact R08p06_column_07
  · exact R08p06_column_08
  · exact R08p06_column_09
  · exact R08p06_column_10
  · exact R08p06_column_11
  · exact R08p06_column_12
  · exact R08p06_column_13
  · exact R08p06_column_14
  · exact R08p06_column_15
  · exact R08p06_column_16
  · exact R08p06_column_17
  · exact R08p06_column_18
  · exact R08p06_column_19
  · exact R08p06_column_20
  · exact R08p06_column_21

def R08p06_data : PackedData 22 2 32 where
  raw := R08p06_digit
  digit_lt := R08p06_bound
  rowCode := R08p06_rowCode
  columnCode := R08p06_columnCode
  row_binding := R08p06_row_binding
  column_binding := R08p06_column_binding

def R08p07_lowColumnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1082187
  | 1 => 950892
  | 2 => 2146625
  | 3 => 917792
  | 4 => 2660525
  | 5 => 1986734
  | 6 => 1595828
  | 7 => 2131998
  | 8 => 20650
  | 9 => 3195721
  | 10 => 2043765
  | 11 => 3065965
  | 12 => 3199305
  | 13 => 2763637
  | 14 => 3123772
  | 15 => 917504
  | 16 => 3416064
  | 17 => 1034860
  | 18 => 2532115
  | 19 => 425984
  | 20 => 1026102
  | 21 => 2097152
  | _ => 0

def R08p07_rowCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1237940077368979808224019457
  | 1 => 1268888540267514782905507250177
  | 2 => 1267689287071979333227518099488
  | 3 => 38686808008275470905770017
  | 4 => 1268888541485001016571773059072
  | 5 => 1267689287071979334292670021664
  | 6 => 38685664311267666914444321
  | 7 => 1100619972608
  | 8 => 1237940077332951012277781505
  | 9 => 1276626882999318357599060001
  | 10 => 1125899906842624
  | 11 => 1267689287071979333227484545024
  | 12 => 1152922605226819584
  | 13 => 1268889750410820631165514285056
  | 14 => 38685627416654720207422464
  | 15 => 1308541308332655224939734893601
  | 16 => 1267689287035049816247611949056
  | 17 => 1308541346147328745220916412448
  | 18 => 1308542555036254871702672015392
  | 19 => 1267689324850911196150320103456
  | 20 => 1208926973697219167780865
  | 21 => 40566058357487119937183765496832
  | _ => 0

def R08p07_columnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 41833707785387833902276366303264
  | 1 => 40853268002321948163689186304
  | 2 => 40564819245119166199034516865025
  | 3 => 1208962713102776594891776
  | 4 => 40605672438706170793398112355329
  | 5 => 1308503831631058221133693223968
  | 6 => 39653977026665721543006356512
  | 7 => 1308541307150875744602945486849
  | 8 => 1268889750373926052336920166400
  | 9 => 40566057185159604500814022836257
  | 10 => 40604473220929535727859699581984
  | 11 => 40605672475304511000487851492353
  | 12 => 40566057185158451614493788078113
  | 13 => 40604473220929499699062647030785
  | 14 => 40891915849618880339570099201
  | 15 => 1082368
  | 16 => 1099511660577
  | 17 => 40853268002323074097989321728
  | 18 => 41832508493195844328277408776193
  | 19 => 1074823168
  | 20 => 1307304576037409980056767333376
  | 21 => 1
  | _ => 0

def R08p07_digit (i j : Fin 22) : ℕ := packedDigit 1 (R08p07_lowColumnCode j) i.val

private theorem R08p07_bound_00 : ∀ j : Fin 22,R08p07_digit 0 j<2 := by decide +kernel

private theorem R08p07_bound_01 : ∀ j : Fin 22,R08p07_digit 1 j<2 := by decide +kernel

private theorem R08p07_bound_02 : ∀ j : Fin 22,R08p07_digit 2 j<2 := by decide +kernel

private theorem R08p07_bound_03 : ∀ j : Fin 22,R08p07_digit 3 j<2 := by decide +kernel

private theorem R08p07_bound_04 : ∀ j : Fin 22,R08p07_digit 4 j<2 := by decide +kernel

private theorem R08p07_bound_05 : ∀ j : Fin 22,R08p07_digit 5 j<2 := by decide +kernel

private theorem R08p07_bound_06 : ∀ j : Fin 22,R08p07_digit 6 j<2 := by decide +kernel

private theorem R08p07_bound_07 : ∀ j : Fin 22,R08p07_digit 7 j<2 := by decide +kernel

private theorem R08p07_bound_08 : ∀ j : Fin 22,R08p07_digit 8 j<2 := by decide +kernel

private theorem R08p07_bound_09 : ∀ j : Fin 22,R08p07_digit 9 j<2 := by decide +kernel

private theorem R08p07_bound_10 : ∀ j : Fin 22,R08p07_digit 10 j<2 := by decide +kernel

private theorem R08p07_bound_11 : ∀ j : Fin 22,R08p07_digit 11 j<2 := by decide +kernel

private theorem R08p07_bound_12 : ∀ j : Fin 22,R08p07_digit 12 j<2 := by decide +kernel

private theorem R08p07_bound_13 : ∀ j : Fin 22,R08p07_digit 13 j<2 := by decide +kernel

private theorem R08p07_bound_14 : ∀ j : Fin 22,R08p07_digit 14 j<2 := by decide +kernel

private theorem R08p07_bound_15 : ∀ j : Fin 22,R08p07_digit 15 j<2 := by decide +kernel

private theorem R08p07_bound_16 : ∀ j : Fin 22,R08p07_digit 16 j<2 := by decide +kernel

private theorem R08p07_bound_17 : ∀ j : Fin 22,R08p07_digit 17 j<2 := by decide +kernel

private theorem R08p07_bound_18 : ∀ j : Fin 22,R08p07_digit 18 j<2 := by decide +kernel

private theorem R08p07_bound_19 : ∀ j : Fin 22,R08p07_digit 19 j<2 := by decide +kernel

private theorem R08p07_bound_20 : ∀ j : Fin 22,R08p07_digit 20 j<2 := by decide +kernel

private theorem R08p07_bound_21 : ∀ j : Fin 22,R08p07_digit 21 j<2 := by decide +kernel

theorem R08p07_bound : ∀ i j : Fin 22,R08p07_digit i j<2 := by
  intro i j
  fin_cases i
  · exact R08p07_bound_00 j
  · exact R08p07_bound_01 j
  · exact R08p07_bound_02 j
  · exact R08p07_bound_03 j
  · exact R08p07_bound_04 j
  · exact R08p07_bound_05 j
  · exact R08p07_bound_06 j
  · exact R08p07_bound_07 j
  · exact R08p07_bound_08 j
  · exact R08p07_bound_09 j
  · exact R08p07_bound_10 j
  · exact R08p07_bound_11 j
  · exact R08p07_bound_12 j
  · exact R08p07_bound_13 j
  · exact R08p07_bound_14 j
  · exact R08p07_bound_15 j
  · exact R08p07_bound_16 j
  · exact R08p07_bound_17 j
  · exact R08p07_bound_18 j
  · exact R08p07_bound_19 j
  · exact R08p07_bound_20 j
  · exact R08p07_bound_21 j

private theorem R08p07_row_00 : pack 32 (R08p07_digit 0)=R08p07_rowCode 0 := by decide +kernel

private theorem R08p07_row_01 : pack 32 (R08p07_digit 1)=R08p07_rowCode 1 := by decide +kernel

private theorem R08p07_row_02 : pack 32 (R08p07_digit 2)=R08p07_rowCode 2 := by decide +kernel

private theorem R08p07_row_03 : pack 32 (R08p07_digit 3)=R08p07_rowCode 3 := by decide +kernel

private theorem R08p07_row_04 : pack 32 (R08p07_digit 4)=R08p07_rowCode 4 := by decide +kernel

private theorem R08p07_row_05 : pack 32 (R08p07_digit 5)=R08p07_rowCode 5 := by decide +kernel

private theorem R08p07_row_06 : pack 32 (R08p07_digit 6)=R08p07_rowCode 6 := by decide +kernel

private theorem R08p07_row_07 : pack 32 (R08p07_digit 7)=R08p07_rowCode 7 := by decide +kernel

private theorem R08p07_row_08 : pack 32 (R08p07_digit 8)=R08p07_rowCode 8 := by decide +kernel

private theorem R08p07_row_09 : pack 32 (R08p07_digit 9)=R08p07_rowCode 9 := by decide +kernel

private theorem R08p07_row_10 : pack 32 (R08p07_digit 10)=R08p07_rowCode 10 := by decide +kernel

private theorem R08p07_row_11 : pack 32 (R08p07_digit 11)=R08p07_rowCode 11 := by decide +kernel

private theorem R08p07_row_12 : pack 32 (R08p07_digit 12)=R08p07_rowCode 12 := by decide +kernel

private theorem R08p07_row_13 : pack 32 (R08p07_digit 13)=R08p07_rowCode 13 := by decide +kernel

private theorem R08p07_row_14 : pack 32 (R08p07_digit 14)=R08p07_rowCode 14 := by decide +kernel

private theorem R08p07_row_15 : pack 32 (R08p07_digit 15)=R08p07_rowCode 15 := by decide +kernel

private theorem R08p07_row_16 : pack 32 (R08p07_digit 16)=R08p07_rowCode 16 := by decide +kernel

private theorem R08p07_row_17 : pack 32 (R08p07_digit 17)=R08p07_rowCode 17 := by decide +kernel

private theorem R08p07_row_18 : pack 32 (R08p07_digit 18)=R08p07_rowCode 18 := by decide +kernel

private theorem R08p07_row_19 : pack 32 (R08p07_digit 19)=R08p07_rowCode 19 := by decide +kernel

private theorem R08p07_row_20 : pack 32 (R08p07_digit 20)=R08p07_rowCode 20 := by decide +kernel

private theorem R08p07_row_21 : pack 32 (R08p07_digit 21)=R08p07_rowCode 21 := by decide +kernel

theorem R08p07_row_binding : ∀ i : Fin 22,pack 32 (R08p07_digit i)=R08p07_rowCode i := by
  intro i
  fin_cases i
  · exact R08p07_row_00
  · exact R08p07_row_01
  · exact R08p07_row_02
  · exact R08p07_row_03
  · exact R08p07_row_04
  · exact R08p07_row_05
  · exact R08p07_row_06
  · exact R08p07_row_07
  · exact R08p07_row_08
  · exact R08p07_row_09
  · exact R08p07_row_10
  · exact R08p07_row_11
  · exact R08p07_row_12
  · exact R08p07_row_13
  · exact R08p07_row_14
  · exact R08p07_row_15
  · exact R08p07_row_16
  · exact R08p07_row_17
  · exact R08p07_row_18
  · exact R08p07_row_19
  · exact R08p07_row_20
  · exact R08p07_row_21

private theorem R08p07_column_00 : reversePack 32 (fun j : Fin 22 => R08p07_digit j 0)=R08p07_columnCode 0 := by decide +kernel

private theorem R08p07_column_01 : reversePack 32 (fun j : Fin 22 => R08p07_digit j 1)=R08p07_columnCode 1 := by decide +kernel

private theorem R08p07_column_02 : reversePack 32 (fun j : Fin 22 => R08p07_digit j 2)=R08p07_columnCode 2 := by decide +kernel

private theorem R08p07_column_03 : reversePack 32 (fun j : Fin 22 => R08p07_digit j 3)=R08p07_columnCode 3 := by decide +kernel

private theorem R08p07_column_04 : reversePack 32 (fun j : Fin 22 => R08p07_digit j 4)=R08p07_columnCode 4 := by decide +kernel

private theorem R08p07_column_05 : reversePack 32 (fun j : Fin 22 => R08p07_digit j 5)=R08p07_columnCode 5 := by decide +kernel

private theorem R08p07_column_06 : reversePack 32 (fun j : Fin 22 => R08p07_digit j 6)=R08p07_columnCode 6 := by decide +kernel

private theorem R08p07_column_07 : reversePack 32 (fun j : Fin 22 => R08p07_digit j 7)=R08p07_columnCode 7 := by decide +kernel

private theorem R08p07_column_08 : reversePack 32 (fun j : Fin 22 => R08p07_digit j 8)=R08p07_columnCode 8 := by decide +kernel

private theorem R08p07_column_09 : reversePack 32 (fun j : Fin 22 => R08p07_digit j 9)=R08p07_columnCode 9 := by decide +kernel

private theorem R08p07_column_10 : reversePack 32 (fun j : Fin 22 => R08p07_digit j 10)=R08p07_columnCode 10 := by decide +kernel

private theorem R08p07_column_11 : reversePack 32 (fun j : Fin 22 => R08p07_digit j 11)=R08p07_columnCode 11 := by decide +kernel

private theorem R08p07_column_12 : reversePack 32 (fun j : Fin 22 => R08p07_digit j 12)=R08p07_columnCode 12 := by decide +kernel

private theorem R08p07_column_13 : reversePack 32 (fun j : Fin 22 => R08p07_digit j 13)=R08p07_columnCode 13 := by decide +kernel

private theorem R08p07_column_14 : reversePack 32 (fun j : Fin 22 => R08p07_digit j 14)=R08p07_columnCode 14 := by decide +kernel

private theorem R08p07_column_15 : reversePack 32 (fun j : Fin 22 => R08p07_digit j 15)=R08p07_columnCode 15 := by decide +kernel

private theorem R08p07_column_16 : reversePack 32 (fun j : Fin 22 => R08p07_digit j 16)=R08p07_columnCode 16 := by decide +kernel

private theorem R08p07_column_17 : reversePack 32 (fun j : Fin 22 => R08p07_digit j 17)=R08p07_columnCode 17 := by decide +kernel

private theorem R08p07_column_18 : reversePack 32 (fun j : Fin 22 => R08p07_digit j 18)=R08p07_columnCode 18 := by decide +kernel

private theorem R08p07_column_19 : reversePack 32 (fun j : Fin 22 => R08p07_digit j 19)=R08p07_columnCode 19 := by decide +kernel

private theorem R08p07_column_20 : reversePack 32 (fun j : Fin 22 => R08p07_digit j 20)=R08p07_columnCode 20 := by decide +kernel

private theorem R08p07_column_21 : reversePack 32 (fun j : Fin 22 => R08p07_digit j 21)=R08p07_columnCode 21 := by decide +kernel

theorem R08p07_column_binding : ∀ i : Fin 22,reversePack 32 (fun j : Fin 22 => R08p07_digit j i)=R08p07_columnCode i := by
  intro i
  fin_cases i
  · exact R08p07_column_00
  · exact R08p07_column_01
  · exact R08p07_column_02
  · exact R08p07_column_03
  · exact R08p07_column_04
  · exact R08p07_column_05
  · exact R08p07_column_06
  · exact R08p07_column_07
  · exact R08p07_column_08
  · exact R08p07_column_09
  · exact R08p07_column_10
  · exact R08p07_column_11
  · exact R08p07_column_12
  · exact R08p07_column_13
  · exact R08p07_column_14
  · exact R08p07_column_15
  · exact R08p07_column_16
  · exact R08p07_column_17
  · exact R08p07_column_18
  · exact R08p07_column_19
  · exact R08p07_column_20
  · exact R08p07_column_21

def R08p07_data : PackedData 22 2 32 where
  raw := R08p07_digit
  digit_lt := R08p07_bound
  rowCode := R08p07_rowCode
  columnCode := R08p07_columnCode
  row_binding := R08p07_row_binding
  column_binding := R08p07_column_binding

def R08e02_lowColumnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 3760742
  | 1 => 3793741
  | 2 => 598121
  | 3 => 3271035
  | 4 => 3539646
  | 5 => 2203777
  | 6 => 936664
  | 7 => 529101
  | 8 => 2171017
  | 9 => 3689014
  | 10 => 2223482
  | 11 => 3719454
  | 12 => 3692598
  | 13 => 256298
  | 14 => 1696076
  | 15 => 3139967
  | 16 => 2302032
  | 17 => 827676
  | 18 => 2836579
  | 19 => 2582911
  | 20 => 631113
  | 21 => 2097152
  | _ => 0

def R08e02_rowCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1308502659303578814659440968736
  | 1 => 40852059113433011562157735937
  | 2 => 39652805844072306125294272545
  | 3 => 1307303406108043366080929891360
  | 4 => 39654013589301425903678554112
  | 5 => 40852059113396982765138772993
  | 6 => 1308503869409991174807462380577
  | 7 => 1134979710976
  | 8 => 1307303406108043364945983733792
  | 9 => 35219806617633
  | 10 => 1125899906842624
  | 11 => 40852059113396982766211465216
  | 12 => 1152921538966585344
  | 13 => 1307304615033826951877684659233
  | 14 => 40852060294024632280641732641
  | 15 => 1267689324850911196149245313056
  | 16 => 1308503869446884664018993185825
  | 17 => 40853268038062514806501408768
  | 18 => 39652804662291699888599072768
  | 19 => 1268927264854454919101197321249
  | 20 => 1181780606203410284577
  | 21 => 40605672475305699987037961093153
  | _ => 0

def R08e02_columnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1307265928191265970518323364897
  | 1 => 40605671266416736670710339994657
  | 2 => 40566058394047377706855283295232
  | 3 => 41833747679938729390568336523297
  | 4 => 1308542517258438775553158840353
  | 5 => 40564819208483932469712532799489
  | 6 => 1276664626190579521937245184
  | 7 => 40605671267560434837329725621248
  | 8 => 40566057148523217849986358181889
  | 9 => 1307304576038562900495113913377
  | 10 => 1268928472635424571470852915201
  | 11 => 1308541307187768106884817486881
  | 12 => 1307304576037410014174879155233
  | 13 => 1268889749230229011583082692608
  | 14 => 40852059112242901311230575648
  | 15 => 41873361761195861559365109580801
  | 16 => 38723405159532190298537985
  | 17 => 40890706959538706453266203648
  | 18 => 41832471054236322852911843378177
  | 19 => 41873361761195861559364035837953
  | 20 => 40566057185158451580374601434112
  | 21 => 1
  | _ => 0

def R08e02_digit (i j : Fin 22) : ℕ := packedDigit 1 (R08e02_lowColumnCode j) i.val

private theorem R08e02_bound_00 : ∀ j : Fin 22,R08e02_digit 0 j<2 := by decide +kernel

private theorem R08e02_bound_01 : ∀ j : Fin 22,R08e02_digit 1 j<2 := by decide +kernel

private theorem R08e02_bound_02 : ∀ j : Fin 22,R08e02_digit 2 j<2 := by decide +kernel

private theorem R08e02_bound_03 : ∀ j : Fin 22,R08e02_digit 3 j<2 := by decide +kernel

private theorem R08e02_bound_04 : ∀ j : Fin 22,R08e02_digit 4 j<2 := by decide +kernel

private theorem R08e02_bound_05 : ∀ j : Fin 22,R08e02_digit 5 j<2 := by decide +kernel

private theorem R08e02_bound_06 : ∀ j : Fin 22,R08e02_digit 6 j<2 := by decide +kernel

private theorem R08e02_bound_07 : ∀ j : Fin 22,R08e02_digit 7 j<2 := by decide +kernel

private theorem R08e02_bound_08 : ∀ j : Fin 22,R08e02_digit 8 j<2 := by decide +kernel

private theorem R08e02_bound_09 : ∀ j : Fin 22,R08e02_digit 9 j<2 := by decide +kernel

private theorem R08e02_bound_10 : ∀ j : Fin 22,R08e02_digit 10 j<2 := by decide +kernel

private theorem R08e02_bound_11 : ∀ j : Fin 22,R08e02_digit 11 j<2 := by decide +kernel

private theorem R08e02_bound_12 : ∀ j : Fin 22,R08e02_digit 12 j<2 := by decide +kernel

private theorem R08e02_bound_13 : ∀ j : Fin 22,R08e02_digit 13 j<2 := by decide +kernel

private theorem R08e02_bound_14 : ∀ j : Fin 22,R08e02_digit 14 j<2 := by decide +kernel

private theorem R08e02_bound_15 : ∀ j : Fin 22,R08e02_digit 15 j<2 := by decide +kernel

private theorem R08e02_bound_16 : ∀ j : Fin 22,R08e02_digit 16 j<2 := by decide +kernel

private theorem R08e02_bound_17 : ∀ j : Fin 22,R08e02_digit 17 j<2 := by decide +kernel

private theorem R08e02_bound_18 : ∀ j : Fin 22,R08e02_digit 18 j<2 := by decide +kernel

private theorem R08e02_bound_19 : ∀ j : Fin 22,R08e02_digit 19 j<2 := by decide +kernel

private theorem R08e02_bound_20 : ∀ j : Fin 22,R08e02_digit 20 j<2 := by decide +kernel

private theorem R08e02_bound_21 : ∀ j : Fin 22,R08e02_digit 21 j<2 := by decide +kernel

theorem R08e02_bound : ∀ i j : Fin 22,R08e02_digit i j<2 := by
  intro i j
  fin_cases i
  · exact R08e02_bound_00 j
  · exact R08e02_bound_01 j
  · exact R08e02_bound_02 j
  · exact R08e02_bound_03 j
  · exact R08e02_bound_04 j
  · exact R08e02_bound_05 j
  · exact R08e02_bound_06 j
  · exact R08e02_bound_07 j
  · exact R08e02_bound_08 j
  · exact R08e02_bound_09 j
  · exact R08e02_bound_10 j
  · exact R08e02_bound_11 j
  · exact R08e02_bound_12 j
  · exact R08e02_bound_13 j
  · exact R08e02_bound_14 j
  · exact R08e02_bound_15 j
  · exact R08e02_bound_16 j
  · exact R08e02_bound_17 j
  · exact R08e02_bound_18 j
  · exact R08e02_bound_19 j
  · exact R08e02_bound_20 j
  · exact R08e02_bound_21 j

private theorem R08e02_row_00 : pack 32 (R08e02_digit 0)=R08e02_rowCode 0 := by decide +kernel

private theorem R08e02_row_01 : pack 32 (R08e02_digit 1)=R08e02_rowCode 1 := by decide +kernel

private theorem R08e02_row_02 : pack 32 (R08e02_digit 2)=R08e02_rowCode 2 := by decide +kernel

private theorem R08e02_row_03 : pack 32 (R08e02_digit 3)=R08e02_rowCode 3 := by decide +kernel

private theorem R08e02_row_04 : pack 32 (R08e02_digit 4)=R08e02_rowCode 4 := by decide +kernel

private theorem R08e02_row_05 : pack 32 (R08e02_digit 5)=R08e02_rowCode 5 := by decide +kernel

private theorem R08e02_row_06 : pack 32 (R08e02_digit 6)=R08e02_rowCode 6 := by decide +kernel

private theorem R08e02_row_07 : pack 32 (R08e02_digit 7)=R08e02_rowCode 7 := by decide +kernel

private theorem R08e02_row_08 : pack 32 (R08e02_digit 8)=R08e02_rowCode 8 := by decide +kernel

private theorem R08e02_row_09 : pack 32 (R08e02_digit 9)=R08e02_rowCode 9 := by decide +kernel

private theorem R08e02_row_10 : pack 32 (R08e02_digit 10)=R08e02_rowCode 10 := by decide +kernel

private theorem R08e02_row_11 : pack 32 (R08e02_digit 11)=R08e02_rowCode 11 := by decide +kernel

private theorem R08e02_row_12 : pack 32 (R08e02_digit 12)=R08e02_rowCode 12 := by decide +kernel

private theorem R08e02_row_13 : pack 32 (R08e02_digit 13)=R08e02_rowCode 13 := by decide +kernel

private theorem R08e02_row_14 : pack 32 (R08e02_digit 14)=R08e02_rowCode 14 := by decide +kernel

private theorem R08e02_row_15 : pack 32 (R08e02_digit 15)=R08e02_rowCode 15 := by decide +kernel

private theorem R08e02_row_16 : pack 32 (R08e02_digit 16)=R08e02_rowCode 16 := by decide +kernel

private theorem R08e02_row_17 : pack 32 (R08e02_digit 17)=R08e02_rowCode 17 := by decide +kernel

private theorem R08e02_row_18 : pack 32 (R08e02_digit 18)=R08e02_rowCode 18 := by decide +kernel

private theorem R08e02_row_19 : pack 32 (R08e02_digit 19)=R08e02_rowCode 19 := by decide +kernel

private theorem R08e02_row_20 : pack 32 (R08e02_digit 20)=R08e02_rowCode 20 := by decide +kernel

private theorem R08e02_row_21 : pack 32 (R08e02_digit 21)=R08e02_rowCode 21 := by decide +kernel

theorem R08e02_row_binding : ∀ i : Fin 22,pack 32 (R08e02_digit i)=R08e02_rowCode i := by
  intro i
  fin_cases i
  · exact R08e02_row_00
  · exact R08e02_row_01
  · exact R08e02_row_02
  · exact R08e02_row_03
  · exact R08e02_row_04
  · exact R08e02_row_05
  · exact R08e02_row_06
  · exact R08e02_row_07
  · exact R08e02_row_08
  · exact R08e02_row_09
  · exact R08e02_row_10
  · exact R08e02_row_11
  · exact R08e02_row_12
  · exact R08e02_row_13
  · exact R08e02_row_14
  · exact R08e02_row_15
  · exact R08e02_row_16
  · exact R08e02_row_17
  · exact R08e02_row_18
  · exact R08e02_row_19
  · exact R08e02_row_20
  · exact R08e02_row_21

private theorem R08e02_column_00 : reversePack 32 (fun j : Fin 22 => R08e02_digit j 0)=R08e02_columnCode 0 := by decide +kernel

private theorem R08e02_column_01 : reversePack 32 (fun j : Fin 22 => R08e02_digit j 1)=R08e02_columnCode 1 := by decide +kernel

private theorem R08e02_column_02 : reversePack 32 (fun j : Fin 22 => R08e02_digit j 2)=R08e02_columnCode 2 := by decide +kernel

private theorem R08e02_column_03 : reversePack 32 (fun j : Fin 22 => R08e02_digit j 3)=R08e02_columnCode 3 := by decide +kernel

private theorem R08e02_column_04 : reversePack 32 (fun j : Fin 22 => R08e02_digit j 4)=R08e02_columnCode 4 := by decide +kernel

private theorem R08e02_column_05 : reversePack 32 (fun j : Fin 22 => R08e02_digit j 5)=R08e02_columnCode 5 := by decide +kernel

private theorem R08e02_column_06 : reversePack 32 (fun j : Fin 22 => R08e02_digit j 6)=R08e02_columnCode 6 := by decide +kernel

private theorem R08e02_column_07 : reversePack 32 (fun j : Fin 22 => R08e02_digit j 7)=R08e02_columnCode 7 := by decide +kernel

private theorem R08e02_column_08 : reversePack 32 (fun j : Fin 22 => R08e02_digit j 8)=R08e02_columnCode 8 := by decide +kernel

private theorem R08e02_column_09 : reversePack 32 (fun j : Fin 22 => R08e02_digit j 9)=R08e02_columnCode 9 := by decide +kernel

private theorem R08e02_column_10 : reversePack 32 (fun j : Fin 22 => R08e02_digit j 10)=R08e02_columnCode 10 := by decide +kernel

private theorem R08e02_column_11 : reversePack 32 (fun j : Fin 22 => R08e02_digit j 11)=R08e02_columnCode 11 := by decide +kernel

private theorem R08e02_column_12 : reversePack 32 (fun j : Fin 22 => R08e02_digit j 12)=R08e02_columnCode 12 := by decide +kernel

private theorem R08e02_column_13 : reversePack 32 (fun j : Fin 22 => R08e02_digit j 13)=R08e02_columnCode 13 := by decide +kernel

private theorem R08e02_column_14 : reversePack 32 (fun j : Fin 22 => R08e02_digit j 14)=R08e02_columnCode 14 := by decide +kernel

private theorem R08e02_column_15 : reversePack 32 (fun j : Fin 22 => R08e02_digit j 15)=R08e02_columnCode 15 := by decide +kernel

private theorem R08e02_column_16 : reversePack 32 (fun j : Fin 22 => R08e02_digit j 16)=R08e02_columnCode 16 := by decide +kernel

private theorem R08e02_column_17 : reversePack 32 (fun j : Fin 22 => R08e02_digit j 17)=R08e02_columnCode 17 := by decide +kernel

private theorem R08e02_column_18 : reversePack 32 (fun j : Fin 22 => R08e02_digit j 18)=R08e02_columnCode 18 := by decide +kernel

private theorem R08e02_column_19 : reversePack 32 (fun j : Fin 22 => R08e02_digit j 19)=R08e02_columnCode 19 := by decide +kernel

private theorem R08e02_column_20 : reversePack 32 (fun j : Fin 22 => R08e02_digit j 20)=R08e02_columnCode 20 := by decide +kernel

private theorem R08e02_column_21 : reversePack 32 (fun j : Fin 22 => R08e02_digit j 21)=R08e02_columnCode 21 := by decide +kernel

theorem R08e02_column_binding : ∀ i : Fin 22,reversePack 32 (fun j : Fin 22 => R08e02_digit j i)=R08e02_columnCode i := by
  intro i
  fin_cases i
  · exact R08e02_column_00
  · exact R08e02_column_01
  · exact R08e02_column_02
  · exact R08e02_column_03
  · exact R08e02_column_04
  · exact R08e02_column_05
  · exact R08e02_column_06
  · exact R08e02_column_07
  · exact R08e02_column_08
  · exact R08e02_column_09
  · exact R08e02_column_10
  · exact R08e02_column_11
  · exact R08e02_column_12
  · exact R08e02_column_13
  · exact R08e02_column_14
  · exact R08e02_column_15
  · exact R08e02_column_16
  · exact R08e02_column_17
  · exact R08e02_column_18
  · exact R08e02_column_19
  · exact R08e02_column_20
  · exact R08e02_column_21

def R08e02_data : PackedData 22 2 32 where
  raw := R08e02_digit
  digit_lt := R08e02_bound
  rowCode := R08e02_rowCode
  columnCode := R08e02_columnCode
  row_binding := R08e02_row_binding
  column_binding := R08e02_column_binding

def R09p05_lowColumnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 3396058
  | 1 => 246394
  | 2 => 3392261
  | 3 => 3943527
  | 4 => 2598283
  | 5 => 938231
  | 6 => 1804391
  | 7 => 2032212
  | 8 => 1336832
  | 9 => 279373
  | 10 => 1649484
  | 11 => 1917772
  | 12 => 2908777
  | 13 => 830244
  | 14 => 1294427
  | 15 => 3945447
  | 16 => 1220608
  | 17 => 1862198
  | 18 => 5280
  | 19 => 1377361
  | 20 => 1193153
  | 21 => 600118
  | _ => 0

def R09p05_rowCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1307264720446038010658135507968
  | 1 => 40564857931889091999703774560289
  | 2 => 40564857930745431057049438946304
  | 3 => 1181781732103317094433
  | 4 => 40604471975367292305576669741089
  | 5 => 40566095870785832168913287282720
  | 6 => 1307264720446075165389420003361
  | 7 => 1268888578046446644728798642177
  | 8 => 37815862540985879757825
  | 9 => 38723443243131757947520032
  | 10 => 1308502621524646951667887013888
  | 11 => 40564857892966463130076492890112
  | 12 => 1268888578046446644728797593601
  | 13 => 41832509739900596931762578292736
  | 14 => 38686808008275436544984097
  | 15 => 1210143304723495079904289
  | 16 => 40604433289741101792141046187041
  | 17 => 1267651810334640636878757299233
  | 18 => 39652804700374174654847287296
  | 19 => 40564857930746583943369673703424
  | 20 => 1307304614996969492562684445697
  | 21 => 37780084784461769638913
  | _ => 0

def R09p05_columnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1268927264890159456947025215521
  | 1 => 1268928472599646849031604273152
  | 2 => 40604433288598519426378768580641
  | 3 => 41872085135493491051570751636513
  | 4 => 41833707748788376768428574277633
  | 5 => 41872123822300273219844048978944
  | 6 => 41872085135493455021675329356832
  | 7 => 39652804663444621392165766176
  | 8 => 1188951435497209888
  | 9 => 40605671266416736669609721102336
  | 10 => 40852059113396948680310785056
  | 11 => 40852059113395821715252085792
  | 12 => 40566058394048530628394216358913
  | 13 => 39615290220999320078464877568
  | 14 => 41833746470976015160792325292064
  | 15 => 41872085136712091962427635172385
  | 16 => 1100586418208
  | 17 => 1307304576038562901594625573920
  | 18 => 1210106447299327977062400
  | 19 => 40564857930708536407782307430432
  | 20 => 40564819246262900396649979314208
  | 21 => 1307304576037409980055692510208
  | _ => 0

def R09p05_digit (i j : Fin 22) : ℕ := packedDigit 1 (R09p05_lowColumnCode j) i.val

private theorem R09p05_bound_00 : ∀ j : Fin 22,R09p05_digit 0 j<2 := by decide +kernel

private theorem R09p05_bound_01 : ∀ j : Fin 22,R09p05_digit 1 j<2 := by decide +kernel

private theorem R09p05_bound_02 : ∀ j : Fin 22,R09p05_digit 2 j<2 := by decide +kernel

private theorem R09p05_bound_03 : ∀ j : Fin 22,R09p05_digit 3 j<2 := by decide +kernel

private theorem R09p05_bound_04 : ∀ j : Fin 22,R09p05_digit 4 j<2 := by decide +kernel

private theorem R09p05_bound_05 : ∀ j : Fin 22,R09p05_digit 5 j<2 := by decide +kernel

private theorem R09p05_bound_06 : ∀ j : Fin 22,R09p05_digit 6 j<2 := by decide +kernel

private theorem R09p05_bound_07 : ∀ j : Fin 22,R09p05_digit 7 j<2 := by decide +kernel

private theorem R09p05_bound_08 : ∀ j : Fin 22,R09p05_digit 8 j<2 := by decide +kernel

private theorem R09p05_bound_09 : ∀ j : Fin 22,R09p05_digit 9 j<2 := by decide +kernel

private theorem R09p05_bound_10 : ∀ j : Fin 22,R09p05_digit 10 j<2 := by decide +kernel

private theorem R09p05_bound_11 : ∀ j : Fin 22,R09p05_digit 11 j<2 := by decide +kernel

private theorem R09p05_bound_12 : ∀ j : Fin 22,R09p05_digit 12 j<2 := by decide +kernel

private theorem R09p05_bound_13 : ∀ j : Fin 22,R09p05_digit 13 j<2 := by decide +kernel

private theorem R09p05_bound_14 : ∀ j : Fin 22,R09p05_digit 14 j<2 := by decide +kernel

private theorem R09p05_bound_15 : ∀ j : Fin 22,R09p05_digit 15 j<2 := by decide +kernel

private theorem R09p05_bound_16 : ∀ j : Fin 22,R09p05_digit 16 j<2 := by decide +kernel

private theorem R09p05_bound_17 : ∀ j : Fin 22,R09p05_digit 17 j<2 := by decide +kernel

private theorem R09p05_bound_18 : ∀ j : Fin 22,R09p05_digit 18 j<2 := by decide +kernel

private theorem R09p05_bound_19 : ∀ j : Fin 22,R09p05_digit 19 j<2 := by decide +kernel

private theorem R09p05_bound_20 : ∀ j : Fin 22,R09p05_digit 20 j<2 := by decide +kernel

private theorem R09p05_bound_21 : ∀ j : Fin 22,R09p05_digit 21 j<2 := by decide +kernel

theorem R09p05_bound : ∀ i j : Fin 22,R09p05_digit i j<2 := by
  intro i j
  fin_cases i
  · exact R09p05_bound_00 j
  · exact R09p05_bound_01 j
  · exact R09p05_bound_02 j
  · exact R09p05_bound_03 j
  · exact R09p05_bound_04 j
  · exact R09p05_bound_05 j
  · exact R09p05_bound_06 j
  · exact R09p05_bound_07 j
  · exact R09p05_bound_08 j
  · exact R09p05_bound_09 j
  · exact R09p05_bound_10 j
  · exact R09p05_bound_11 j
  · exact R09p05_bound_12 j
  · exact R09p05_bound_13 j
  · exact R09p05_bound_14 j
  · exact R09p05_bound_15 j
  · exact R09p05_bound_16 j
  · exact R09p05_bound_17 j
  · exact R09p05_bound_18 j
  · exact R09p05_bound_19 j
  · exact R09p05_bound_20 j
  · exact R09p05_bound_21 j

private theorem R09p05_row_00 : pack 32 (R09p05_digit 0)=R09p05_rowCode 0 := by decide +kernel

private theorem R09p05_row_01 : pack 32 (R09p05_digit 1)=R09p05_rowCode 1 := by decide +kernel

private theorem R09p05_row_02 : pack 32 (R09p05_digit 2)=R09p05_rowCode 2 := by decide +kernel

private theorem R09p05_row_03 : pack 32 (R09p05_digit 3)=R09p05_rowCode 3 := by decide +kernel

private theorem R09p05_row_04 : pack 32 (R09p05_digit 4)=R09p05_rowCode 4 := by decide +kernel

private theorem R09p05_row_05 : pack 32 (R09p05_digit 5)=R09p05_rowCode 5 := by decide +kernel

private theorem R09p05_row_06 : pack 32 (R09p05_digit 6)=R09p05_rowCode 6 := by decide +kernel

private theorem R09p05_row_07 : pack 32 (R09p05_digit 7)=R09p05_rowCode 7 := by decide +kernel

private theorem R09p05_row_08 : pack 32 (R09p05_digit 8)=R09p05_rowCode 8 := by decide +kernel

private theorem R09p05_row_09 : pack 32 (R09p05_digit 9)=R09p05_rowCode 9 := by decide +kernel

private theorem R09p05_row_10 : pack 32 (R09p05_digit 10)=R09p05_rowCode 10 := by decide +kernel

private theorem R09p05_row_11 : pack 32 (R09p05_digit 11)=R09p05_rowCode 11 := by decide +kernel

private theorem R09p05_row_12 : pack 32 (R09p05_digit 12)=R09p05_rowCode 12 := by decide +kernel

private theorem R09p05_row_13 : pack 32 (R09p05_digit 13)=R09p05_rowCode 13 := by decide +kernel

private theorem R09p05_row_14 : pack 32 (R09p05_digit 14)=R09p05_rowCode 14 := by decide +kernel

private theorem R09p05_row_15 : pack 32 (R09p05_digit 15)=R09p05_rowCode 15 := by decide +kernel

private theorem R09p05_row_16 : pack 32 (R09p05_digit 16)=R09p05_rowCode 16 := by decide +kernel

private theorem R09p05_row_17 : pack 32 (R09p05_digit 17)=R09p05_rowCode 17 := by decide +kernel

private theorem R09p05_row_18 : pack 32 (R09p05_digit 18)=R09p05_rowCode 18 := by decide +kernel

private theorem R09p05_row_19 : pack 32 (R09p05_digit 19)=R09p05_rowCode 19 := by decide +kernel

private theorem R09p05_row_20 : pack 32 (R09p05_digit 20)=R09p05_rowCode 20 := by decide +kernel

private theorem R09p05_row_21 : pack 32 (R09p05_digit 21)=R09p05_rowCode 21 := by decide +kernel

theorem R09p05_row_binding : ∀ i : Fin 22,pack 32 (R09p05_digit i)=R09p05_rowCode i := by
  intro i
  fin_cases i
  · exact R09p05_row_00
  · exact R09p05_row_01
  · exact R09p05_row_02
  · exact R09p05_row_03
  · exact R09p05_row_04
  · exact R09p05_row_05
  · exact R09p05_row_06
  · exact R09p05_row_07
  · exact R09p05_row_08
  · exact R09p05_row_09
  · exact R09p05_row_10
  · exact R09p05_row_11
  · exact R09p05_row_12
  · exact R09p05_row_13
  · exact R09p05_row_14
  · exact R09p05_row_15
  · exact R09p05_row_16
  · exact R09p05_row_17
  · exact R09p05_row_18
  · exact R09p05_row_19
  · exact R09p05_row_20
  · exact R09p05_row_21

private theorem R09p05_column_00 : reversePack 32 (fun j : Fin 22 => R09p05_digit j 0)=R09p05_columnCode 0 := by decide +kernel

private theorem R09p05_column_01 : reversePack 32 (fun j : Fin 22 => R09p05_digit j 1)=R09p05_columnCode 1 := by decide +kernel

private theorem R09p05_column_02 : reversePack 32 (fun j : Fin 22 => R09p05_digit j 2)=R09p05_columnCode 2 := by decide +kernel

private theorem R09p05_column_03 : reversePack 32 (fun j : Fin 22 => R09p05_digit j 3)=R09p05_columnCode 3 := by decide +kernel

private theorem R09p05_column_04 : reversePack 32 (fun j : Fin 22 => R09p05_digit j 4)=R09p05_columnCode 4 := by decide +kernel

private theorem R09p05_column_05 : reversePack 32 (fun j : Fin 22 => R09p05_digit j 5)=R09p05_columnCode 5 := by decide +kernel

private theorem R09p05_column_06 : reversePack 32 (fun j : Fin 22 => R09p05_digit j 6)=R09p05_columnCode 6 := by decide +kernel

private theorem R09p05_column_07 : reversePack 32 (fun j : Fin 22 => R09p05_digit j 7)=R09p05_columnCode 7 := by decide +kernel

private theorem R09p05_column_08 : reversePack 32 (fun j : Fin 22 => R09p05_digit j 8)=R09p05_columnCode 8 := by decide +kernel

private theorem R09p05_column_09 : reversePack 32 (fun j : Fin 22 => R09p05_digit j 9)=R09p05_columnCode 9 := by decide +kernel

private theorem R09p05_column_10 : reversePack 32 (fun j : Fin 22 => R09p05_digit j 10)=R09p05_columnCode 10 := by decide +kernel

private theorem R09p05_column_11 : reversePack 32 (fun j : Fin 22 => R09p05_digit j 11)=R09p05_columnCode 11 := by decide +kernel

private theorem R09p05_column_12 : reversePack 32 (fun j : Fin 22 => R09p05_digit j 12)=R09p05_columnCode 12 := by decide +kernel

private theorem R09p05_column_13 : reversePack 32 (fun j : Fin 22 => R09p05_digit j 13)=R09p05_columnCode 13 := by decide +kernel

private theorem R09p05_column_14 : reversePack 32 (fun j : Fin 22 => R09p05_digit j 14)=R09p05_columnCode 14 := by decide +kernel

private theorem R09p05_column_15 : reversePack 32 (fun j : Fin 22 => R09p05_digit j 15)=R09p05_columnCode 15 := by decide +kernel

private theorem R09p05_column_16 : reversePack 32 (fun j : Fin 22 => R09p05_digit j 16)=R09p05_columnCode 16 := by decide +kernel

private theorem R09p05_column_17 : reversePack 32 (fun j : Fin 22 => R09p05_digit j 17)=R09p05_columnCode 17 := by decide +kernel

private theorem R09p05_column_18 : reversePack 32 (fun j : Fin 22 => R09p05_digit j 18)=R09p05_columnCode 18 := by decide +kernel

private theorem R09p05_column_19 : reversePack 32 (fun j : Fin 22 => R09p05_digit j 19)=R09p05_columnCode 19 := by decide +kernel

private theorem R09p05_column_20 : reversePack 32 (fun j : Fin 22 => R09p05_digit j 20)=R09p05_columnCode 20 := by decide +kernel

private theorem R09p05_column_21 : reversePack 32 (fun j : Fin 22 => R09p05_digit j 21)=R09p05_columnCode 21 := by decide +kernel

theorem R09p05_column_binding : ∀ i : Fin 22,reversePack 32 (fun j : Fin 22 => R09p05_digit j i)=R09p05_columnCode i := by
  intro i
  fin_cases i
  · exact R09p05_column_00
  · exact R09p05_column_01
  · exact R09p05_column_02
  · exact R09p05_column_03
  · exact R09p05_column_04
  · exact R09p05_column_05
  · exact R09p05_column_06
  · exact R09p05_column_07
  · exact R09p05_column_08
  · exact R09p05_column_09
  · exact R09p05_column_10
  · exact R09p05_column_11
  · exact R09p05_column_12
  · exact R09p05_column_13
  · exact R09p05_column_14
  · exact R09p05_column_15
  · exact R09p05_column_16
  · exact R09p05_column_17
  · exact R09p05_column_18
  · exact R09p05_column_19
  · exact R09p05_column_20
  · exact R09p05_column_21

def R09p05_data : PackedData 22 2 32 where
  raw := R09p05_digit
  digit_lt := R09p05_bound
  rowCode := R09p05_rowCode
  columnCode := R09p05_columnCode
  row_binding := R09p05_row_binding
  column_binding := R09p05_column_binding

end SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoCaches08
