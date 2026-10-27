import SymmetricSubgroupAsymptotics.MatrixKroneckerProductReflection
import Mathlib.Tactic.FinCases

/-! Fixed Co2 binary22 shared caches. Every digit and pack binding is kernel checked. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoCaches10
open MatrixKroneckerProductReflection MatrixKroneckerDotReflection
open MatrixNaturalRowDotReflection SmallNaturalMatrixProductReflection

def R09p10_lowColumnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 3518656
  | 1 => 4051953
  | 2 => 2330818
  | 3 => 1630851
  | 4 => 3552048
  | 5 => 2134739
  | 6 => 3604480
  | 7 => 3883080
  | 8 => 3424979
  | 9 => 1441876
  | 10 => 3153920
  | 11 => 3539747
  | 12 => 219888
  | 13 => 3543472
  | 14 => 3528867
  | 15 => 344576
  | 16 => 1048576
  | 17 => 3182083
  | 18 => 1817459
  | 19 => 57987
  | 20 => 552960
  | 21 => 1549171
  | _ => 0

def R09p10_rowCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 40605709915406613715713739751456
  | 1 => 40605709915406613715713739752448
  | 2 => 35184372088832
  | 3 => 34359738368
  | 4 => 40566057147380672674105345966112
  | 5 => 40566057148561300287335858962464
  | 6 => 40566057147343779185992285553697
  | 7 => 39614082475770200265754444833
  | 8 => 40566057147379555745113840812064
  | 9 => 40605709952006106879458098053152
  | 10 => 38685626227668133590597632
  | 11 => 1276626847257590630507872256
  | 12 => 1268888541486152812141074187297
  | 13 => 41873321828827988924362784800769
  | 14 => 1307264720446037976606526439456
  | 15 => 40605709915406577685817209160737
  | 16 => 40566057186303302633384015037473
  | 17 => 40566057147380708701838253229056
  | 18 => 40564819246299793884798472159265
  | 19 => 1268888540267514781805962100768
  | 20 => 40566097043112195810813241491489
  | 21 => 38686843749932830326522913
  | _ => 0

def R09p10_columnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 38959523519959564058657
  | 1 => 40564859140852958059203705996321
  | 2 => 1267650639187752920356756652033
  | 3 => 41832469808713314792748169036832
  | 4 => 39894590093728698676052001
  | 5 => 41832508532118474357889422065665
  | 6 => 34635809
  | 7 => 1237977818217243266455176225
  | 8 => 41832508532118474322738336006177
  | 9 => 39652804662291699887525363744
  | 10 => 1099511627809
  | 11 => 41832471016495436273672407515169
  | 12 => 39933512724849060618436608
  | 13 => 39895769532426811968880673
  | 14 => 41832471017637982645857537785889
  | 15 => 1152921539000172544
  | 16 => 32
  | 17 => 41832469807532760325593812172833
  | 18 => 41832509739900596966948057646112
  | 19 => 41832469808713314792748169035776
  | 20 => 36318243456000
  | 21 => 41832509739900595805863778746400
  | _ => 0

def R09p10_digit (i j : Fin 22) : ℕ := packedDigit 1 (R09p10_lowColumnCode j) i.val

private theorem R09p10_bound_00 : ∀ j : Fin 22,R09p10_digit 0 j<2 := by decide +kernel

private theorem R09p10_bound_01 : ∀ j : Fin 22,R09p10_digit 1 j<2 := by decide +kernel

private theorem R09p10_bound_02 : ∀ j : Fin 22,R09p10_digit 2 j<2 := by decide +kernel

private theorem R09p10_bound_03 : ∀ j : Fin 22,R09p10_digit 3 j<2 := by decide +kernel

private theorem R09p10_bound_04 : ∀ j : Fin 22,R09p10_digit 4 j<2 := by decide +kernel

private theorem R09p10_bound_05 : ∀ j : Fin 22,R09p10_digit 5 j<2 := by decide +kernel

private theorem R09p10_bound_06 : ∀ j : Fin 22,R09p10_digit 6 j<2 := by decide +kernel

private theorem R09p10_bound_07 : ∀ j : Fin 22,R09p10_digit 7 j<2 := by decide +kernel

private theorem R09p10_bound_08 : ∀ j : Fin 22,R09p10_digit 8 j<2 := by decide +kernel

private theorem R09p10_bound_09 : ∀ j : Fin 22,R09p10_digit 9 j<2 := by decide +kernel

private theorem R09p10_bound_10 : ∀ j : Fin 22,R09p10_digit 10 j<2 := by decide +kernel

private theorem R09p10_bound_11 : ∀ j : Fin 22,R09p10_digit 11 j<2 := by decide +kernel

private theorem R09p10_bound_12 : ∀ j : Fin 22,R09p10_digit 12 j<2 := by decide +kernel

private theorem R09p10_bound_13 : ∀ j : Fin 22,R09p10_digit 13 j<2 := by decide +kernel

private theorem R09p10_bound_14 : ∀ j : Fin 22,R09p10_digit 14 j<2 := by decide +kernel

private theorem R09p10_bound_15 : ∀ j : Fin 22,R09p10_digit 15 j<2 := by decide +kernel

private theorem R09p10_bound_16 : ∀ j : Fin 22,R09p10_digit 16 j<2 := by decide +kernel

private theorem R09p10_bound_17 : ∀ j : Fin 22,R09p10_digit 17 j<2 := by decide +kernel

private theorem R09p10_bound_18 : ∀ j : Fin 22,R09p10_digit 18 j<2 := by decide +kernel

private theorem R09p10_bound_19 : ∀ j : Fin 22,R09p10_digit 19 j<2 := by decide +kernel

private theorem R09p10_bound_20 : ∀ j : Fin 22,R09p10_digit 20 j<2 := by decide +kernel

private theorem R09p10_bound_21 : ∀ j : Fin 22,R09p10_digit 21 j<2 := by decide +kernel

theorem R09p10_bound : ∀ i j : Fin 22,R09p10_digit i j<2 := by
  intro i j
  fin_cases i
  · exact R09p10_bound_00 j
  · exact R09p10_bound_01 j
  · exact R09p10_bound_02 j
  · exact R09p10_bound_03 j
  · exact R09p10_bound_04 j
  · exact R09p10_bound_05 j
  · exact R09p10_bound_06 j
  · exact R09p10_bound_07 j
  · exact R09p10_bound_08 j
  · exact R09p10_bound_09 j
  · exact R09p10_bound_10 j
  · exact R09p10_bound_11 j
  · exact R09p10_bound_12 j
  · exact R09p10_bound_13 j
  · exact R09p10_bound_14 j
  · exact R09p10_bound_15 j
  · exact R09p10_bound_16 j
  · exact R09p10_bound_17 j
  · exact R09p10_bound_18 j
  · exact R09p10_bound_19 j
  · exact R09p10_bound_20 j
  · exact R09p10_bound_21 j

private theorem R09p10_row_00 : pack 32 (R09p10_digit 0)=R09p10_rowCode 0 := by decide +kernel

private theorem R09p10_row_01 : pack 32 (R09p10_digit 1)=R09p10_rowCode 1 := by decide +kernel

private theorem R09p10_row_02 : pack 32 (R09p10_digit 2)=R09p10_rowCode 2 := by decide +kernel

private theorem R09p10_row_03 : pack 32 (R09p10_digit 3)=R09p10_rowCode 3 := by decide +kernel

private theorem R09p10_row_04 : pack 32 (R09p10_digit 4)=R09p10_rowCode 4 := by decide +kernel

private theorem R09p10_row_05 : pack 32 (R09p10_digit 5)=R09p10_rowCode 5 := by decide +kernel

private theorem R09p10_row_06 : pack 32 (R09p10_digit 6)=R09p10_rowCode 6 := by decide +kernel

private theorem R09p10_row_07 : pack 32 (R09p10_digit 7)=R09p10_rowCode 7 := by decide +kernel

private theorem R09p10_row_08 : pack 32 (R09p10_digit 8)=R09p10_rowCode 8 := by decide +kernel

private theorem R09p10_row_09 : pack 32 (R09p10_digit 9)=R09p10_rowCode 9 := by decide +kernel

private theorem R09p10_row_10 : pack 32 (R09p10_digit 10)=R09p10_rowCode 10 := by decide +kernel

private theorem R09p10_row_11 : pack 32 (R09p10_digit 11)=R09p10_rowCode 11 := by decide +kernel

private theorem R09p10_row_12 : pack 32 (R09p10_digit 12)=R09p10_rowCode 12 := by decide +kernel

private theorem R09p10_row_13 : pack 32 (R09p10_digit 13)=R09p10_rowCode 13 := by decide +kernel

private theorem R09p10_row_14 : pack 32 (R09p10_digit 14)=R09p10_rowCode 14 := by decide +kernel

private theorem R09p10_row_15 : pack 32 (R09p10_digit 15)=R09p10_rowCode 15 := by decide +kernel

private theorem R09p10_row_16 : pack 32 (R09p10_digit 16)=R09p10_rowCode 16 := by decide +kernel

private theorem R09p10_row_17 : pack 32 (R09p10_digit 17)=R09p10_rowCode 17 := by decide +kernel

private theorem R09p10_row_18 : pack 32 (R09p10_digit 18)=R09p10_rowCode 18 := by decide +kernel

private theorem R09p10_row_19 : pack 32 (R09p10_digit 19)=R09p10_rowCode 19 := by decide +kernel

private theorem R09p10_row_20 : pack 32 (R09p10_digit 20)=R09p10_rowCode 20 := by decide +kernel

private theorem R09p10_row_21 : pack 32 (R09p10_digit 21)=R09p10_rowCode 21 := by decide +kernel

theorem R09p10_row_binding : ∀ i : Fin 22,pack 32 (R09p10_digit i)=R09p10_rowCode i := by
  intro i
  fin_cases i
  · exact R09p10_row_00
  · exact R09p10_row_01
  · exact R09p10_row_02
  · exact R09p10_row_03
  · exact R09p10_row_04
  · exact R09p10_row_05
  · exact R09p10_row_06
  · exact R09p10_row_07
  · exact R09p10_row_08
  · exact R09p10_row_09
  · exact R09p10_row_10
  · exact R09p10_row_11
  · exact R09p10_row_12
  · exact R09p10_row_13
  · exact R09p10_row_14
  · exact R09p10_row_15
  · exact R09p10_row_16
  · exact R09p10_row_17
  · exact R09p10_row_18
  · exact R09p10_row_19
  · exact R09p10_row_20
  · exact R09p10_row_21

private theorem R09p10_column_00 : reversePack 32 (fun j : Fin 22 => R09p10_digit j 0)=R09p10_columnCode 0 := by decide +kernel

private theorem R09p10_column_01 : reversePack 32 (fun j : Fin 22 => R09p10_digit j 1)=R09p10_columnCode 1 := by decide +kernel

private theorem R09p10_column_02 : reversePack 32 (fun j : Fin 22 => R09p10_digit j 2)=R09p10_columnCode 2 := by decide +kernel

private theorem R09p10_column_03 : reversePack 32 (fun j : Fin 22 => R09p10_digit j 3)=R09p10_columnCode 3 := by decide +kernel

private theorem R09p10_column_04 : reversePack 32 (fun j : Fin 22 => R09p10_digit j 4)=R09p10_columnCode 4 := by decide +kernel

private theorem R09p10_column_05 : reversePack 32 (fun j : Fin 22 => R09p10_digit j 5)=R09p10_columnCode 5 := by decide +kernel

private theorem R09p10_column_06 : reversePack 32 (fun j : Fin 22 => R09p10_digit j 6)=R09p10_columnCode 6 := by decide +kernel

private theorem R09p10_column_07 : reversePack 32 (fun j : Fin 22 => R09p10_digit j 7)=R09p10_columnCode 7 := by decide +kernel

private theorem R09p10_column_08 : reversePack 32 (fun j : Fin 22 => R09p10_digit j 8)=R09p10_columnCode 8 := by decide +kernel

private theorem R09p10_column_09 : reversePack 32 (fun j : Fin 22 => R09p10_digit j 9)=R09p10_columnCode 9 := by decide +kernel

private theorem R09p10_column_10 : reversePack 32 (fun j : Fin 22 => R09p10_digit j 10)=R09p10_columnCode 10 := by decide +kernel

private theorem R09p10_column_11 : reversePack 32 (fun j : Fin 22 => R09p10_digit j 11)=R09p10_columnCode 11 := by decide +kernel

private theorem R09p10_column_12 : reversePack 32 (fun j : Fin 22 => R09p10_digit j 12)=R09p10_columnCode 12 := by decide +kernel

private theorem R09p10_column_13 : reversePack 32 (fun j : Fin 22 => R09p10_digit j 13)=R09p10_columnCode 13 := by decide +kernel

private theorem R09p10_column_14 : reversePack 32 (fun j : Fin 22 => R09p10_digit j 14)=R09p10_columnCode 14 := by decide +kernel

private theorem R09p10_column_15 : reversePack 32 (fun j : Fin 22 => R09p10_digit j 15)=R09p10_columnCode 15 := by decide +kernel

private theorem R09p10_column_16 : reversePack 32 (fun j : Fin 22 => R09p10_digit j 16)=R09p10_columnCode 16 := by decide +kernel

private theorem R09p10_column_17 : reversePack 32 (fun j : Fin 22 => R09p10_digit j 17)=R09p10_columnCode 17 := by decide +kernel

private theorem R09p10_column_18 : reversePack 32 (fun j : Fin 22 => R09p10_digit j 18)=R09p10_columnCode 18 := by decide +kernel

private theorem R09p10_column_19 : reversePack 32 (fun j : Fin 22 => R09p10_digit j 19)=R09p10_columnCode 19 := by decide +kernel

private theorem R09p10_column_20 : reversePack 32 (fun j : Fin 22 => R09p10_digit j 20)=R09p10_columnCode 20 := by decide +kernel

private theorem R09p10_column_21 : reversePack 32 (fun j : Fin 22 => R09p10_digit j 21)=R09p10_columnCode 21 := by decide +kernel

theorem R09p10_column_binding : ∀ i : Fin 22,reversePack 32 (fun j : Fin 22 => R09p10_digit j i)=R09p10_columnCode i := by
  intro i
  fin_cases i
  · exact R09p10_column_00
  · exact R09p10_column_01
  · exact R09p10_column_02
  · exact R09p10_column_03
  · exact R09p10_column_04
  · exact R09p10_column_05
  · exact R09p10_column_06
  · exact R09p10_column_07
  · exact R09p10_column_08
  · exact R09p10_column_09
  · exact R09p10_column_10
  · exact R09p10_column_11
  · exact R09p10_column_12
  · exact R09p10_column_13
  · exact R09p10_column_14
  · exact R09p10_column_15
  · exact R09p10_column_16
  · exact R09p10_column_17
  · exact R09p10_column_18
  · exact R09p10_column_19
  · exact R09p10_column_20
  · exact R09p10_column_21

def R09p10_data : PackedData 22 2 32 where
  raw := R09p10_digit
  digit_lt := R09p10_bound
  rowCode := R09p10_rowCode
  columnCode := R09p10_columnCode
  row_binding := R09p10_row_binding
  column_binding := R09p10_column_binding

def R09p11_lowColumnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 906226
  | 1 => 2441586
  | 2 => 4035064
  | 3 => 569844
  | 4 => 406323
  | 5 => 1960784
  | 6 => 405936
  | 7 => 3367280
  | 8 => 1813376
  | 9 => 1831840
  | 10 => 1629699
  | 11 => 3484371
  | 12 => 414499
  | 13 => 2667139
  | 14 => 3051936
  | 15 => 4072307
  | 16 => 475632
  | 17 => 2077315
  | 18 => 147952
  | 19 => 1601536
  | 20 => 1048576
  | 21 => 561795
  | _ => 0

def R09p11_rowCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 40564857930746583943334207684608
  | 1 => 40564857930746583943334207684641
  | 2 => 32768
  | 3 => 1024
  | 4 => 1239186744072886693722620961
  | 5 => 1239187925781435303060341793
  | 6 => 1239186744072886692647830561
  | 7 => 40566097043112194684878973862913
  | 8 => 1239187925781436402605524001
  | 9 => 40564857930746583979618124955649
  | 10 => 1125899906842624
  | 11 => 37155796470988800
  | 12 => 40604471975405339876279656154113
  | 13 => 39652804699221253151314182144
  | 14 => 40853230223391246324124876833
  | 15 => 40564857894147054787076747723777
  | 16 => 39894552083347878061278241
  | 17 => 1277873552009104536162533376
  | 18 => 39933512759716740072473633
  | 19 => 40604472013183118818830681408513
  | 20 => 1307303404890558292399430304768
  | 21 => 38996453000653370819616
  | _ => 0

def R09p11_columnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1267690533777846612805906629632
  | 1 => 1267690532596102035398442647553
  | 2 => 1277873587749670045135963169
  | 3 => 39654014805596459666486854656
  | 4 => 41832509702121663978089881829376
  | 5 => 38723443207067777663796256
  | 6 => 39895769532427911480508416
  | 7 => 39932367872635001252085793
  | 8 => 1218639157369964069920
  | 9 => 1210144457681317963760672
  | 10 => 41832469807532760360812544001056
  | 11 => 41832508532118475449703428292641
  | 12 => 41832471016495436308891139342336
  | 13 => 41832469808713314827898181387265
  | 14 => 1210143304758679452025857
  | 15 => 41832509739900595805862671451169
  | 16 => 39933548464254619151794176
  | 17 => 41832469808713314827898216023072
  | 18 => 39933548464254619118206976
  | 19 => 36318243456032
  | 20 => 32
  | 21 => 41832469808713314826798669759488
  | _ => 0

def R09p11_digit (i j : Fin 22) : ℕ := packedDigit 1 (R09p11_lowColumnCode j) i.val

private theorem R09p11_bound_00 : ∀ j : Fin 22,R09p11_digit 0 j<2 := by decide +kernel

private theorem R09p11_bound_01 : ∀ j : Fin 22,R09p11_digit 1 j<2 := by decide +kernel

private theorem R09p11_bound_02 : ∀ j : Fin 22,R09p11_digit 2 j<2 := by decide +kernel

private theorem R09p11_bound_03 : ∀ j : Fin 22,R09p11_digit 3 j<2 := by decide +kernel

private theorem R09p11_bound_04 : ∀ j : Fin 22,R09p11_digit 4 j<2 := by decide +kernel

private theorem R09p11_bound_05 : ∀ j : Fin 22,R09p11_digit 5 j<2 := by decide +kernel

private theorem R09p11_bound_06 : ∀ j : Fin 22,R09p11_digit 6 j<2 := by decide +kernel

private theorem R09p11_bound_07 : ∀ j : Fin 22,R09p11_digit 7 j<2 := by decide +kernel

private theorem R09p11_bound_08 : ∀ j : Fin 22,R09p11_digit 8 j<2 := by decide +kernel

private theorem R09p11_bound_09 : ∀ j : Fin 22,R09p11_digit 9 j<2 := by decide +kernel

private theorem R09p11_bound_10 : ∀ j : Fin 22,R09p11_digit 10 j<2 := by decide +kernel

private theorem R09p11_bound_11 : ∀ j : Fin 22,R09p11_digit 11 j<2 := by decide +kernel

private theorem R09p11_bound_12 : ∀ j : Fin 22,R09p11_digit 12 j<2 := by decide +kernel

private theorem R09p11_bound_13 : ∀ j : Fin 22,R09p11_digit 13 j<2 := by decide +kernel

private theorem R09p11_bound_14 : ∀ j : Fin 22,R09p11_digit 14 j<2 := by decide +kernel

private theorem R09p11_bound_15 : ∀ j : Fin 22,R09p11_digit 15 j<2 := by decide +kernel

private theorem R09p11_bound_16 : ∀ j : Fin 22,R09p11_digit 16 j<2 := by decide +kernel

private theorem R09p11_bound_17 : ∀ j : Fin 22,R09p11_digit 17 j<2 := by decide +kernel

private theorem R09p11_bound_18 : ∀ j : Fin 22,R09p11_digit 18 j<2 := by decide +kernel

private theorem R09p11_bound_19 : ∀ j : Fin 22,R09p11_digit 19 j<2 := by decide +kernel

private theorem R09p11_bound_20 : ∀ j : Fin 22,R09p11_digit 20 j<2 := by decide +kernel

private theorem R09p11_bound_21 : ∀ j : Fin 22,R09p11_digit 21 j<2 := by decide +kernel

theorem R09p11_bound : ∀ i j : Fin 22,R09p11_digit i j<2 := by
  intro i j
  fin_cases i
  · exact R09p11_bound_00 j
  · exact R09p11_bound_01 j
  · exact R09p11_bound_02 j
  · exact R09p11_bound_03 j
  · exact R09p11_bound_04 j
  · exact R09p11_bound_05 j
  · exact R09p11_bound_06 j
  · exact R09p11_bound_07 j
  · exact R09p11_bound_08 j
  · exact R09p11_bound_09 j
  · exact R09p11_bound_10 j
  · exact R09p11_bound_11 j
  · exact R09p11_bound_12 j
  · exact R09p11_bound_13 j
  · exact R09p11_bound_14 j
  · exact R09p11_bound_15 j
  · exact R09p11_bound_16 j
  · exact R09p11_bound_17 j
  · exact R09p11_bound_18 j
  · exact R09p11_bound_19 j
  · exact R09p11_bound_20 j
  · exact R09p11_bound_21 j

private theorem R09p11_row_00 : pack 32 (R09p11_digit 0)=R09p11_rowCode 0 := by decide +kernel

private theorem R09p11_row_01 : pack 32 (R09p11_digit 1)=R09p11_rowCode 1 := by decide +kernel

private theorem R09p11_row_02 : pack 32 (R09p11_digit 2)=R09p11_rowCode 2 := by decide +kernel

private theorem R09p11_row_03 : pack 32 (R09p11_digit 3)=R09p11_rowCode 3 := by decide +kernel

private theorem R09p11_row_04 : pack 32 (R09p11_digit 4)=R09p11_rowCode 4 := by decide +kernel

private theorem R09p11_row_05 : pack 32 (R09p11_digit 5)=R09p11_rowCode 5 := by decide +kernel

private theorem R09p11_row_06 : pack 32 (R09p11_digit 6)=R09p11_rowCode 6 := by decide +kernel

private theorem R09p11_row_07 : pack 32 (R09p11_digit 7)=R09p11_rowCode 7 := by decide +kernel

private theorem R09p11_row_08 : pack 32 (R09p11_digit 8)=R09p11_rowCode 8 := by decide +kernel

private theorem R09p11_row_09 : pack 32 (R09p11_digit 9)=R09p11_rowCode 9 := by decide +kernel

private theorem R09p11_row_10 : pack 32 (R09p11_digit 10)=R09p11_rowCode 10 := by decide +kernel

private theorem R09p11_row_11 : pack 32 (R09p11_digit 11)=R09p11_rowCode 11 := by decide +kernel

private theorem R09p11_row_12 : pack 32 (R09p11_digit 12)=R09p11_rowCode 12 := by decide +kernel

private theorem R09p11_row_13 : pack 32 (R09p11_digit 13)=R09p11_rowCode 13 := by decide +kernel

private theorem R09p11_row_14 : pack 32 (R09p11_digit 14)=R09p11_rowCode 14 := by decide +kernel

private theorem R09p11_row_15 : pack 32 (R09p11_digit 15)=R09p11_rowCode 15 := by decide +kernel

private theorem R09p11_row_16 : pack 32 (R09p11_digit 16)=R09p11_rowCode 16 := by decide +kernel

private theorem R09p11_row_17 : pack 32 (R09p11_digit 17)=R09p11_rowCode 17 := by decide +kernel

private theorem R09p11_row_18 : pack 32 (R09p11_digit 18)=R09p11_rowCode 18 := by decide +kernel

private theorem R09p11_row_19 : pack 32 (R09p11_digit 19)=R09p11_rowCode 19 := by decide +kernel

private theorem R09p11_row_20 : pack 32 (R09p11_digit 20)=R09p11_rowCode 20 := by decide +kernel

private theorem R09p11_row_21 : pack 32 (R09p11_digit 21)=R09p11_rowCode 21 := by decide +kernel

theorem R09p11_row_binding : ∀ i : Fin 22,pack 32 (R09p11_digit i)=R09p11_rowCode i := by
  intro i
  fin_cases i
  · exact R09p11_row_00
  · exact R09p11_row_01
  · exact R09p11_row_02
  · exact R09p11_row_03
  · exact R09p11_row_04
  · exact R09p11_row_05
  · exact R09p11_row_06
  · exact R09p11_row_07
  · exact R09p11_row_08
  · exact R09p11_row_09
  · exact R09p11_row_10
  · exact R09p11_row_11
  · exact R09p11_row_12
  · exact R09p11_row_13
  · exact R09p11_row_14
  · exact R09p11_row_15
  · exact R09p11_row_16
  · exact R09p11_row_17
  · exact R09p11_row_18
  · exact R09p11_row_19
  · exact R09p11_row_20
  · exact R09p11_row_21

private theorem R09p11_column_00 : reversePack 32 (fun j : Fin 22 => R09p11_digit j 0)=R09p11_columnCode 0 := by decide +kernel

private theorem R09p11_column_01 : reversePack 32 (fun j : Fin 22 => R09p11_digit j 1)=R09p11_columnCode 1 := by decide +kernel

private theorem R09p11_column_02 : reversePack 32 (fun j : Fin 22 => R09p11_digit j 2)=R09p11_columnCode 2 := by decide +kernel

private theorem R09p11_column_03 : reversePack 32 (fun j : Fin 22 => R09p11_digit j 3)=R09p11_columnCode 3 := by decide +kernel

private theorem R09p11_column_04 : reversePack 32 (fun j : Fin 22 => R09p11_digit j 4)=R09p11_columnCode 4 := by decide +kernel

private theorem R09p11_column_05 : reversePack 32 (fun j : Fin 22 => R09p11_digit j 5)=R09p11_columnCode 5 := by decide +kernel

private theorem R09p11_column_06 : reversePack 32 (fun j : Fin 22 => R09p11_digit j 6)=R09p11_columnCode 6 := by decide +kernel

private theorem R09p11_column_07 : reversePack 32 (fun j : Fin 22 => R09p11_digit j 7)=R09p11_columnCode 7 := by decide +kernel

private theorem R09p11_column_08 : reversePack 32 (fun j : Fin 22 => R09p11_digit j 8)=R09p11_columnCode 8 := by decide +kernel

private theorem R09p11_column_09 : reversePack 32 (fun j : Fin 22 => R09p11_digit j 9)=R09p11_columnCode 9 := by decide +kernel

private theorem R09p11_column_10 : reversePack 32 (fun j : Fin 22 => R09p11_digit j 10)=R09p11_columnCode 10 := by decide +kernel

private theorem R09p11_column_11 : reversePack 32 (fun j : Fin 22 => R09p11_digit j 11)=R09p11_columnCode 11 := by decide +kernel

private theorem R09p11_column_12 : reversePack 32 (fun j : Fin 22 => R09p11_digit j 12)=R09p11_columnCode 12 := by decide +kernel

private theorem R09p11_column_13 : reversePack 32 (fun j : Fin 22 => R09p11_digit j 13)=R09p11_columnCode 13 := by decide +kernel

private theorem R09p11_column_14 : reversePack 32 (fun j : Fin 22 => R09p11_digit j 14)=R09p11_columnCode 14 := by decide +kernel

private theorem R09p11_column_15 : reversePack 32 (fun j : Fin 22 => R09p11_digit j 15)=R09p11_columnCode 15 := by decide +kernel

private theorem R09p11_column_16 : reversePack 32 (fun j : Fin 22 => R09p11_digit j 16)=R09p11_columnCode 16 := by decide +kernel

private theorem R09p11_column_17 : reversePack 32 (fun j : Fin 22 => R09p11_digit j 17)=R09p11_columnCode 17 := by decide +kernel

private theorem R09p11_column_18 : reversePack 32 (fun j : Fin 22 => R09p11_digit j 18)=R09p11_columnCode 18 := by decide +kernel

private theorem R09p11_column_19 : reversePack 32 (fun j : Fin 22 => R09p11_digit j 19)=R09p11_columnCode 19 := by decide +kernel

private theorem R09p11_column_20 : reversePack 32 (fun j : Fin 22 => R09p11_digit j 20)=R09p11_columnCode 20 := by decide +kernel

private theorem R09p11_column_21 : reversePack 32 (fun j : Fin 22 => R09p11_digit j 21)=R09p11_columnCode 21 := by decide +kernel

theorem R09p11_column_binding : ∀ i : Fin 22,reversePack 32 (fun j : Fin 22 => R09p11_digit j i)=R09p11_columnCode i := by
  intro i
  fin_cases i
  · exact R09p11_column_00
  · exact R09p11_column_01
  · exact R09p11_column_02
  · exact R09p11_column_03
  · exact R09p11_column_04
  · exact R09p11_column_05
  · exact R09p11_column_06
  · exact R09p11_column_07
  · exact R09p11_column_08
  · exact R09p11_column_09
  · exact R09p11_column_10
  · exact R09p11_column_11
  · exact R09p11_column_12
  · exact R09p11_column_13
  · exact R09p11_column_14
  · exact R09p11_column_15
  · exact R09p11_column_16
  · exact R09p11_column_17
  · exact R09p11_column_18
  · exact R09p11_column_19
  · exact R09p11_column_20
  · exact R09p11_column_21

def R09p11_data : PackedData 22 2 32 where
  raw := R09p11_digit
  digit_lt := R09p11_bound
  rowCode := R09p11_rowCode
  columnCode := R09p11_columnCode
  row_binding := R09p11_row_binding
  column_binding := R09p11_column_binding

def R10p01_lowColumnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 2097280
  | 1 => 16897
  | 2 => 2097283
  | 3 => 3047424
  | 4 => 3571848
  | 5 => 3178500
  | 6 => 294912
  | 7 => 2152512
  | 8 => 2260992
  | 9 => 1086336
  | 10 => 2381968
  | 11 => 1315488
  | 12 => 2130432
  | 13 => 2393088
  | 14 => 2361344
  | 15 => 2134016
  | 16 => 2097152
  | 17 => 1146880
  | 18 => 180224
  | 19 => 2523136
  | 20 => 1220608
  | 21 => 1048576
  | _ => 0

def R10p01_rowCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1056
  | 1 => 1024
  | 2 => 33554432
  | 3 => 1048576
  | 4 => 1125899906842624
  | 5 => 36028797018963968
  | 6 => 34359738368
  | 7 => 37189881298945025
  | 8 => 35184372088832
  | 9 => 1188985485997899808
  | 10 => 36893488147419103232
  | 11 => 1180592746651677884416
  | 12 => 37778969052872819343360
  | 13 => 1267650600228229401496703205376
  | 14 => 1237940039286506209165705248
  | 15 => 1308541344967852927630504394752
  | 16 => 38685626227668133590597632
  | 17 => 1308502621524646951667887013888
  | 18 => 39614082474654432359603011584
  | 19 => 32768
  | 20 => 41832508493157833981506222030848
  | 21 => 39615329180522803786358490113
  | _ => 0

def R10p01_columnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1180591620717411303425
  | 1 => 40564819207304493769433469157376
  | 2 => 41832469808712161870108617080833
  | 3 => 1074824193
  | 4 => 1237941219877000993385250849
  | 5 => 39614081257132168797845717025
  | 6 => 1073774592
  | 7 => 37778933024076874121217
  | 8 => 1074790401
  | 9 => 1218638065554883084320
  | 10 => 38686806820449969640603649
  | 11 => 1210107564192035564978208
  | 12 => 1152921505680588801
  | 13 => 36028798092738561
  | 14 => 1125899906875393
  | 15 => 35185445830657
  | 16 => 1
  | 17 => 1107296288
  | 18 => 35434528768
  | 19 => 1074823169
  | 20 => 1100586418208
  | 21 => 32
  | _ => 0

def R10p01_digit (i j : Fin 22) : ℕ := packedDigit 1 (R10p01_lowColumnCode j) i.val

private theorem R10p01_bound_00 : ∀ j : Fin 22,R10p01_digit 0 j<2 := by decide +kernel

private theorem R10p01_bound_01 : ∀ j : Fin 22,R10p01_digit 1 j<2 := by decide +kernel

private theorem R10p01_bound_02 : ∀ j : Fin 22,R10p01_digit 2 j<2 := by decide +kernel

private theorem R10p01_bound_03 : ∀ j : Fin 22,R10p01_digit 3 j<2 := by decide +kernel

private theorem R10p01_bound_04 : ∀ j : Fin 22,R10p01_digit 4 j<2 := by decide +kernel

private theorem R10p01_bound_05 : ∀ j : Fin 22,R10p01_digit 5 j<2 := by decide +kernel

private theorem R10p01_bound_06 : ∀ j : Fin 22,R10p01_digit 6 j<2 := by decide +kernel

private theorem R10p01_bound_07 : ∀ j : Fin 22,R10p01_digit 7 j<2 := by decide +kernel

private theorem R10p01_bound_08 : ∀ j : Fin 22,R10p01_digit 8 j<2 := by decide +kernel

private theorem R10p01_bound_09 : ∀ j : Fin 22,R10p01_digit 9 j<2 := by decide +kernel

private theorem R10p01_bound_10 : ∀ j : Fin 22,R10p01_digit 10 j<2 := by decide +kernel

private theorem R10p01_bound_11 : ∀ j : Fin 22,R10p01_digit 11 j<2 := by decide +kernel

private theorem R10p01_bound_12 : ∀ j : Fin 22,R10p01_digit 12 j<2 := by decide +kernel

private theorem R10p01_bound_13 : ∀ j : Fin 22,R10p01_digit 13 j<2 := by decide +kernel

private theorem R10p01_bound_14 : ∀ j : Fin 22,R10p01_digit 14 j<2 := by decide +kernel

private theorem R10p01_bound_15 : ∀ j : Fin 22,R10p01_digit 15 j<2 := by decide +kernel

private theorem R10p01_bound_16 : ∀ j : Fin 22,R10p01_digit 16 j<2 := by decide +kernel

private theorem R10p01_bound_17 : ∀ j : Fin 22,R10p01_digit 17 j<2 := by decide +kernel

private theorem R10p01_bound_18 : ∀ j : Fin 22,R10p01_digit 18 j<2 := by decide +kernel

private theorem R10p01_bound_19 : ∀ j : Fin 22,R10p01_digit 19 j<2 := by decide +kernel

private theorem R10p01_bound_20 : ∀ j : Fin 22,R10p01_digit 20 j<2 := by decide +kernel

private theorem R10p01_bound_21 : ∀ j : Fin 22,R10p01_digit 21 j<2 := by decide +kernel

theorem R10p01_bound : ∀ i j : Fin 22,R10p01_digit i j<2 := by
  intro i j
  fin_cases i
  · exact R10p01_bound_00 j
  · exact R10p01_bound_01 j
  · exact R10p01_bound_02 j
  · exact R10p01_bound_03 j
  · exact R10p01_bound_04 j
  · exact R10p01_bound_05 j
  · exact R10p01_bound_06 j
  · exact R10p01_bound_07 j
  · exact R10p01_bound_08 j
  · exact R10p01_bound_09 j
  · exact R10p01_bound_10 j
  · exact R10p01_bound_11 j
  · exact R10p01_bound_12 j
  · exact R10p01_bound_13 j
  · exact R10p01_bound_14 j
  · exact R10p01_bound_15 j
  · exact R10p01_bound_16 j
  · exact R10p01_bound_17 j
  · exact R10p01_bound_18 j
  · exact R10p01_bound_19 j
  · exact R10p01_bound_20 j
  · exact R10p01_bound_21 j

private theorem R10p01_row_00 : pack 32 (R10p01_digit 0)=R10p01_rowCode 0 := by decide +kernel

private theorem R10p01_row_01 : pack 32 (R10p01_digit 1)=R10p01_rowCode 1 := by decide +kernel

private theorem R10p01_row_02 : pack 32 (R10p01_digit 2)=R10p01_rowCode 2 := by decide +kernel

private theorem R10p01_row_03 : pack 32 (R10p01_digit 3)=R10p01_rowCode 3 := by decide +kernel

private theorem R10p01_row_04 : pack 32 (R10p01_digit 4)=R10p01_rowCode 4 := by decide +kernel

private theorem R10p01_row_05 : pack 32 (R10p01_digit 5)=R10p01_rowCode 5 := by decide +kernel

private theorem R10p01_row_06 : pack 32 (R10p01_digit 6)=R10p01_rowCode 6 := by decide +kernel

private theorem R10p01_row_07 : pack 32 (R10p01_digit 7)=R10p01_rowCode 7 := by decide +kernel

private theorem R10p01_row_08 : pack 32 (R10p01_digit 8)=R10p01_rowCode 8 := by decide +kernel

private theorem R10p01_row_09 : pack 32 (R10p01_digit 9)=R10p01_rowCode 9 := by decide +kernel

private theorem R10p01_row_10 : pack 32 (R10p01_digit 10)=R10p01_rowCode 10 := by decide +kernel

private theorem R10p01_row_11 : pack 32 (R10p01_digit 11)=R10p01_rowCode 11 := by decide +kernel

private theorem R10p01_row_12 : pack 32 (R10p01_digit 12)=R10p01_rowCode 12 := by decide +kernel

private theorem R10p01_row_13 : pack 32 (R10p01_digit 13)=R10p01_rowCode 13 := by decide +kernel

private theorem R10p01_row_14 : pack 32 (R10p01_digit 14)=R10p01_rowCode 14 := by decide +kernel

private theorem R10p01_row_15 : pack 32 (R10p01_digit 15)=R10p01_rowCode 15 := by decide +kernel

private theorem R10p01_row_16 : pack 32 (R10p01_digit 16)=R10p01_rowCode 16 := by decide +kernel

private theorem R10p01_row_17 : pack 32 (R10p01_digit 17)=R10p01_rowCode 17 := by decide +kernel

private theorem R10p01_row_18 : pack 32 (R10p01_digit 18)=R10p01_rowCode 18 := by decide +kernel

private theorem R10p01_row_19 : pack 32 (R10p01_digit 19)=R10p01_rowCode 19 := by decide +kernel

private theorem R10p01_row_20 : pack 32 (R10p01_digit 20)=R10p01_rowCode 20 := by decide +kernel

private theorem R10p01_row_21 : pack 32 (R10p01_digit 21)=R10p01_rowCode 21 := by decide +kernel

theorem R10p01_row_binding : ∀ i : Fin 22,pack 32 (R10p01_digit i)=R10p01_rowCode i := by
  intro i
  fin_cases i
  · exact R10p01_row_00
  · exact R10p01_row_01
  · exact R10p01_row_02
  · exact R10p01_row_03
  · exact R10p01_row_04
  · exact R10p01_row_05
  · exact R10p01_row_06
  · exact R10p01_row_07
  · exact R10p01_row_08
  · exact R10p01_row_09
  · exact R10p01_row_10
  · exact R10p01_row_11
  · exact R10p01_row_12
  · exact R10p01_row_13
  · exact R10p01_row_14
  · exact R10p01_row_15
  · exact R10p01_row_16
  · exact R10p01_row_17
  · exact R10p01_row_18
  · exact R10p01_row_19
  · exact R10p01_row_20
  · exact R10p01_row_21

private theorem R10p01_column_00 : reversePack 32 (fun j : Fin 22 => R10p01_digit j 0)=R10p01_columnCode 0 := by decide +kernel

private theorem R10p01_column_01 : reversePack 32 (fun j : Fin 22 => R10p01_digit j 1)=R10p01_columnCode 1 := by decide +kernel

private theorem R10p01_column_02 : reversePack 32 (fun j : Fin 22 => R10p01_digit j 2)=R10p01_columnCode 2 := by decide +kernel

private theorem R10p01_column_03 : reversePack 32 (fun j : Fin 22 => R10p01_digit j 3)=R10p01_columnCode 3 := by decide +kernel

private theorem R10p01_column_04 : reversePack 32 (fun j : Fin 22 => R10p01_digit j 4)=R10p01_columnCode 4 := by decide +kernel

private theorem R10p01_column_05 : reversePack 32 (fun j : Fin 22 => R10p01_digit j 5)=R10p01_columnCode 5 := by decide +kernel

private theorem R10p01_column_06 : reversePack 32 (fun j : Fin 22 => R10p01_digit j 6)=R10p01_columnCode 6 := by decide +kernel

private theorem R10p01_column_07 : reversePack 32 (fun j : Fin 22 => R10p01_digit j 7)=R10p01_columnCode 7 := by decide +kernel

private theorem R10p01_column_08 : reversePack 32 (fun j : Fin 22 => R10p01_digit j 8)=R10p01_columnCode 8 := by decide +kernel

private theorem R10p01_column_09 : reversePack 32 (fun j : Fin 22 => R10p01_digit j 9)=R10p01_columnCode 9 := by decide +kernel

private theorem R10p01_column_10 : reversePack 32 (fun j : Fin 22 => R10p01_digit j 10)=R10p01_columnCode 10 := by decide +kernel

private theorem R10p01_column_11 : reversePack 32 (fun j : Fin 22 => R10p01_digit j 11)=R10p01_columnCode 11 := by decide +kernel

private theorem R10p01_column_12 : reversePack 32 (fun j : Fin 22 => R10p01_digit j 12)=R10p01_columnCode 12 := by decide +kernel

private theorem R10p01_column_13 : reversePack 32 (fun j : Fin 22 => R10p01_digit j 13)=R10p01_columnCode 13 := by decide +kernel

private theorem R10p01_column_14 : reversePack 32 (fun j : Fin 22 => R10p01_digit j 14)=R10p01_columnCode 14 := by decide +kernel

private theorem R10p01_column_15 : reversePack 32 (fun j : Fin 22 => R10p01_digit j 15)=R10p01_columnCode 15 := by decide +kernel

private theorem R10p01_column_16 : reversePack 32 (fun j : Fin 22 => R10p01_digit j 16)=R10p01_columnCode 16 := by decide +kernel

private theorem R10p01_column_17 : reversePack 32 (fun j : Fin 22 => R10p01_digit j 17)=R10p01_columnCode 17 := by decide +kernel

private theorem R10p01_column_18 : reversePack 32 (fun j : Fin 22 => R10p01_digit j 18)=R10p01_columnCode 18 := by decide +kernel

private theorem R10p01_column_19 : reversePack 32 (fun j : Fin 22 => R10p01_digit j 19)=R10p01_columnCode 19 := by decide +kernel

private theorem R10p01_column_20 : reversePack 32 (fun j : Fin 22 => R10p01_digit j 20)=R10p01_columnCode 20 := by decide +kernel

private theorem R10p01_column_21 : reversePack 32 (fun j : Fin 22 => R10p01_digit j 21)=R10p01_columnCode 21 := by decide +kernel

theorem R10p01_column_binding : ∀ i : Fin 22,reversePack 32 (fun j : Fin 22 => R10p01_digit j i)=R10p01_columnCode i := by
  intro i
  fin_cases i
  · exact R10p01_column_00
  · exact R10p01_column_01
  · exact R10p01_column_02
  · exact R10p01_column_03
  · exact R10p01_column_04
  · exact R10p01_column_05
  · exact R10p01_column_06
  · exact R10p01_column_07
  · exact R10p01_column_08
  · exact R10p01_column_09
  · exact R10p01_column_10
  · exact R10p01_column_11
  · exact R10p01_column_12
  · exact R10p01_column_13
  · exact R10p01_column_14
  · exact R10p01_column_15
  · exact R10p01_column_16
  · exact R10p01_column_17
  · exact R10p01_column_18
  · exact R10p01_column_19
  · exact R10p01_column_20
  · exact R10p01_column_21

def R10p01_data : PackedData 22 2 32 where
  raw := R10p01_digit
  digit_lt := R10p01_bound
  rowCode := R10p01_rowCode
  columnCode := R10p01_columnCode
  row_binding := R10p01_row_binding
  column_binding := R10p01_column_binding

def R10p02_lowColumnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 2414977
  | 1 => 301824
  | 2 => 3940352
  | 3 => 3317891
  | 4 => 2588896
  | 5 => 3205568
  | 6 => 1409128
  | 7 => 2152512
  | 8 => 2288068
  | 9 => 1086336
  | 10 => 2381968
  | 11 => 1315488
  | 12 => 2130432
  | 13 => 2121728
  | 14 => 2361344
  | 15 => 3522560
  | 16 => 2417664
  | 17 => 1146880
  | 18 => 180224
  | 19 => 3395584
  | 20 => 1220608
  | 21 => 1048576
  | _ => 0

def R10p02_rowCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 32769
  | 1 => 32768
  | 2 => 1099511627776
  | 3 => 1073741824
  | 4 => 1125899906842624
  | 5 => 36028798093754368
  | 6 => 1134979710976
  | 7 => 37190980844158977
  | 8 => 36283917271073
  | 9 => 1188985485997899808
  | 10 => 1208925819614629174706176
  | 11 => 1180592747751223066657
  | 12 => 39614081257169358712429608993
  | 13 => 1267651809190942505372842230784
  | 14 => 40853268038063641839238381569
  | 15 => 1308542553856779054112259997729
  | 16 => 39652804662291699888599072768
  | 17 => 1308502621524646951667887013888
  | 18 => 1247885380253001748317217
  | 19 => 1024
  | 20 => 41872122612193898013261228442624
  | 21 => 39615329180522803786358490113
  | _ => 0

def R10p02_columnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 40564819208520827117879045423105
  | 1 => 38047570737378656256
  | 2 => 1099511661601
  | 3 => 41832469808712161871209203499041
  | 4 => 1247885343098304856096769
  | 5 => 38996418098856844066849
  | 6 => 1239186744036857862342869024
  | 7 => 37778933024076874121217
  | 8 => 39614120253550267653617090561
  | 9 => 1218638065554883084320
  | 10 => 38686806820449969640603649
  | 11 => 1210107564192035564978208
  | 12 => 1152921505680588801
  | 13 => 1133871366145
  | 14 => 1125899906875393
  | 15 => 35467067425
  | 16 => 36029931964104705
  | 17 => 1107296288
  | 18 => 35434528768
  | 19 => 35219840172065
  | 20 => 1100586418208
  | 21 => 32
  | _ => 0

def R10p02_digit (i j : Fin 22) : ℕ := packedDigit 1 (R10p02_lowColumnCode j) i.val

private theorem R10p02_bound_00 : ∀ j : Fin 22,R10p02_digit 0 j<2 := by decide +kernel

private theorem R10p02_bound_01 : ∀ j : Fin 22,R10p02_digit 1 j<2 := by decide +kernel

private theorem R10p02_bound_02 : ∀ j : Fin 22,R10p02_digit 2 j<2 := by decide +kernel

private theorem R10p02_bound_03 : ∀ j : Fin 22,R10p02_digit 3 j<2 := by decide +kernel

private theorem R10p02_bound_04 : ∀ j : Fin 22,R10p02_digit 4 j<2 := by decide +kernel

private theorem R10p02_bound_05 : ∀ j : Fin 22,R10p02_digit 5 j<2 := by decide +kernel

private theorem R10p02_bound_06 : ∀ j : Fin 22,R10p02_digit 6 j<2 := by decide +kernel

private theorem R10p02_bound_07 : ∀ j : Fin 22,R10p02_digit 7 j<2 := by decide +kernel

private theorem R10p02_bound_08 : ∀ j : Fin 22,R10p02_digit 8 j<2 := by decide +kernel

private theorem R10p02_bound_09 : ∀ j : Fin 22,R10p02_digit 9 j<2 := by decide +kernel

private theorem R10p02_bound_10 : ∀ j : Fin 22,R10p02_digit 10 j<2 := by decide +kernel

private theorem R10p02_bound_11 : ∀ j : Fin 22,R10p02_digit 11 j<2 := by decide +kernel

private theorem R10p02_bound_12 : ∀ j : Fin 22,R10p02_digit 12 j<2 := by decide +kernel

private theorem R10p02_bound_13 : ∀ j : Fin 22,R10p02_digit 13 j<2 := by decide +kernel

private theorem R10p02_bound_14 : ∀ j : Fin 22,R10p02_digit 14 j<2 := by decide +kernel

private theorem R10p02_bound_15 : ∀ j : Fin 22,R10p02_digit 15 j<2 := by decide +kernel

private theorem R10p02_bound_16 : ∀ j : Fin 22,R10p02_digit 16 j<2 := by decide +kernel

private theorem R10p02_bound_17 : ∀ j : Fin 22,R10p02_digit 17 j<2 := by decide +kernel

private theorem R10p02_bound_18 : ∀ j : Fin 22,R10p02_digit 18 j<2 := by decide +kernel

private theorem R10p02_bound_19 : ∀ j : Fin 22,R10p02_digit 19 j<2 := by decide +kernel

private theorem R10p02_bound_20 : ∀ j : Fin 22,R10p02_digit 20 j<2 := by decide +kernel

private theorem R10p02_bound_21 : ∀ j : Fin 22,R10p02_digit 21 j<2 := by decide +kernel

theorem R10p02_bound : ∀ i j : Fin 22,R10p02_digit i j<2 := by
  intro i j
  fin_cases i
  · exact R10p02_bound_00 j
  · exact R10p02_bound_01 j
  · exact R10p02_bound_02 j
  · exact R10p02_bound_03 j
  · exact R10p02_bound_04 j
  · exact R10p02_bound_05 j
  · exact R10p02_bound_06 j
  · exact R10p02_bound_07 j
  · exact R10p02_bound_08 j
  · exact R10p02_bound_09 j
  · exact R10p02_bound_10 j
  · exact R10p02_bound_11 j
  · exact R10p02_bound_12 j
  · exact R10p02_bound_13 j
  · exact R10p02_bound_14 j
  · exact R10p02_bound_15 j
  · exact R10p02_bound_16 j
  · exact R10p02_bound_17 j
  · exact R10p02_bound_18 j
  · exact R10p02_bound_19 j
  · exact R10p02_bound_20 j
  · exact R10p02_bound_21 j

private theorem R10p02_row_00 : pack 32 (R10p02_digit 0)=R10p02_rowCode 0 := by decide +kernel

private theorem R10p02_row_01 : pack 32 (R10p02_digit 1)=R10p02_rowCode 1 := by decide +kernel

private theorem R10p02_row_02 : pack 32 (R10p02_digit 2)=R10p02_rowCode 2 := by decide +kernel

private theorem R10p02_row_03 : pack 32 (R10p02_digit 3)=R10p02_rowCode 3 := by decide +kernel

private theorem R10p02_row_04 : pack 32 (R10p02_digit 4)=R10p02_rowCode 4 := by decide +kernel

private theorem R10p02_row_05 : pack 32 (R10p02_digit 5)=R10p02_rowCode 5 := by decide +kernel

private theorem R10p02_row_06 : pack 32 (R10p02_digit 6)=R10p02_rowCode 6 := by decide +kernel

private theorem R10p02_row_07 : pack 32 (R10p02_digit 7)=R10p02_rowCode 7 := by decide +kernel

private theorem R10p02_row_08 : pack 32 (R10p02_digit 8)=R10p02_rowCode 8 := by decide +kernel

private theorem R10p02_row_09 : pack 32 (R10p02_digit 9)=R10p02_rowCode 9 := by decide +kernel

private theorem R10p02_row_10 : pack 32 (R10p02_digit 10)=R10p02_rowCode 10 := by decide +kernel

private theorem R10p02_row_11 : pack 32 (R10p02_digit 11)=R10p02_rowCode 11 := by decide +kernel

private theorem R10p02_row_12 : pack 32 (R10p02_digit 12)=R10p02_rowCode 12 := by decide +kernel

private theorem R10p02_row_13 : pack 32 (R10p02_digit 13)=R10p02_rowCode 13 := by decide +kernel

private theorem R10p02_row_14 : pack 32 (R10p02_digit 14)=R10p02_rowCode 14 := by decide +kernel

private theorem R10p02_row_15 : pack 32 (R10p02_digit 15)=R10p02_rowCode 15 := by decide +kernel

private theorem R10p02_row_16 : pack 32 (R10p02_digit 16)=R10p02_rowCode 16 := by decide +kernel

private theorem R10p02_row_17 : pack 32 (R10p02_digit 17)=R10p02_rowCode 17 := by decide +kernel

private theorem R10p02_row_18 : pack 32 (R10p02_digit 18)=R10p02_rowCode 18 := by decide +kernel

private theorem R10p02_row_19 : pack 32 (R10p02_digit 19)=R10p02_rowCode 19 := by decide +kernel

private theorem R10p02_row_20 : pack 32 (R10p02_digit 20)=R10p02_rowCode 20 := by decide +kernel

private theorem R10p02_row_21 : pack 32 (R10p02_digit 21)=R10p02_rowCode 21 := by decide +kernel

theorem R10p02_row_binding : ∀ i : Fin 22,pack 32 (R10p02_digit i)=R10p02_rowCode i := by
  intro i
  fin_cases i
  · exact R10p02_row_00
  · exact R10p02_row_01
  · exact R10p02_row_02
  · exact R10p02_row_03
  · exact R10p02_row_04
  · exact R10p02_row_05
  · exact R10p02_row_06
  · exact R10p02_row_07
  · exact R10p02_row_08
  · exact R10p02_row_09
  · exact R10p02_row_10
  · exact R10p02_row_11
  · exact R10p02_row_12
  · exact R10p02_row_13
  · exact R10p02_row_14
  · exact R10p02_row_15
  · exact R10p02_row_16
  · exact R10p02_row_17
  · exact R10p02_row_18
  · exact R10p02_row_19
  · exact R10p02_row_20
  · exact R10p02_row_21

private theorem R10p02_column_00 : reversePack 32 (fun j : Fin 22 => R10p02_digit j 0)=R10p02_columnCode 0 := by decide +kernel

private theorem R10p02_column_01 : reversePack 32 (fun j : Fin 22 => R10p02_digit j 1)=R10p02_columnCode 1 := by decide +kernel

private theorem R10p02_column_02 : reversePack 32 (fun j : Fin 22 => R10p02_digit j 2)=R10p02_columnCode 2 := by decide +kernel

private theorem R10p02_column_03 : reversePack 32 (fun j : Fin 22 => R10p02_digit j 3)=R10p02_columnCode 3 := by decide +kernel

private theorem R10p02_column_04 : reversePack 32 (fun j : Fin 22 => R10p02_digit j 4)=R10p02_columnCode 4 := by decide +kernel

private theorem R10p02_column_05 : reversePack 32 (fun j : Fin 22 => R10p02_digit j 5)=R10p02_columnCode 5 := by decide +kernel

private theorem R10p02_column_06 : reversePack 32 (fun j : Fin 22 => R10p02_digit j 6)=R10p02_columnCode 6 := by decide +kernel

private theorem R10p02_column_07 : reversePack 32 (fun j : Fin 22 => R10p02_digit j 7)=R10p02_columnCode 7 := by decide +kernel

private theorem R10p02_column_08 : reversePack 32 (fun j : Fin 22 => R10p02_digit j 8)=R10p02_columnCode 8 := by decide +kernel

private theorem R10p02_column_09 : reversePack 32 (fun j : Fin 22 => R10p02_digit j 9)=R10p02_columnCode 9 := by decide +kernel

private theorem R10p02_column_10 : reversePack 32 (fun j : Fin 22 => R10p02_digit j 10)=R10p02_columnCode 10 := by decide +kernel

private theorem R10p02_column_11 : reversePack 32 (fun j : Fin 22 => R10p02_digit j 11)=R10p02_columnCode 11 := by decide +kernel

private theorem R10p02_column_12 : reversePack 32 (fun j : Fin 22 => R10p02_digit j 12)=R10p02_columnCode 12 := by decide +kernel

private theorem R10p02_column_13 : reversePack 32 (fun j : Fin 22 => R10p02_digit j 13)=R10p02_columnCode 13 := by decide +kernel

private theorem R10p02_column_14 : reversePack 32 (fun j : Fin 22 => R10p02_digit j 14)=R10p02_columnCode 14 := by decide +kernel

private theorem R10p02_column_15 : reversePack 32 (fun j : Fin 22 => R10p02_digit j 15)=R10p02_columnCode 15 := by decide +kernel

private theorem R10p02_column_16 : reversePack 32 (fun j : Fin 22 => R10p02_digit j 16)=R10p02_columnCode 16 := by decide +kernel

private theorem R10p02_column_17 : reversePack 32 (fun j : Fin 22 => R10p02_digit j 17)=R10p02_columnCode 17 := by decide +kernel

private theorem R10p02_column_18 : reversePack 32 (fun j : Fin 22 => R10p02_digit j 18)=R10p02_columnCode 18 := by decide +kernel

private theorem R10p02_column_19 : reversePack 32 (fun j : Fin 22 => R10p02_digit j 19)=R10p02_columnCode 19 := by decide +kernel

private theorem R10p02_column_20 : reversePack 32 (fun j : Fin 22 => R10p02_digit j 20)=R10p02_columnCode 20 := by decide +kernel

private theorem R10p02_column_21 : reversePack 32 (fun j : Fin 22 => R10p02_digit j 21)=R10p02_columnCode 21 := by decide +kernel

theorem R10p02_column_binding : ∀ i : Fin 22,reversePack 32 (fun j : Fin 22 => R10p02_digit j i)=R10p02_columnCode i := by
  intro i
  fin_cases i
  · exact R10p02_column_00
  · exact R10p02_column_01
  · exact R10p02_column_02
  · exact R10p02_column_03
  · exact R10p02_column_04
  · exact R10p02_column_05
  · exact R10p02_column_06
  · exact R10p02_column_07
  · exact R10p02_column_08
  · exact R10p02_column_09
  · exact R10p02_column_10
  · exact R10p02_column_11
  · exact R10p02_column_12
  · exact R10p02_column_13
  · exact R10p02_column_14
  · exact R10p02_column_15
  · exact R10p02_column_16
  · exact R10p02_column_17
  · exact R10p02_column_18
  · exact R10p02_column_19
  · exact R10p02_column_20
  · exact R10p02_column_21

def R10p02_data : PackedData 22 2 32 where
  raw := R10p02_digit
  digit_lt := R10p02_bound
  rowCode := R10p02_rowCode
  columnCode := R10p02_columnCode
  row_binding := R10p02_row_binding
  column_binding := R10p02_column_binding

end SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoCaches10
