import SymmetricSubgroupAsymptotics.MatrixKroneckerProductReflection
import Mathlib.Tactic.FinCases

/-! Fixed Co2 binary22 shared caches. Every digit and pack binding is kernel checked. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoCaches05
open MatrixKroneckerProductReflection MatrixKroneckerDotReflection
open MatrixNaturalRowDotReflection SmallNaturalMatrixProductReflection

def R07p04_lowColumnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 3256331
  | 1 => 3801014
  | 2 => 3665924
  | 3 => 2282285
  | 4 => 3664238
  | 5 => 1098104
  | 6 => 3561541
  | 7 => 61838
  | 8 => 778620
  | 9 => 1116724
  | 10 => 84528
  | 11 => 1059380
  | 12 => 1407686
  | 13 => 1861778
  | 14 => 2537620
  | 15 => 1405062
  | 16 => 995330
  | 17 => 3142180
  | 18 => 542866
  | 19 => 692752
  | 20 => 1231408
  | 21 => 3571716
  | _ => 0

def R07p04_rowCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1073774593
  | 1 => 1239186782083267547622277153
  | 2 => 40564857931890280986323610272800
  | 3 => 1133906001921
  | 4 => 1308502622742169250414047789088
  | 5 => 1267689285854494260611137962016
  | 6 => 1152922605226819584
  | 7 => 1237979036855273635857825824
  | 8 => 1133906001952
  | 9 => 1307303367112779349812970553376
  | 10 => 32
  | 11 => 1268888541486190002023412269088
  | 12 => 39654014769855856774150652961
  | 13 => 39933549653206020255646753
  | 14 => 1268927263710721849549267174432
  | 15 => 41872122575595521708172885656609
  | 16 => 39932332133229408325469217
  | 17 => 41872123784521341322768740811776
  | 18 => 40564859140852958023984941630464
  | 19 => 40891915885358321081367134240
  | 20 => 41832469845348584585982892835873
  | 21 => 40564857894110160136746579297313
  | _ => 0

def R07p04_columnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 41833707747570855665951095914529
  | 1 => 1307304577256084074441954296865
  | 2 => 39614081257132205116123807777
  | 3 => 40605672437563624456467180945409
  | 4 => 1308503868266293043337016410145
  | 5 => 1277872407158014177678721056
  | 6 => 40604433326339406040767076007969
  | 7 => 1308502622742132095752521908224
  | 8 => 40891953664290184073996928000
  | 9 => 39653975810333498964084523040
  | 10 => 39894553201330201672286208
  | 11 => 39653975810333500063562596384
  | 12 => 1307264720446039137690838925344
  | 13 => 1267689287035049817381483349024
  | 14 => 39652768063952619832639258625
  | 15 => 1307264682665953227329163526176
  | 16 => 1267650600228229437780621558784
  | 17 => 39615290184104741249905361921
  | 18 => 1267689287035049816281971688448
  | 19 => 38685627380624823644324864
  | 20 => 39894553201330202713522208
  | 21 => 39614081257132168797846798369
  | _ => 0

def R07p04_digit (i j : Fin 22) : ℕ := packedDigit 1 (R07p04_lowColumnCode j) i.val

private theorem R07p04_bound_00 : ∀ j : Fin 22,R07p04_digit 0 j<2 := by decide +kernel

private theorem R07p04_bound_01 : ∀ j : Fin 22,R07p04_digit 1 j<2 := by decide +kernel

private theorem R07p04_bound_02 : ∀ j : Fin 22,R07p04_digit 2 j<2 := by decide +kernel

private theorem R07p04_bound_03 : ∀ j : Fin 22,R07p04_digit 3 j<2 := by decide +kernel

private theorem R07p04_bound_04 : ∀ j : Fin 22,R07p04_digit 4 j<2 := by decide +kernel

private theorem R07p04_bound_05 : ∀ j : Fin 22,R07p04_digit 5 j<2 := by decide +kernel

private theorem R07p04_bound_06 : ∀ j : Fin 22,R07p04_digit 6 j<2 := by decide +kernel

private theorem R07p04_bound_07 : ∀ j : Fin 22,R07p04_digit 7 j<2 := by decide +kernel

private theorem R07p04_bound_08 : ∀ j : Fin 22,R07p04_digit 8 j<2 := by decide +kernel

private theorem R07p04_bound_09 : ∀ j : Fin 22,R07p04_digit 9 j<2 := by decide +kernel

private theorem R07p04_bound_10 : ∀ j : Fin 22,R07p04_digit 10 j<2 := by decide +kernel

private theorem R07p04_bound_11 : ∀ j : Fin 22,R07p04_digit 11 j<2 := by decide +kernel

private theorem R07p04_bound_12 : ∀ j : Fin 22,R07p04_digit 12 j<2 := by decide +kernel

private theorem R07p04_bound_13 : ∀ j : Fin 22,R07p04_digit 13 j<2 := by decide +kernel

private theorem R07p04_bound_14 : ∀ j : Fin 22,R07p04_digit 14 j<2 := by decide +kernel

private theorem R07p04_bound_15 : ∀ j : Fin 22,R07p04_digit 15 j<2 := by decide +kernel

private theorem R07p04_bound_16 : ∀ j : Fin 22,R07p04_digit 16 j<2 := by decide +kernel

private theorem R07p04_bound_17 : ∀ j : Fin 22,R07p04_digit 17 j<2 := by decide +kernel

private theorem R07p04_bound_18 : ∀ j : Fin 22,R07p04_digit 18 j<2 := by decide +kernel

private theorem R07p04_bound_19 : ∀ j : Fin 22,R07p04_digit 19 j<2 := by decide +kernel

private theorem R07p04_bound_20 : ∀ j : Fin 22,R07p04_digit 20 j<2 := by decide +kernel

private theorem R07p04_bound_21 : ∀ j : Fin 22,R07p04_digit 21 j<2 := by decide +kernel

theorem R07p04_bound : ∀ i j : Fin 22,R07p04_digit i j<2 := by
  intro i j
  fin_cases i
  · exact R07p04_bound_00 j
  · exact R07p04_bound_01 j
  · exact R07p04_bound_02 j
  · exact R07p04_bound_03 j
  · exact R07p04_bound_04 j
  · exact R07p04_bound_05 j
  · exact R07p04_bound_06 j
  · exact R07p04_bound_07 j
  · exact R07p04_bound_08 j
  · exact R07p04_bound_09 j
  · exact R07p04_bound_10 j
  · exact R07p04_bound_11 j
  · exact R07p04_bound_12 j
  · exact R07p04_bound_13 j
  · exact R07p04_bound_14 j
  · exact R07p04_bound_15 j
  · exact R07p04_bound_16 j
  · exact R07p04_bound_17 j
  · exact R07p04_bound_18 j
  · exact R07p04_bound_19 j
  · exact R07p04_bound_20 j
  · exact R07p04_bound_21 j

private theorem R07p04_row_00 : pack 32 (R07p04_digit 0)=R07p04_rowCode 0 := by decide +kernel

private theorem R07p04_row_01 : pack 32 (R07p04_digit 1)=R07p04_rowCode 1 := by decide +kernel

private theorem R07p04_row_02 : pack 32 (R07p04_digit 2)=R07p04_rowCode 2 := by decide +kernel

private theorem R07p04_row_03 : pack 32 (R07p04_digit 3)=R07p04_rowCode 3 := by decide +kernel

private theorem R07p04_row_04 : pack 32 (R07p04_digit 4)=R07p04_rowCode 4 := by decide +kernel

private theorem R07p04_row_05 : pack 32 (R07p04_digit 5)=R07p04_rowCode 5 := by decide +kernel

private theorem R07p04_row_06 : pack 32 (R07p04_digit 6)=R07p04_rowCode 6 := by decide +kernel

private theorem R07p04_row_07 : pack 32 (R07p04_digit 7)=R07p04_rowCode 7 := by decide +kernel

private theorem R07p04_row_08 : pack 32 (R07p04_digit 8)=R07p04_rowCode 8 := by decide +kernel

private theorem R07p04_row_09 : pack 32 (R07p04_digit 9)=R07p04_rowCode 9 := by decide +kernel

private theorem R07p04_row_10 : pack 32 (R07p04_digit 10)=R07p04_rowCode 10 := by decide +kernel

private theorem R07p04_row_11 : pack 32 (R07p04_digit 11)=R07p04_rowCode 11 := by decide +kernel

private theorem R07p04_row_12 : pack 32 (R07p04_digit 12)=R07p04_rowCode 12 := by decide +kernel

private theorem R07p04_row_13 : pack 32 (R07p04_digit 13)=R07p04_rowCode 13 := by decide +kernel

private theorem R07p04_row_14 : pack 32 (R07p04_digit 14)=R07p04_rowCode 14 := by decide +kernel

private theorem R07p04_row_15 : pack 32 (R07p04_digit 15)=R07p04_rowCode 15 := by decide +kernel

private theorem R07p04_row_16 : pack 32 (R07p04_digit 16)=R07p04_rowCode 16 := by decide +kernel

private theorem R07p04_row_17 : pack 32 (R07p04_digit 17)=R07p04_rowCode 17 := by decide +kernel

private theorem R07p04_row_18 : pack 32 (R07p04_digit 18)=R07p04_rowCode 18 := by decide +kernel

private theorem R07p04_row_19 : pack 32 (R07p04_digit 19)=R07p04_rowCode 19 := by decide +kernel

private theorem R07p04_row_20 : pack 32 (R07p04_digit 20)=R07p04_rowCode 20 := by decide +kernel

private theorem R07p04_row_21 : pack 32 (R07p04_digit 21)=R07p04_rowCode 21 := by decide +kernel

theorem R07p04_row_binding : ∀ i : Fin 22,pack 32 (R07p04_digit i)=R07p04_rowCode i := by
  intro i
  fin_cases i
  · exact R07p04_row_00
  · exact R07p04_row_01
  · exact R07p04_row_02
  · exact R07p04_row_03
  · exact R07p04_row_04
  · exact R07p04_row_05
  · exact R07p04_row_06
  · exact R07p04_row_07
  · exact R07p04_row_08
  · exact R07p04_row_09
  · exact R07p04_row_10
  · exact R07p04_row_11
  · exact R07p04_row_12
  · exact R07p04_row_13
  · exact R07p04_row_14
  · exact R07p04_row_15
  · exact R07p04_row_16
  · exact R07p04_row_17
  · exact R07p04_row_18
  · exact R07p04_row_19
  · exact R07p04_row_20
  · exact R07p04_row_21

private theorem R07p04_column_00 : reversePack 32 (fun j : Fin 22 => R07p04_digit j 0)=R07p04_columnCode 0 := by decide +kernel

private theorem R07p04_column_01 : reversePack 32 (fun j : Fin 22 => R07p04_digit j 1)=R07p04_columnCode 1 := by decide +kernel

private theorem R07p04_column_02 : reversePack 32 (fun j : Fin 22 => R07p04_digit j 2)=R07p04_columnCode 2 := by decide +kernel

private theorem R07p04_column_03 : reversePack 32 (fun j : Fin 22 => R07p04_digit j 3)=R07p04_columnCode 3 := by decide +kernel

private theorem R07p04_column_04 : reversePack 32 (fun j : Fin 22 => R07p04_digit j 4)=R07p04_columnCode 4 := by decide +kernel

private theorem R07p04_column_05 : reversePack 32 (fun j : Fin 22 => R07p04_digit j 5)=R07p04_columnCode 5 := by decide +kernel

private theorem R07p04_column_06 : reversePack 32 (fun j : Fin 22 => R07p04_digit j 6)=R07p04_columnCode 6 := by decide +kernel

private theorem R07p04_column_07 : reversePack 32 (fun j : Fin 22 => R07p04_digit j 7)=R07p04_columnCode 7 := by decide +kernel

private theorem R07p04_column_08 : reversePack 32 (fun j : Fin 22 => R07p04_digit j 8)=R07p04_columnCode 8 := by decide +kernel

private theorem R07p04_column_09 : reversePack 32 (fun j : Fin 22 => R07p04_digit j 9)=R07p04_columnCode 9 := by decide +kernel

private theorem R07p04_column_10 : reversePack 32 (fun j : Fin 22 => R07p04_digit j 10)=R07p04_columnCode 10 := by decide +kernel

private theorem R07p04_column_11 : reversePack 32 (fun j : Fin 22 => R07p04_digit j 11)=R07p04_columnCode 11 := by decide +kernel

private theorem R07p04_column_12 : reversePack 32 (fun j : Fin 22 => R07p04_digit j 12)=R07p04_columnCode 12 := by decide +kernel

private theorem R07p04_column_13 : reversePack 32 (fun j : Fin 22 => R07p04_digit j 13)=R07p04_columnCode 13 := by decide +kernel

private theorem R07p04_column_14 : reversePack 32 (fun j : Fin 22 => R07p04_digit j 14)=R07p04_columnCode 14 := by decide +kernel

private theorem R07p04_column_15 : reversePack 32 (fun j : Fin 22 => R07p04_digit j 15)=R07p04_columnCode 15 := by decide +kernel

private theorem R07p04_column_16 : reversePack 32 (fun j : Fin 22 => R07p04_digit j 16)=R07p04_columnCode 16 := by decide +kernel

private theorem R07p04_column_17 : reversePack 32 (fun j : Fin 22 => R07p04_digit j 17)=R07p04_columnCode 17 := by decide +kernel

private theorem R07p04_column_18 : reversePack 32 (fun j : Fin 22 => R07p04_digit j 18)=R07p04_columnCode 18 := by decide +kernel

private theorem R07p04_column_19 : reversePack 32 (fun j : Fin 22 => R07p04_digit j 19)=R07p04_columnCode 19 := by decide +kernel

private theorem R07p04_column_20 : reversePack 32 (fun j : Fin 22 => R07p04_digit j 20)=R07p04_columnCode 20 := by decide +kernel

private theorem R07p04_column_21 : reversePack 32 (fun j : Fin 22 => R07p04_digit j 21)=R07p04_columnCode 21 := by decide +kernel

theorem R07p04_column_binding : ∀ i : Fin 22,reversePack 32 (fun j : Fin 22 => R07p04_digit j i)=R07p04_columnCode i := by
  intro i
  fin_cases i
  · exact R07p04_column_00
  · exact R07p04_column_01
  · exact R07p04_column_02
  · exact R07p04_column_03
  · exact R07p04_column_04
  · exact R07p04_column_05
  · exact R07p04_column_06
  · exact R07p04_column_07
  · exact R07p04_column_08
  · exact R07p04_column_09
  · exact R07p04_column_10
  · exact R07p04_column_11
  · exact R07p04_column_12
  · exact R07p04_column_13
  · exact R07p04_column_14
  · exact R07p04_column_15
  · exact R07p04_column_16
  · exact R07p04_column_17
  · exact R07p04_column_18
  · exact R07p04_column_19
  · exact R07p04_column_20
  · exact R07p04_column_21

def R07p04_data : PackedData 22 2 32 where
  raw := R07p04_digit
  digit_lt := R07p04_bound
  rowCode := R07p04_rowCode
  columnCode := R07p04_columnCode
  row_binding := R07p04_row_binding
  column_binding := R07p04_column_binding

def R07p05_lowColumnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 3182523
  | 1 => 3592116
  | 2 => 260983
  | 3 => 2677331
  | 4 => 3466135
  | 5 => 2691359
  | 6 => 4030565
  | 7 => 4096009
  | 8 => 1993050
  | 9 => 2974189
  | 10 => 2425045
  | 11 => 2685946
  | 12 => 2976685
  | 13 => 1481315
  | 14 => 825836
  | 15 => 1755142
  | 16 => 1595424
  | 17 => 3406423
  | 18 => 95084
  | 19 => 369170
  | 20 => 3571716
  | 21 => 995330
  | _ => 0

def R07p05_rowCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 38685664275238905363596289
  | 1 => 40604472012002562065826011186177
  | 2 => 1268927264854420016169760064544
  | 3 => 1237941221065987612213248001
  | 4 => 39652766883396992726834644001
  | 5 => 1239150183779089255975879713
  | 6 => 1276626883035348255203427328
  | 7 => 1181781732103317094433
  | 8 => 1237941221065987577854559265
  | 9 => 40890706960727655654307693601
  | 10 => 33
  | 11 => 39933549653205985894892577
  | 12 => 40566097043112194648594049958912
  | 13 => 40605709914227175051685274846208
  | 14 => 1277872371453512580336747552
  | 15 => 1307303406108042239081511420961
  | 16 => 40605709914227140147689757344768
  | 17 => 41832508530973623269763248555040
  | 18 => 41872083890007341610776640094240
  | 19 => 40564820455189872932819226886144
  | 20 => 1267690532596102036498995478561
  | 21 => 1267689285855647181051666661409
  | _ => 0

def R07p05_columnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 41833747643341578097496307007521
  | 1 => 39653977027854636661334900769
  | 2 => 41872123821157729135779189358592
  | 3 => 41832508530937883863106277344257
  | 4 => 41872122575633568117825950744609
  | 5 => 41873360514491108989928292221953
  | 6 => 40604434535265224494278718293025
  | 7 => 40566057147342626228170476520481
  | 8 => 1268927263709568928043553031200
  | 9 => 40605672476521994984551245448193
  | 10 => 40604472013146224168499471745025
  | 11 => 1268928473817133120080190637057
  | 12 => 40605672438744217168998597428225
  | 13 => 41832471054237475809567502794784
  | 14 => 40853269218655296608190628864
  | 15 => 1307264681485362696228816552992
  | 16 => 1208925820775747813377056
  | 17 => 41872122612195016033002595549217
  | 18 => 40853268039215472628310474752
  | 19 => 1267689285855609992235519606784
  | 20 => 39614081257132168797846798369
  | 21 => 1267650600228229437780621558784
  | _ => 0

def R07p05_digit (i j : Fin 22) : ℕ := packedDigit 1 (R07p05_lowColumnCode j) i.val

private theorem R07p05_bound_00 : ∀ j : Fin 22,R07p05_digit 0 j<2 := by decide +kernel

private theorem R07p05_bound_01 : ∀ j : Fin 22,R07p05_digit 1 j<2 := by decide +kernel

private theorem R07p05_bound_02 : ∀ j : Fin 22,R07p05_digit 2 j<2 := by decide +kernel

private theorem R07p05_bound_03 : ∀ j : Fin 22,R07p05_digit 3 j<2 := by decide +kernel

private theorem R07p05_bound_04 : ∀ j : Fin 22,R07p05_digit 4 j<2 := by decide +kernel

private theorem R07p05_bound_05 : ∀ j : Fin 22,R07p05_digit 5 j<2 := by decide +kernel

private theorem R07p05_bound_06 : ∀ j : Fin 22,R07p05_digit 6 j<2 := by decide +kernel

private theorem R07p05_bound_07 : ∀ j : Fin 22,R07p05_digit 7 j<2 := by decide +kernel

private theorem R07p05_bound_08 : ∀ j : Fin 22,R07p05_digit 8 j<2 := by decide +kernel

private theorem R07p05_bound_09 : ∀ j : Fin 22,R07p05_digit 9 j<2 := by decide +kernel

private theorem R07p05_bound_10 : ∀ j : Fin 22,R07p05_digit 10 j<2 := by decide +kernel

private theorem R07p05_bound_11 : ∀ j : Fin 22,R07p05_digit 11 j<2 := by decide +kernel

private theorem R07p05_bound_12 : ∀ j : Fin 22,R07p05_digit 12 j<2 := by decide +kernel

private theorem R07p05_bound_13 : ∀ j : Fin 22,R07p05_digit 13 j<2 := by decide +kernel

private theorem R07p05_bound_14 : ∀ j : Fin 22,R07p05_digit 14 j<2 := by decide +kernel

private theorem R07p05_bound_15 : ∀ j : Fin 22,R07p05_digit 15 j<2 := by decide +kernel

private theorem R07p05_bound_16 : ∀ j : Fin 22,R07p05_digit 16 j<2 := by decide +kernel

private theorem R07p05_bound_17 : ∀ j : Fin 22,R07p05_digit 17 j<2 := by decide +kernel

private theorem R07p05_bound_18 : ∀ j : Fin 22,R07p05_digit 18 j<2 := by decide +kernel

private theorem R07p05_bound_19 : ∀ j : Fin 22,R07p05_digit 19 j<2 := by decide +kernel

private theorem R07p05_bound_20 : ∀ j : Fin 22,R07p05_digit 20 j<2 := by decide +kernel

private theorem R07p05_bound_21 : ∀ j : Fin 22,R07p05_digit 21 j<2 := by decide +kernel

theorem R07p05_bound : ∀ i j : Fin 22,R07p05_digit i j<2 := by
  intro i j
  fin_cases i
  · exact R07p05_bound_00 j
  · exact R07p05_bound_01 j
  · exact R07p05_bound_02 j
  · exact R07p05_bound_03 j
  · exact R07p05_bound_04 j
  · exact R07p05_bound_05 j
  · exact R07p05_bound_06 j
  · exact R07p05_bound_07 j
  · exact R07p05_bound_08 j
  · exact R07p05_bound_09 j
  · exact R07p05_bound_10 j
  · exact R07p05_bound_11 j
  · exact R07p05_bound_12 j
  · exact R07p05_bound_13 j
  · exact R07p05_bound_14 j
  · exact R07p05_bound_15 j
  · exact R07p05_bound_16 j
  · exact R07p05_bound_17 j
  · exact R07p05_bound_18 j
  · exact R07p05_bound_19 j
  · exact R07p05_bound_20 j
  · exact R07p05_bound_21 j

private theorem R07p05_row_00 : pack 32 (R07p05_digit 0)=R07p05_rowCode 0 := by decide +kernel

private theorem R07p05_row_01 : pack 32 (R07p05_digit 1)=R07p05_rowCode 1 := by decide +kernel

private theorem R07p05_row_02 : pack 32 (R07p05_digit 2)=R07p05_rowCode 2 := by decide +kernel

private theorem R07p05_row_03 : pack 32 (R07p05_digit 3)=R07p05_rowCode 3 := by decide +kernel

private theorem R07p05_row_04 : pack 32 (R07p05_digit 4)=R07p05_rowCode 4 := by decide +kernel

private theorem R07p05_row_05 : pack 32 (R07p05_digit 5)=R07p05_rowCode 5 := by decide +kernel

private theorem R07p05_row_06 : pack 32 (R07p05_digit 6)=R07p05_rowCode 6 := by decide +kernel

private theorem R07p05_row_07 : pack 32 (R07p05_digit 7)=R07p05_rowCode 7 := by decide +kernel

private theorem R07p05_row_08 : pack 32 (R07p05_digit 8)=R07p05_rowCode 8 := by decide +kernel

private theorem R07p05_row_09 : pack 32 (R07p05_digit 9)=R07p05_rowCode 9 := by decide +kernel

private theorem R07p05_row_10 : pack 32 (R07p05_digit 10)=R07p05_rowCode 10 := by decide +kernel

private theorem R07p05_row_11 : pack 32 (R07p05_digit 11)=R07p05_rowCode 11 := by decide +kernel

private theorem R07p05_row_12 : pack 32 (R07p05_digit 12)=R07p05_rowCode 12 := by decide +kernel

private theorem R07p05_row_13 : pack 32 (R07p05_digit 13)=R07p05_rowCode 13 := by decide +kernel

private theorem R07p05_row_14 : pack 32 (R07p05_digit 14)=R07p05_rowCode 14 := by decide +kernel

private theorem R07p05_row_15 : pack 32 (R07p05_digit 15)=R07p05_rowCode 15 := by decide +kernel

private theorem R07p05_row_16 : pack 32 (R07p05_digit 16)=R07p05_rowCode 16 := by decide +kernel

private theorem R07p05_row_17 : pack 32 (R07p05_digit 17)=R07p05_rowCode 17 := by decide +kernel

private theorem R07p05_row_18 : pack 32 (R07p05_digit 18)=R07p05_rowCode 18 := by decide +kernel

private theorem R07p05_row_19 : pack 32 (R07p05_digit 19)=R07p05_rowCode 19 := by decide +kernel

private theorem R07p05_row_20 : pack 32 (R07p05_digit 20)=R07p05_rowCode 20 := by decide +kernel

private theorem R07p05_row_21 : pack 32 (R07p05_digit 21)=R07p05_rowCode 21 := by decide +kernel

theorem R07p05_row_binding : ∀ i : Fin 22,pack 32 (R07p05_digit i)=R07p05_rowCode i := by
  intro i
  fin_cases i
  · exact R07p05_row_00
  · exact R07p05_row_01
  · exact R07p05_row_02
  · exact R07p05_row_03
  · exact R07p05_row_04
  · exact R07p05_row_05
  · exact R07p05_row_06
  · exact R07p05_row_07
  · exact R07p05_row_08
  · exact R07p05_row_09
  · exact R07p05_row_10
  · exact R07p05_row_11
  · exact R07p05_row_12
  · exact R07p05_row_13
  · exact R07p05_row_14
  · exact R07p05_row_15
  · exact R07p05_row_16
  · exact R07p05_row_17
  · exact R07p05_row_18
  · exact R07p05_row_19
  · exact R07p05_row_20
  · exact R07p05_row_21

private theorem R07p05_column_00 : reversePack 32 (fun j : Fin 22 => R07p05_digit j 0)=R07p05_columnCode 0 := by decide +kernel

private theorem R07p05_column_01 : reversePack 32 (fun j : Fin 22 => R07p05_digit j 1)=R07p05_columnCode 1 := by decide +kernel

private theorem R07p05_column_02 : reversePack 32 (fun j : Fin 22 => R07p05_digit j 2)=R07p05_columnCode 2 := by decide +kernel

private theorem R07p05_column_03 : reversePack 32 (fun j : Fin 22 => R07p05_digit j 3)=R07p05_columnCode 3 := by decide +kernel

private theorem R07p05_column_04 : reversePack 32 (fun j : Fin 22 => R07p05_digit j 4)=R07p05_columnCode 4 := by decide +kernel

private theorem R07p05_column_05 : reversePack 32 (fun j : Fin 22 => R07p05_digit j 5)=R07p05_columnCode 5 := by decide +kernel

private theorem R07p05_column_06 : reversePack 32 (fun j : Fin 22 => R07p05_digit j 6)=R07p05_columnCode 6 := by decide +kernel

private theorem R07p05_column_07 : reversePack 32 (fun j : Fin 22 => R07p05_digit j 7)=R07p05_columnCode 7 := by decide +kernel

private theorem R07p05_column_08 : reversePack 32 (fun j : Fin 22 => R07p05_digit j 8)=R07p05_columnCode 8 := by decide +kernel

private theorem R07p05_column_09 : reversePack 32 (fun j : Fin 22 => R07p05_digit j 9)=R07p05_columnCode 9 := by decide +kernel

private theorem R07p05_column_10 : reversePack 32 (fun j : Fin 22 => R07p05_digit j 10)=R07p05_columnCode 10 := by decide +kernel

private theorem R07p05_column_11 : reversePack 32 (fun j : Fin 22 => R07p05_digit j 11)=R07p05_columnCode 11 := by decide +kernel

private theorem R07p05_column_12 : reversePack 32 (fun j : Fin 22 => R07p05_digit j 12)=R07p05_columnCode 12 := by decide +kernel

private theorem R07p05_column_13 : reversePack 32 (fun j : Fin 22 => R07p05_digit j 13)=R07p05_columnCode 13 := by decide +kernel

private theorem R07p05_column_14 : reversePack 32 (fun j : Fin 22 => R07p05_digit j 14)=R07p05_columnCode 14 := by decide +kernel

private theorem R07p05_column_15 : reversePack 32 (fun j : Fin 22 => R07p05_digit j 15)=R07p05_columnCode 15 := by decide +kernel

private theorem R07p05_column_16 : reversePack 32 (fun j : Fin 22 => R07p05_digit j 16)=R07p05_columnCode 16 := by decide +kernel

private theorem R07p05_column_17 : reversePack 32 (fun j : Fin 22 => R07p05_digit j 17)=R07p05_columnCode 17 := by decide +kernel

private theorem R07p05_column_18 : reversePack 32 (fun j : Fin 22 => R07p05_digit j 18)=R07p05_columnCode 18 := by decide +kernel

private theorem R07p05_column_19 : reversePack 32 (fun j : Fin 22 => R07p05_digit j 19)=R07p05_columnCode 19 := by decide +kernel

private theorem R07p05_column_20 : reversePack 32 (fun j : Fin 22 => R07p05_digit j 20)=R07p05_columnCode 20 := by decide +kernel

private theorem R07p05_column_21 : reversePack 32 (fun j : Fin 22 => R07p05_digit j 21)=R07p05_columnCode 21 := by decide +kernel

theorem R07p05_column_binding : ∀ i : Fin 22,reversePack 32 (fun j : Fin 22 => R07p05_digit j i)=R07p05_columnCode i := by
  intro i
  fin_cases i
  · exact R07p05_column_00
  · exact R07p05_column_01
  · exact R07p05_column_02
  · exact R07p05_column_03
  · exact R07p05_column_04
  · exact R07p05_column_05
  · exact R07p05_column_06
  · exact R07p05_column_07
  · exact R07p05_column_08
  · exact R07p05_column_09
  · exact R07p05_column_10
  · exact R07p05_column_11
  · exact R07p05_column_12
  · exact R07p05_column_13
  · exact R07p05_column_14
  · exact R07p05_column_15
  · exact R07p05_column_16
  · exact R07p05_column_17
  · exact R07p05_column_18
  · exact R07p05_column_19
  · exact R07p05_column_20
  · exact R07p05_column_21

def R07p05_data : PackedData 22 2 32 where
  raw := R07p05_digit
  digit_lt := R07p05_bound
  rowCode := R07p05_rowCode
  columnCode := R07p05_columnCode
  row_binding := R07p05_row_binding
  column_binding := R07p05_column_binding

def R07p06_lowColumnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1574839
  | 1 => 1984440
  | 2 => 1989207
  | 3 => 3505011
  | 4 => 3703020
  | 5 => 1659669
  | 6 => 3269406
  | 7 => 4096009
  | 8 => 3025744
  | 9 => 2974189
  | 10 => 2425045
  | 11 => 2685946
  | 12 => 2976685
  | 13 => 2136906
  | 14 => 825836
  | 15 => 3615529
  | 16 => 3037449
  | 17 => 3406423
  | 18 => 95084
  | 19 => 2638141
  | 20 => 3571716
  | 21 => 995330
  | _ => 0

def R07p06_rowCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 39654013589265397139978093569
  | 1 => 40564857892966498032973605012481
  | 2 => 1308541308332620322009370330113
  | 3 => 40853269219843121044270350368
  | 4 => 39652766883396992727907337249
  | 5 => 40852060257130018232243093537
  | 6 => 1276626883035348254130734080
  | 7 => 1181781732103317094433
  | 8 => 40853269219843122109454778401
  | 9 => 1276663482527350915315303457
  | 10 => 33
  | 11 => 39933549653205985894892544
  | 12 => 40566097043112194648594049958912
  | 13 => 40566095870748974745846737305600
  | 14 => 40891915849653817321541633056
  | 15 => 1267689287071978207327577702400
  | 16 => 40566095870748939841850147110912
  | 17 => 41832509739862549396245004157984
  | 18 => 41832471055418067431417710674976
  | 19 => 40604434498668073238657764426785
  | 20 => 1267689323633388932622923629601
  | 21 => 1307304613854424316681672228864
  | _ => 0

def R07p06_columnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 41872123784559423760117199275040
  | 1 => 1277835810006722238481466400
  | 2 => 41872122612195016031901976658976
  | 3 => 41832509739900596966981342625825
  | 4 => 40853269181760647376492561441
  | 5 => 40604471974224747129695656477728
  | 6 => 1308541307188921029488969515041
  | 7 => 40566057147342626228170476520481
  | 8 => 38723443207067742197810177
  | 9 => 40605672476521994984551245448193
  | 10 => 40604472013146224168499471745025
  | 11 => 1268928473817133120080190637057
  | 12 => 40605672438744217168998597428225
  | 13 => 1268888578084494215466142662657
  | 14 => 40853269218655296608190628864
  | 15 => 40566058356306493379450055458849
  | 16 => 40566057147379520877435460551681
  | 17 => 41872122612195016033002595549217
  | 18 => 40853268039215472628310474752
  | 19 => 40605711123188699167910717817857
  | 20 => 39614081257132168797846798369
  | 21 => 1267650600228229437780621558784
  | _ => 0

def R07p06_digit (i j : Fin 22) : ℕ := packedDigit 1 (R07p06_lowColumnCode j) i.val

private theorem R07p06_bound_00 : ∀ j : Fin 22,R07p06_digit 0 j<2 := by decide +kernel

private theorem R07p06_bound_01 : ∀ j : Fin 22,R07p06_digit 1 j<2 := by decide +kernel

private theorem R07p06_bound_02 : ∀ j : Fin 22,R07p06_digit 2 j<2 := by decide +kernel

private theorem R07p06_bound_03 : ∀ j : Fin 22,R07p06_digit 3 j<2 := by decide +kernel

private theorem R07p06_bound_04 : ∀ j : Fin 22,R07p06_digit 4 j<2 := by decide +kernel

private theorem R07p06_bound_05 : ∀ j : Fin 22,R07p06_digit 5 j<2 := by decide +kernel

private theorem R07p06_bound_06 : ∀ j : Fin 22,R07p06_digit 6 j<2 := by decide +kernel

private theorem R07p06_bound_07 : ∀ j : Fin 22,R07p06_digit 7 j<2 := by decide +kernel

private theorem R07p06_bound_08 : ∀ j : Fin 22,R07p06_digit 8 j<2 := by decide +kernel

private theorem R07p06_bound_09 : ∀ j : Fin 22,R07p06_digit 9 j<2 := by decide +kernel

private theorem R07p06_bound_10 : ∀ j : Fin 22,R07p06_digit 10 j<2 := by decide +kernel

private theorem R07p06_bound_11 : ∀ j : Fin 22,R07p06_digit 11 j<2 := by decide +kernel

private theorem R07p06_bound_12 : ∀ j : Fin 22,R07p06_digit 12 j<2 := by decide +kernel

private theorem R07p06_bound_13 : ∀ j : Fin 22,R07p06_digit 13 j<2 := by decide +kernel

private theorem R07p06_bound_14 : ∀ j : Fin 22,R07p06_digit 14 j<2 := by decide +kernel

private theorem R07p06_bound_15 : ∀ j : Fin 22,R07p06_digit 15 j<2 := by decide +kernel

private theorem R07p06_bound_16 : ∀ j : Fin 22,R07p06_digit 16 j<2 := by decide +kernel

private theorem R07p06_bound_17 : ∀ j : Fin 22,R07p06_digit 17 j<2 := by decide +kernel

private theorem R07p06_bound_18 : ∀ j : Fin 22,R07p06_digit 18 j<2 := by decide +kernel

private theorem R07p06_bound_19 : ∀ j : Fin 22,R07p06_digit 19 j<2 := by decide +kernel

private theorem R07p06_bound_20 : ∀ j : Fin 22,R07p06_digit 20 j<2 := by decide +kernel

private theorem R07p06_bound_21 : ∀ j : Fin 22,R07p06_digit 21 j<2 := by decide +kernel

theorem R07p06_bound : ∀ i j : Fin 22,R07p06_digit i j<2 := by
  intro i j
  fin_cases i
  · exact R07p06_bound_00 j
  · exact R07p06_bound_01 j
  · exact R07p06_bound_02 j
  · exact R07p06_bound_03 j
  · exact R07p06_bound_04 j
  · exact R07p06_bound_05 j
  · exact R07p06_bound_06 j
  · exact R07p06_bound_07 j
  · exact R07p06_bound_08 j
  · exact R07p06_bound_09 j
  · exact R07p06_bound_10 j
  · exact R07p06_bound_11 j
  · exact R07p06_bound_12 j
  · exact R07p06_bound_13 j
  · exact R07p06_bound_14 j
  · exact R07p06_bound_15 j
  · exact R07p06_bound_16 j
  · exact R07p06_bound_17 j
  · exact R07p06_bound_18 j
  · exact R07p06_bound_19 j
  · exact R07p06_bound_20 j
  · exact R07p06_bound_21 j

private theorem R07p06_row_00 : pack 32 (R07p06_digit 0)=R07p06_rowCode 0 := by decide +kernel

private theorem R07p06_row_01 : pack 32 (R07p06_digit 1)=R07p06_rowCode 1 := by decide +kernel

private theorem R07p06_row_02 : pack 32 (R07p06_digit 2)=R07p06_rowCode 2 := by decide +kernel

private theorem R07p06_row_03 : pack 32 (R07p06_digit 3)=R07p06_rowCode 3 := by decide +kernel

private theorem R07p06_row_04 : pack 32 (R07p06_digit 4)=R07p06_rowCode 4 := by decide +kernel

private theorem R07p06_row_05 : pack 32 (R07p06_digit 5)=R07p06_rowCode 5 := by decide +kernel

private theorem R07p06_row_06 : pack 32 (R07p06_digit 6)=R07p06_rowCode 6 := by decide +kernel

private theorem R07p06_row_07 : pack 32 (R07p06_digit 7)=R07p06_rowCode 7 := by decide +kernel

private theorem R07p06_row_08 : pack 32 (R07p06_digit 8)=R07p06_rowCode 8 := by decide +kernel

private theorem R07p06_row_09 : pack 32 (R07p06_digit 9)=R07p06_rowCode 9 := by decide +kernel

private theorem R07p06_row_10 : pack 32 (R07p06_digit 10)=R07p06_rowCode 10 := by decide +kernel

private theorem R07p06_row_11 : pack 32 (R07p06_digit 11)=R07p06_rowCode 11 := by decide +kernel

private theorem R07p06_row_12 : pack 32 (R07p06_digit 12)=R07p06_rowCode 12 := by decide +kernel

private theorem R07p06_row_13 : pack 32 (R07p06_digit 13)=R07p06_rowCode 13 := by decide +kernel

private theorem R07p06_row_14 : pack 32 (R07p06_digit 14)=R07p06_rowCode 14 := by decide +kernel

private theorem R07p06_row_15 : pack 32 (R07p06_digit 15)=R07p06_rowCode 15 := by decide +kernel

private theorem R07p06_row_16 : pack 32 (R07p06_digit 16)=R07p06_rowCode 16 := by decide +kernel

private theorem R07p06_row_17 : pack 32 (R07p06_digit 17)=R07p06_rowCode 17 := by decide +kernel

private theorem R07p06_row_18 : pack 32 (R07p06_digit 18)=R07p06_rowCode 18 := by decide +kernel

private theorem R07p06_row_19 : pack 32 (R07p06_digit 19)=R07p06_rowCode 19 := by decide +kernel

private theorem R07p06_row_20 : pack 32 (R07p06_digit 20)=R07p06_rowCode 20 := by decide +kernel

private theorem R07p06_row_21 : pack 32 (R07p06_digit 21)=R07p06_rowCode 21 := by decide +kernel

theorem R07p06_row_binding : ∀ i : Fin 22,pack 32 (R07p06_digit i)=R07p06_rowCode i := by
  intro i
  fin_cases i
  · exact R07p06_row_00
  · exact R07p06_row_01
  · exact R07p06_row_02
  · exact R07p06_row_03
  · exact R07p06_row_04
  · exact R07p06_row_05
  · exact R07p06_row_06
  · exact R07p06_row_07
  · exact R07p06_row_08
  · exact R07p06_row_09
  · exact R07p06_row_10
  · exact R07p06_row_11
  · exact R07p06_row_12
  · exact R07p06_row_13
  · exact R07p06_row_14
  · exact R07p06_row_15
  · exact R07p06_row_16
  · exact R07p06_row_17
  · exact R07p06_row_18
  · exact R07p06_row_19
  · exact R07p06_row_20
  · exact R07p06_row_21

private theorem R07p06_column_00 : reversePack 32 (fun j : Fin 22 => R07p06_digit j 0)=R07p06_columnCode 0 := by decide +kernel

private theorem R07p06_column_01 : reversePack 32 (fun j : Fin 22 => R07p06_digit j 1)=R07p06_columnCode 1 := by decide +kernel

private theorem R07p06_column_02 : reversePack 32 (fun j : Fin 22 => R07p06_digit j 2)=R07p06_columnCode 2 := by decide +kernel

private theorem R07p06_column_03 : reversePack 32 (fun j : Fin 22 => R07p06_digit j 3)=R07p06_columnCode 3 := by decide +kernel

private theorem R07p06_column_04 : reversePack 32 (fun j : Fin 22 => R07p06_digit j 4)=R07p06_columnCode 4 := by decide +kernel

private theorem R07p06_column_05 : reversePack 32 (fun j : Fin 22 => R07p06_digit j 5)=R07p06_columnCode 5 := by decide +kernel

private theorem R07p06_column_06 : reversePack 32 (fun j : Fin 22 => R07p06_digit j 6)=R07p06_columnCode 6 := by decide +kernel

private theorem R07p06_column_07 : reversePack 32 (fun j : Fin 22 => R07p06_digit j 7)=R07p06_columnCode 7 := by decide +kernel

private theorem R07p06_column_08 : reversePack 32 (fun j : Fin 22 => R07p06_digit j 8)=R07p06_columnCode 8 := by decide +kernel

private theorem R07p06_column_09 : reversePack 32 (fun j : Fin 22 => R07p06_digit j 9)=R07p06_columnCode 9 := by decide +kernel

private theorem R07p06_column_10 : reversePack 32 (fun j : Fin 22 => R07p06_digit j 10)=R07p06_columnCode 10 := by decide +kernel

private theorem R07p06_column_11 : reversePack 32 (fun j : Fin 22 => R07p06_digit j 11)=R07p06_columnCode 11 := by decide +kernel

private theorem R07p06_column_12 : reversePack 32 (fun j : Fin 22 => R07p06_digit j 12)=R07p06_columnCode 12 := by decide +kernel

private theorem R07p06_column_13 : reversePack 32 (fun j : Fin 22 => R07p06_digit j 13)=R07p06_columnCode 13 := by decide +kernel

private theorem R07p06_column_14 : reversePack 32 (fun j : Fin 22 => R07p06_digit j 14)=R07p06_columnCode 14 := by decide +kernel

private theorem R07p06_column_15 : reversePack 32 (fun j : Fin 22 => R07p06_digit j 15)=R07p06_columnCode 15 := by decide +kernel

private theorem R07p06_column_16 : reversePack 32 (fun j : Fin 22 => R07p06_digit j 16)=R07p06_columnCode 16 := by decide +kernel

private theorem R07p06_column_17 : reversePack 32 (fun j : Fin 22 => R07p06_digit j 17)=R07p06_columnCode 17 := by decide +kernel

private theorem R07p06_column_18 : reversePack 32 (fun j : Fin 22 => R07p06_digit j 18)=R07p06_columnCode 18 := by decide +kernel

private theorem R07p06_column_19 : reversePack 32 (fun j : Fin 22 => R07p06_digit j 19)=R07p06_columnCode 19 := by decide +kernel

private theorem R07p06_column_20 : reversePack 32 (fun j : Fin 22 => R07p06_digit j 20)=R07p06_columnCode 20 := by decide +kernel

private theorem R07p06_column_21 : reversePack 32 (fun j : Fin 22 => R07p06_digit j 21)=R07p06_columnCode 21 := by decide +kernel

theorem R07p06_column_binding : ∀ i : Fin 22,reversePack 32 (fun j : Fin 22 => R07p06_digit j i)=R07p06_columnCode i := by
  intro i
  fin_cases i
  · exact R07p06_column_00
  · exact R07p06_column_01
  · exact R07p06_column_02
  · exact R07p06_column_03
  · exact R07p06_column_04
  · exact R07p06_column_05
  · exact R07p06_column_06
  · exact R07p06_column_07
  · exact R07p06_column_08
  · exact R07p06_column_09
  · exact R07p06_column_10
  · exact R07p06_column_11
  · exact R07p06_column_12
  · exact R07p06_column_13
  · exact R07p06_column_14
  · exact R07p06_column_15
  · exact R07p06_column_16
  · exact R07p06_column_17
  · exact R07p06_column_18
  · exact R07p06_column_19
  · exact R07p06_column_20
  · exact R07p06_column_21

def R07p06_data : PackedData 22 2 32 where
  raw := R07p06_digit
  digit_lt := R07p06_bound
  rowCode := R07p06_rowCode
  columnCode := R07p06_columnCode
  row_binding := R07p06_row_binding
  column_binding := R07p06_column_binding

def R07p07_lowColumnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 3256331
  | 1 => 1144762
  | 2 => 3665924
  | 3 => 2282285
  | 4 => 502625
  | 5 => 2130807
  | 6 => 1817450
  | 7 => 2191834
  | 8 => 2490963
  | 9 => 830225
  | 10 => 862539
  | 11 => 2123838
  | 12 => 3709417
  | 13 => 3247037
  | 14 => 2537620
  | 15 => 3707817
  | 16 => 995330
  | 17 => 3412002
  | 18 => 2468797
  | 19 => 2584895
  | 20 => 600118
  | 21 => 3571716
  | _ => 0

def R07p07_rowCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 40852059113396983864683954177
  | 1 => 1307304576037446008888144953377
  | 2 => 41873321830045508936124759835648
  | 3 => 40852059113432976413218078753
  | 4 => 1308502622742168124548500684832
  | 5 => 1308541344967888920109279903776
  | 6 => 1154048539493400576
  | 7 => 1237979036855273635857825824
  | 8 => 40852059113396982800605806624
  | 9 => 1237977855110767664472031264
  | 10 => 32
  | 11 => 1268888541486190002023412269056
  | 12 => 39654014769855856774150652961
  | 13 => 1308503831631095375831692739617
  | 14 => 39614081257168197628150711328
  | 15 => 40566057186340196156681481126913
  | 16 => 1308503830487361179280309486625
  | 17 => 40604434498666884253138447008768
  | 18 => 40605711124332398462630141887488
  | 19 => 1267651846934134961672999141376
  | 20 => 40564857930746546788638354572321
  | 21 => 40605709953223591988357287150593
  | _ => 0

def R07p07_columnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 41833707747570855665951095914529
  | 1 => 1268928436038236160019100860448
  | 2 => 39614081257132205116123807777
  | 3 => 40605672437563624456467180945409
  | 4 => 40564820454046139862133391785984
  | 5 => 41872123821157727973561004457985
  | 6 => 1268889787010313831194863600672
  | 7 => 1268927264890159458045462052865
  | 8 => 41832508530937882701986566012929
  | 9 => 40564857892967616052680611365888
  | 10 => 41833707785386682107770137773056
  | 11 => 1308542516076695360364917817345
  | 12 => 40566058395264863975705921192993
  | 13 => 40605711124370444835999390367777
  | 14 => 39652768063952619832639258625
  | 15 => 40566058357487083908353459487777
  | 16 => 1267650600228229437780621558784
  | 17 => 1267651809154049051310250033185
  | 18 => 40605711124370444837098902028289
  | 19 => 41873361723416928605691339374593
  | 20 => 1307304576037409980055692510208
  | 21 => 39614081257132168797846798369
  | _ => 0

def R07p07_digit (i j : Fin 22) : ℕ := packedDigit 1 (R07p07_lowColumnCode j) i.val

private theorem R07p07_bound_00 : ∀ j : Fin 22,R07p07_digit 0 j<2 := by decide +kernel

private theorem R07p07_bound_01 : ∀ j : Fin 22,R07p07_digit 1 j<2 := by decide +kernel

private theorem R07p07_bound_02 : ∀ j : Fin 22,R07p07_digit 2 j<2 := by decide +kernel

private theorem R07p07_bound_03 : ∀ j : Fin 22,R07p07_digit 3 j<2 := by decide +kernel

private theorem R07p07_bound_04 : ∀ j : Fin 22,R07p07_digit 4 j<2 := by decide +kernel

private theorem R07p07_bound_05 : ∀ j : Fin 22,R07p07_digit 5 j<2 := by decide +kernel

private theorem R07p07_bound_06 : ∀ j : Fin 22,R07p07_digit 6 j<2 := by decide +kernel

private theorem R07p07_bound_07 : ∀ j : Fin 22,R07p07_digit 7 j<2 := by decide +kernel

private theorem R07p07_bound_08 : ∀ j : Fin 22,R07p07_digit 8 j<2 := by decide +kernel

private theorem R07p07_bound_09 : ∀ j : Fin 22,R07p07_digit 9 j<2 := by decide +kernel

private theorem R07p07_bound_10 : ∀ j : Fin 22,R07p07_digit 10 j<2 := by decide +kernel

private theorem R07p07_bound_11 : ∀ j : Fin 22,R07p07_digit 11 j<2 := by decide +kernel

private theorem R07p07_bound_12 : ∀ j : Fin 22,R07p07_digit 12 j<2 := by decide +kernel

private theorem R07p07_bound_13 : ∀ j : Fin 22,R07p07_digit 13 j<2 := by decide +kernel

private theorem R07p07_bound_14 : ∀ j : Fin 22,R07p07_digit 14 j<2 := by decide +kernel

private theorem R07p07_bound_15 : ∀ j : Fin 22,R07p07_digit 15 j<2 := by decide +kernel

private theorem R07p07_bound_16 : ∀ j : Fin 22,R07p07_digit 16 j<2 := by decide +kernel

private theorem R07p07_bound_17 : ∀ j : Fin 22,R07p07_digit 17 j<2 := by decide +kernel

private theorem R07p07_bound_18 : ∀ j : Fin 22,R07p07_digit 18 j<2 := by decide +kernel

private theorem R07p07_bound_19 : ∀ j : Fin 22,R07p07_digit 19 j<2 := by decide +kernel

private theorem R07p07_bound_20 : ∀ j : Fin 22,R07p07_digit 20 j<2 := by decide +kernel

private theorem R07p07_bound_21 : ∀ j : Fin 22,R07p07_digit 21 j<2 := by decide +kernel

theorem R07p07_bound : ∀ i j : Fin 22,R07p07_digit i j<2 := by
  intro i j
  fin_cases i
  · exact R07p07_bound_00 j
  · exact R07p07_bound_01 j
  · exact R07p07_bound_02 j
  · exact R07p07_bound_03 j
  · exact R07p07_bound_04 j
  · exact R07p07_bound_05 j
  · exact R07p07_bound_06 j
  · exact R07p07_bound_07 j
  · exact R07p07_bound_08 j
  · exact R07p07_bound_09 j
  · exact R07p07_bound_10 j
  · exact R07p07_bound_11 j
  · exact R07p07_bound_12 j
  · exact R07p07_bound_13 j
  · exact R07p07_bound_14 j
  · exact R07p07_bound_15 j
  · exact R07p07_bound_16 j
  · exact R07p07_bound_17 j
  · exact R07p07_bound_18 j
  · exact R07p07_bound_19 j
  · exact R07p07_bound_20 j
  · exact R07p07_bound_21 j

private theorem R07p07_row_00 : pack 32 (R07p07_digit 0)=R07p07_rowCode 0 := by decide +kernel

private theorem R07p07_row_01 : pack 32 (R07p07_digit 1)=R07p07_rowCode 1 := by decide +kernel

private theorem R07p07_row_02 : pack 32 (R07p07_digit 2)=R07p07_rowCode 2 := by decide +kernel

private theorem R07p07_row_03 : pack 32 (R07p07_digit 3)=R07p07_rowCode 3 := by decide +kernel

private theorem R07p07_row_04 : pack 32 (R07p07_digit 4)=R07p07_rowCode 4 := by decide +kernel

private theorem R07p07_row_05 : pack 32 (R07p07_digit 5)=R07p07_rowCode 5 := by decide +kernel

private theorem R07p07_row_06 : pack 32 (R07p07_digit 6)=R07p07_rowCode 6 := by decide +kernel

private theorem R07p07_row_07 : pack 32 (R07p07_digit 7)=R07p07_rowCode 7 := by decide +kernel

private theorem R07p07_row_08 : pack 32 (R07p07_digit 8)=R07p07_rowCode 8 := by decide +kernel

private theorem R07p07_row_09 : pack 32 (R07p07_digit 9)=R07p07_rowCode 9 := by decide +kernel

private theorem R07p07_row_10 : pack 32 (R07p07_digit 10)=R07p07_rowCode 10 := by decide +kernel

private theorem R07p07_row_11 : pack 32 (R07p07_digit 11)=R07p07_rowCode 11 := by decide +kernel

private theorem R07p07_row_12 : pack 32 (R07p07_digit 12)=R07p07_rowCode 12 := by decide +kernel

private theorem R07p07_row_13 : pack 32 (R07p07_digit 13)=R07p07_rowCode 13 := by decide +kernel

private theorem R07p07_row_14 : pack 32 (R07p07_digit 14)=R07p07_rowCode 14 := by decide +kernel

private theorem R07p07_row_15 : pack 32 (R07p07_digit 15)=R07p07_rowCode 15 := by decide +kernel

private theorem R07p07_row_16 : pack 32 (R07p07_digit 16)=R07p07_rowCode 16 := by decide +kernel

private theorem R07p07_row_17 : pack 32 (R07p07_digit 17)=R07p07_rowCode 17 := by decide +kernel

private theorem R07p07_row_18 : pack 32 (R07p07_digit 18)=R07p07_rowCode 18 := by decide +kernel

private theorem R07p07_row_19 : pack 32 (R07p07_digit 19)=R07p07_rowCode 19 := by decide +kernel

private theorem R07p07_row_20 : pack 32 (R07p07_digit 20)=R07p07_rowCode 20 := by decide +kernel

private theorem R07p07_row_21 : pack 32 (R07p07_digit 21)=R07p07_rowCode 21 := by decide +kernel

theorem R07p07_row_binding : ∀ i : Fin 22,pack 32 (R07p07_digit i)=R07p07_rowCode i := by
  intro i
  fin_cases i
  · exact R07p07_row_00
  · exact R07p07_row_01
  · exact R07p07_row_02
  · exact R07p07_row_03
  · exact R07p07_row_04
  · exact R07p07_row_05
  · exact R07p07_row_06
  · exact R07p07_row_07
  · exact R07p07_row_08
  · exact R07p07_row_09
  · exact R07p07_row_10
  · exact R07p07_row_11
  · exact R07p07_row_12
  · exact R07p07_row_13
  · exact R07p07_row_14
  · exact R07p07_row_15
  · exact R07p07_row_16
  · exact R07p07_row_17
  · exact R07p07_row_18
  · exact R07p07_row_19
  · exact R07p07_row_20
  · exact R07p07_row_21

private theorem R07p07_column_00 : reversePack 32 (fun j : Fin 22 => R07p07_digit j 0)=R07p07_columnCode 0 := by decide +kernel

private theorem R07p07_column_01 : reversePack 32 (fun j : Fin 22 => R07p07_digit j 1)=R07p07_columnCode 1 := by decide +kernel

private theorem R07p07_column_02 : reversePack 32 (fun j : Fin 22 => R07p07_digit j 2)=R07p07_columnCode 2 := by decide +kernel

private theorem R07p07_column_03 : reversePack 32 (fun j : Fin 22 => R07p07_digit j 3)=R07p07_columnCode 3 := by decide +kernel

private theorem R07p07_column_04 : reversePack 32 (fun j : Fin 22 => R07p07_digit j 4)=R07p07_columnCode 4 := by decide +kernel

private theorem R07p07_column_05 : reversePack 32 (fun j : Fin 22 => R07p07_digit j 5)=R07p07_columnCode 5 := by decide +kernel

private theorem R07p07_column_06 : reversePack 32 (fun j : Fin 22 => R07p07_digit j 6)=R07p07_columnCode 6 := by decide +kernel

private theorem R07p07_column_07 : reversePack 32 (fun j : Fin 22 => R07p07_digit j 7)=R07p07_columnCode 7 := by decide +kernel

private theorem R07p07_column_08 : reversePack 32 (fun j : Fin 22 => R07p07_digit j 8)=R07p07_columnCode 8 := by decide +kernel

private theorem R07p07_column_09 : reversePack 32 (fun j : Fin 22 => R07p07_digit j 9)=R07p07_columnCode 9 := by decide +kernel

private theorem R07p07_column_10 : reversePack 32 (fun j : Fin 22 => R07p07_digit j 10)=R07p07_columnCode 10 := by decide +kernel

private theorem R07p07_column_11 : reversePack 32 (fun j : Fin 22 => R07p07_digit j 11)=R07p07_columnCode 11 := by decide +kernel

private theorem R07p07_column_12 : reversePack 32 (fun j : Fin 22 => R07p07_digit j 12)=R07p07_columnCode 12 := by decide +kernel

private theorem R07p07_column_13 : reversePack 32 (fun j : Fin 22 => R07p07_digit j 13)=R07p07_columnCode 13 := by decide +kernel

private theorem R07p07_column_14 : reversePack 32 (fun j : Fin 22 => R07p07_digit j 14)=R07p07_columnCode 14 := by decide +kernel

private theorem R07p07_column_15 : reversePack 32 (fun j : Fin 22 => R07p07_digit j 15)=R07p07_columnCode 15 := by decide +kernel

private theorem R07p07_column_16 : reversePack 32 (fun j : Fin 22 => R07p07_digit j 16)=R07p07_columnCode 16 := by decide +kernel

private theorem R07p07_column_17 : reversePack 32 (fun j : Fin 22 => R07p07_digit j 17)=R07p07_columnCode 17 := by decide +kernel

private theorem R07p07_column_18 : reversePack 32 (fun j : Fin 22 => R07p07_digit j 18)=R07p07_columnCode 18 := by decide +kernel

private theorem R07p07_column_19 : reversePack 32 (fun j : Fin 22 => R07p07_digit j 19)=R07p07_columnCode 19 := by decide +kernel

private theorem R07p07_column_20 : reversePack 32 (fun j : Fin 22 => R07p07_digit j 20)=R07p07_columnCode 20 := by decide +kernel

private theorem R07p07_column_21 : reversePack 32 (fun j : Fin 22 => R07p07_digit j 21)=R07p07_columnCode 21 := by decide +kernel

theorem R07p07_column_binding : ∀ i : Fin 22,reversePack 32 (fun j : Fin 22 => R07p07_digit j i)=R07p07_columnCode i := by
  intro i
  fin_cases i
  · exact R07p07_column_00
  · exact R07p07_column_01
  · exact R07p07_column_02
  · exact R07p07_column_03
  · exact R07p07_column_04
  · exact R07p07_column_05
  · exact R07p07_column_06
  · exact R07p07_column_07
  · exact R07p07_column_08
  · exact R07p07_column_09
  · exact R07p07_column_10
  · exact R07p07_column_11
  · exact R07p07_column_12
  · exact R07p07_column_13
  · exact R07p07_column_14
  · exact R07p07_column_15
  · exact R07p07_column_16
  · exact R07p07_column_17
  · exact R07p07_column_18
  · exact R07p07_column_19
  · exact R07p07_column_20
  · exact R07p07_column_21

def R07p07_data : PackedData 22 2 32 where
  raw := R07p07_digit
  digit_lt := R07p07_bound
  rowCode := R07p07_rowCode
  columnCode := R07p07_columnCode
  row_binding := R07p07_row_binding
  column_binding := R07p07_column_binding

end SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoCaches05
