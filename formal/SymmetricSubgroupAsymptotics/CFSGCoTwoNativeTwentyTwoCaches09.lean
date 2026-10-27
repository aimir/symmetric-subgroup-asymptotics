import SymmetricSubgroupAsymptotics.MatrixKroneckerProductReflection
import Mathlib.Tactic.FinCases

/-! Fixed Co2 binary22 shared caches. Every digit and pack binding is kernel checked. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoCaches09
open MatrixKroneckerProductReflection MatrixKroneckerDotReflection
open MatrixNaturalRowDotReflection SmallNaturalMatrixProductReflection

def R09p06_lowColumnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1927514
  | 1 => 2980602
  | 2 => 3020966
  | 3 => 2226116
  | 4 => 3806683
  | 5 => 3692935
  | 6 => 407607
  | 7 => 2032212
  | 8 => 2256752
  | 9 => 279373
  | 10 => 1649484
  | 11 => 1917772
  | 12 => 2908777
  | 13 => 632919
  | 14 => 1294427
  | 15 => 621255
  | 16 => 1549171
  | 17 => 1862198
  | 18 => 5280
  | 19 => 2116977
  | 20 => 1193153
  | 21 => 600118
  | _ => 0

def R09p06_rowCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1307265929408751113434729283584
  | 1 => 40564859140851805102480368337953
  | 2 => 40564857930745431057049438946304
  | 3 => 1181781732103317094433
  | 4 => 40604473184330005409453816414241
  | 5 => 40605711123152958602334131192864
  | 6 => 1307265929408788269264419192865
  | 7 => 1268888578046446644728798676000
  | 8 => 39615290182988974406790840321
  | 9 => 39932332169258239703154720
  | 10 => 1308502621524646951667887013888
  | 11 => 40604472012002527162929971725345
  | 12 => 1268888578046446644729872417824
  | 13 => 41832509739900596931763650986017
  | 14 => 39652805844072307190478700577
  | 15 => 1210143304723494005145600
  | 16 => 40564820455225614589076954972193
  | 17 => 1267651810334640637978235372544
  | 18 => 39894553236268284196684833
  | 19 => 40564857930746583943368600978465
  | 20 => 1267690495960905459708199960577
  | 21 => 39614081258285091400925086752
  | _ => 0

def R09p06_columnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1268927263709568928043585537056
  | 1 => 1268928473780239631931731379201
  | 2 => 1307265891591773966724341203969
  | 3 => 39614120254738127239740653569
  | 4 => 41833746472193536333603079717921
  | 5 => 41872083890006188688171446830113
  | 6 => 41872123783340750863134534696960
  | 7 => 39652804663444621392165766176
  | 8 => 39932369062711202751184897
  | 9 => 40605671266416736669609721102336
  | 10 => 40852059113396948680310785056
  | 11 => 40852059113395821715252085792
  | 12 => 40566058394048530628394216358913
  | 13 => 41872122612193863076279255827456
  | 14 => 41833746470976015160792325292064
  | 15 => 41872083927749379985585341465600
  | 16 => 41832509739900595805863778746400
  | 17 => 1307304576038562901594625573920
  | 18 => 1210106447299327977062400
  | 19 => 40564859139671250636493134233601
  | 20 => 40564819246262900396649979314208
  | 21 => 1307304576037409980055692510208
  | _ => 0

def R09p06_digit (i j : Fin 22) : ℕ := packedDigit 1 (R09p06_lowColumnCode j) i.val

private theorem R09p06_bound_00 : ∀ j : Fin 22,R09p06_digit 0 j<2 := by decide +kernel

private theorem R09p06_bound_01 : ∀ j : Fin 22,R09p06_digit 1 j<2 := by decide +kernel

private theorem R09p06_bound_02 : ∀ j : Fin 22,R09p06_digit 2 j<2 := by decide +kernel

private theorem R09p06_bound_03 : ∀ j : Fin 22,R09p06_digit 3 j<2 := by decide +kernel

private theorem R09p06_bound_04 : ∀ j : Fin 22,R09p06_digit 4 j<2 := by decide +kernel

private theorem R09p06_bound_05 : ∀ j : Fin 22,R09p06_digit 5 j<2 := by decide +kernel

private theorem R09p06_bound_06 : ∀ j : Fin 22,R09p06_digit 6 j<2 := by decide +kernel

private theorem R09p06_bound_07 : ∀ j : Fin 22,R09p06_digit 7 j<2 := by decide +kernel

private theorem R09p06_bound_08 : ∀ j : Fin 22,R09p06_digit 8 j<2 := by decide +kernel

private theorem R09p06_bound_09 : ∀ j : Fin 22,R09p06_digit 9 j<2 := by decide +kernel

private theorem R09p06_bound_10 : ∀ j : Fin 22,R09p06_digit 10 j<2 := by decide +kernel

private theorem R09p06_bound_11 : ∀ j : Fin 22,R09p06_digit 11 j<2 := by decide +kernel

private theorem R09p06_bound_12 : ∀ j : Fin 22,R09p06_digit 12 j<2 := by decide +kernel

private theorem R09p06_bound_13 : ∀ j : Fin 22,R09p06_digit 13 j<2 := by decide +kernel

private theorem R09p06_bound_14 : ∀ j : Fin 22,R09p06_digit 14 j<2 := by decide +kernel

private theorem R09p06_bound_15 : ∀ j : Fin 22,R09p06_digit 15 j<2 := by decide +kernel

private theorem R09p06_bound_16 : ∀ j : Fin 22,R09p06_digit 16 j<2 := by decide +kernel

private theorem R09p06_bound_17 : ∀ j : Fin 22,R09p06_digit 17 j<2 := by decide +kernel

private theorem R09p06_bound_18 : ∀ j : Fin 22,R09p06_digit 18 j<2 := by decide +kernel

private theorem R09p06_bound_19 : ∀ j : Fin 22,R09p06_digit 19 j<2 := by decide +kernel

private theorem R09p06_bound_20 : ∀ j : Fin 22,R09p06_digit 20 j<2 := by decide +kernel

private theorem R09p06_bound_21 : ∀ j : Fin 22,R09p06_digit 21 j<2 := by decide +kernel

theorem R09p06_bound : ∀ i j : Fin 22,R09p06_digit i j<2 := by
  intro i j
  fin_cases i
  · exact R09p06_bound_00 j
  · exact R09p06_bound_01 j
  · exact R09p06_bound_02 j
  · exact R09p06_bound_03 j
  · exact R09p06_bound_04 j
  · exact R09p06_bound_05 j
  · exact R09p06_bound_06 j
  · exact R09p06_bound_07 j
  · exact R09p06_bound_08 j
  · exact R09p06_bound_09 j
  · exact R09p06_bound_10 j
  · exact R09p06_bound_11 j
  · exact R09p06_bound_12 j
  · exact R09p06_bound_13 j
  · exact R09p06_bound_14 j
  · exact R09p06_bound_15 j
  · exact R09p06_bound_16 j
  · exact R09p06_bound_17 j
  · exact R09p06_bound_18 j
  · exact R09p06_bound_19 j
  · exact R09p06_bound_20 j
  · exact R09p06_bound_21 j

private theorem R09p06_row_00 : pack 32 (R09p06_digit 0)=R09p06_rowCode 0 := by decide +kernel

private theorem R09p06_row_01 : pack 32 (R09p06_digit 1)=R09p06_rowCode 1 := by decide +kernel

private theorem R09p06_row_02 : pack 32 (R09p06_digit 2)=R09p06_rowCode 2 := by decide +kernel

private theorem R09p06_row_03 : pack 32 (R09p06_digit 3)=R09p06_rowCode 3 := by decide +kernel

private theorem R09p06_row_04 : pack 32 (R09p06_digit 4)=R09p06_rowCode 4 := by decide +kernel

private theorem R09p06_row_05 : pack 32 (R09p06_digit 5)=R09p06_rowCode 5 := by decide +kernel

private theorem R09p06_row_06 : pack 32 (R09p06_digit 6)=R09p06_rowCode 6 := by decide +kernel

private theorem R09p06_row_07 : pack 32 (R09p06_digit 7)=R09p06_rowCode 7 := by decide +kernel

private theorem R09p06_row_08 : pack 32 (R09p06_digit 8)=R09p06_rowCode 8 := by decide +kernel

private theorem R09p06_row_09 : pack 32 (R09p06_digit 9)=R09p06_rowCode 9 := by decide +kernel

private theorem R09p06_row_10 : pack 32 (R09p06_digit 10)=R09p06_rowCode 10 := by decide +kernel

private theorem R09p06_row_11 : pack 32 (R09p06_digit 11)=R09p06_rowCode 11 := by decide +kernel

private theorem R09p06_row_12 : pack 32 (R09p06_digit 12)=R09p06_rowCode 12 := by decide +kernel

private theorem R09p06_row_13 : pack 32 (R09p06_digit 13)=R09p06_rowCode 13 := by decide +kernel

private theorem R09p06_row_14 : pack 32 (R09p06_digit 14)=R09p06_rowCode 14 := by decide +kernel

private theorem R09p06_row_15 : pack 32 (R09p06_digit 15)=R09p06_rowCode 15 := by decide +kernel

private theorem R09p06_row_16 : pack 32 (R09p06_digit 16)=R09p06_rowCode 16 := by decide +kernel

private theorem R09p06_row_17 : pack 32 (R09p06_digit 17)=R09p06_rowCode 17 := by decide +kernel

private theorem R09p06_row_18 : pack 32 (R09p06_digit 18)=R09p06_rowCode 18 := by decide +kernel

private theorem R09p06_row_19 : pack 32 (R09p06_digit 19)=R09p06_rowCode 19 := by decide +kernel

private theorem R09p06_row_20 : pack 32 (R09p06_digit 20)=R09p06_rowCode 20 := by decide +kernel

private theorem R09p06_row_21 : pack 32 (R09p06_digit 21)=R09p06_rowCode 21 := by decide +kernel

theorem R09p06_row_binding : ∀ i : Fin 22,pack 32 (R09p06_digit i)=R09p06_rowCode i := by
  intro i
  fin_cases i
  · exact R09p06_row_00
  · exact R09p06_row_01
  · exact R09p06_row_02
  · exact R09p06_row_03
  · exact R09p06_row_04
  · exact R09p06_row_05
  · exact R09p06_row_06
  · exact R09p06_row_07
  · exact R09p06_row_08
  · exact R09p06_row_09
  · exact R09p06_row_10
  · exact R09p06_row_11
  · exact R09p06_row_12
  · exact R09p06_row_13
  · exact R09p06_row_14
  · exact R09p06_row_15
  · exact R09p06_row_16
  · exact R09p06_row_17
  · exact R09p06_row_18
  · exact R09p06_row_19
  · exact R09p06_row_20
  · exact R09p06_row_21

private theorem R09p06_column_00 : reversePack 32 (fun j : Fin 22 => R09p06_digit j 0)=R09p06_columnCode 0 := by decide +kernel

private theorem R09p06_column_01 : reversePack 32 (fun j : Fin 22 => R09p06_digit j 1)=R09p06_columnCode 1 := by decide +kernel

private theorem R09p06_column_02 : reversePack 32 (fun j : Fin 22 => R09p06_digit j 2)=R09p06_columnCode 2 := by decide +kernel

private theorem R09p06_column_03 : reversePack 32 (fun j : Fin 22 => R09p06_digit j 3)=R09p06_columnCode 3 := by decide +kernel

private theorem R09p06_column_04 : reversePack 32 (fun j : Fin 22 => R09p06_digit j 4)=R09p06_columnCode 4 := by decide +kernel

private theorem R09p06_column_05 : reversePack 32 (fun j : Fin 22 => R09p06_digit j 5)=R09p06_columnCode 5 := by decide +kernel

private theorem R09p06_column_06 : reversePack 32 (fun j : Fin 22 => R09p06_digit j 6)=R09p06_columnCode 6 := by decide +kernel

private theorem R09p06_column_07 : reversePack 32 (fun j : Fin 22 => R09p06_digit j 7)=R09p06_columnCode 7 := by decide +kernel

private theorem R09p06_column_08 : reversePack 32 (fun j : Fin 22 => R09p06_digit j 8)=R09p06_columnCode 8 := by decide +kernel

private theorem R09p06_column_09 : reversePack 32 (fun j : Fin 22 => R09p06_digit j 9)=R09p06_columnCode 9 := by decide +kernel

private theorem R09p06_column_10 : reversePack 32 (fun j : Fin 22 => R09p06_digit j 10)=R09p06_columnCode 10 := by decide +kernel

private theorem R09p06_column_11 : reversePack 32 (fun j : Fin 22 => R09p06_digit j 11)=R09p06_columnCode 11 := by decide +kernel

private theorem R09p06_column_12 : reversePack 32 (fun j : Fin 22 => R09p06_digit j 12)=R09p06_columnCode 12 := by decide +kernel

private theorem R09p06_column_13 : reversePack 32 (fun j : Fin 22 => R09p06_digit j 13)=R09p06_columnCode 13 := by decide +kernel

private theorem R09p06_column_14 : reversePack 32 (fun j : Fin 22 => R09p06_digit j 14)=R09p06_columnCode 14 := by decide +kernel

private theorem R09p06_column_15 : reversePack 32 (fun j : Fin 22 => R09p06_digit j 15)=R09p06_columnCode 15 := by decide +kernel

private theorem R09p06_column_16 : reversePack 32 (fun j : Fin 22 => R09p06_digit j 16)=R09p06_columnCode 16 := by decide +kernel

private theorem R09p06_column_17 : reversePack 32 (fun j : Fin 22 => R09p06_digit j 17)=R09p06_columnCode 17 := by decide +kernel

private theorem R09p06_column_18 : reversePack 32 (fun j : Fin 22 => R09p06_digit j 18)=R09p06_columnCode 18 := by decide +kernel

private theorem R09p06_column_19 : reversePack 32 (fun j : Fin 22 => R09p06_digit j 19)=R09p06_columnCode 19 := by decide +kernel

private theorem R09p06_column_20 : reversePack 32 (fun j : Fin 22 => R09p06_digit j 20)=R09p06_columnCode 20 := by decide +kernel

private theorem R09p06_column_21 : reversePack 32 (fun j : Fin 22 => R09p06_digit j 21)=R09p06_columnCode 21 := by decide +kernel

theorem R09p06_column_binding : ∀ i : Fin 22,reversePack 32 (fun j : Fin 22 => R09p06_digit j i)=R09p06_columnCode i := by
  intro i
  fin_cases i
  · exact R09p06_column_00
  · exact R09p06_column_01
  · exact R09p06_column_02
  · exact R09p06_column_03
  · exact R09p06_column_04
  · exact R09p06_column_05
  · exact R09p06_column_06
  · exact R09p06_column_07
  · exact R09p06_column_08
  · exact R09p06_column_09
  · exact R09p06_column_10
  · exact R09p06_column_11
  · exact R09p06_column_12
  · exact R09p06_column_13
  · exact R09p06_column_14
  · exact R09p06_column_15
  · exact R09p06_column_16
  · exact R09p06_column_17
  · exact R09p06_column_18
  · exact R09p06_column_19
  · exact R09p06_column_20
  · exact R09p06_column_21

def R09p06_data : PackedData 22 2 32 where
  raw := R09p06_digit
  digit_lt := R09p06_bound
  rowCode := R09p06_rowCode
  columnCode := R09p06_columnCode
  row_binding := R09p06_row_binding
  column_binding := R09p06_column_binding

def R09p07_lowColumnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1153743
  | 1 => 565305
  | 2 => 3783371
  | 3 => 2486670
  | 4 => 456174
  | 5 => 905386
  | 6 => 1082139
  | 7 => 3920325
  | 8 => 726181
  | 9 => 2672644
  | 10 => 54984
  | 11 => 3706159
  | 12 => 17671
  | 13 => 3993999
  | 14 => 3709327
  | 15 => 1698628
  | 16 => 4113972
  | 17 => 3852728
  | 18 => 4140092
  | 19 => 366514
  | 20 => 1549171
  | 21 => 3307952
  | _ => 0

def R09p07_rowCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1267650601446903461798104532001
  | 1 => 1307264682704035629461039776769
  | 2 => 1239187962710953345936293889
  | 3 => 1276626883035311971354313761
  | 4 => 41873361723380035081226715922464
  | 5 => 41873361723380071111122207375392
  | 6 => 1267650638007162390388132545537
  | 7 => 40604471975404186920723508397057
  | 8 => 41872122613412536008480620838912
  | 9 => 1307265928190114173780792181761
  | 10 => 40853230223427241001891135488
  | 11 => 40566095871928413443958956360705
  | 12 => 40604433289777959252589917799425
  | 13 => 41833707785386680980770686796832
  | 14 => 40564859139672367564385128841216
  | 15 => 1307304615033863014794998613025
  | 16 => 1308502659303578814659440968705
  | 17 => 41833747642122902913562742620160
  | 18 => 1308503830487360053345002749952
  | 19 => 1277873587785699974952518688
  | 20 => 41833747681119355913083314766849
  | 21 => 40566097043112194683812748231680
  | _ => 0

def R09p07_columnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 41873321867788665364727442964512
  | 1 => 40566097041894673512032752370688
  | 2 => 41833707786531533197030182618145
  | 3 => 1308502622742132095752555495425
  | 4 => 1308503869446919602135878369280
  | 5 => 1268889750373926052338027496448
  | 6 => 41833746433235129707452795191328
  | 7 => 40604433327556890023733106836513
  | 8 => 40604434498666920316019286213632
  | 9 => 39614081257133294732112299009
  | 10 => 1237978999997849470903517184
  | 11 => 41873323037790738055937470235681
  | 12 => 41872083888825631935166775558144
  | 13 => 41873321830045472943647024514081
  | 14 => 41873321830045474068413059957793
  | 15 => 39614119074111568440845141024
  | 16 => 39653975810368401896597652513
  | 17 => 1277835808818897837836207137
  | 18 => 40891915848501987630908474401
  | 19 => 1267690495998950778611404144640
  | 20 => 41832509739900595805863778746400
  | 21 => 39895769533553845747056673
  | _ => 0

def R09p07_digit (i j : Fin 22) : ℕ := packedDigit 1 (R09p07_lowColumnCode j) i.val

private theorem R09p07_bound_00 : ∀ j : Fin 22,R09p07_digit 0 j<2 := by decide +kernel

private theorem R09p07_bound_01 : ∀ j : Fin 22,R09p07_digit 1 j<2 := by decide +kernel

private theorem R09p07_bound_02 : ∀ j : Fin 22,R09p07_digit 2 j<2 := by decide +kernel

private theorem R09p07_bound_03 : ∀ j : Fin 22,R09p07_digit 3 j<2 := by decide +kernel

private theorem R09p07_bound_04 : ∀ j : Fin 22,R09p07_digit 4 j<2 := by decide +kernel

private theorem R09p07_bound_05 : ∀ j : Fin 22,R09p07_digit 5 j<2 := by decide +kernel

private theorem R09p07_bound_06 : ∀ j : Fin 22,R09p07_digit 6 j<2 := by decide +kernel

private theorem R09p07_bound_07 : ∀ j : Fin 22,R09p07_digit 7 j<2 := by decide +kernel

private theorem R09p07_bound_08 : ∀ j : Fin 22,R09p07_digit 8 j<2 := by decide +kernel

private theorem R09p07_bound_09 : ∀ j : Fin 22,R09p07_digit 9 j<2 := by decide +kernel

private theorem R09p07_bound_10 : ∀ j : Fin 22,R09p07_digit 10 j<2 := by decide +kernel

private theorem R09p07_bound_11 : ∀ j : Fin 22,R09p07_digit 11 j<2 := by decide +kernel

private theorem R09p07_bound_12 : ∀ j : Fin 22,R09p07_digit 12 j<2 := by decide +kernel

private theorem R09p07_bound_13 : ∀ j : Fin 22,R09p07_digit 13 j<2 := by decide +kernel

private theorem R09p07_bound_14 : ∀ j : Fin 22,R09p07_digit 14 j<2 := by decide +kernel

private theorem R09p07_bound_15 : ∀ j : Fin 22,R09p07_digit 15 j<2 := by decide +kernel

private theorem R09p07_bound_16 : ∀ j : Fin 22,R09p07_digit 16 j<2 := by decide +kernel

private theorem R09p07_bound_17 : ∀ j : Fin 22,R09p07_digit 17 j<2 := by decide +kernel

private theorem R09p07_bound_18 : ∀ j : Fin 22,R09p07_digit 18 j<2 := by decide +kernel

private theorem R09p07_bound_19 : ∀ j : Fin 22,R09p07_digit 19 j<2 := by decide +kernel

private theorem R09p07_bound_20 : ∀ j : Fin 22,R09p07_digit 20 j<2 := by decide +kernel

private theorem R09p07_bound_21 : ∀ j : Fin 22,R09p07_digit 21 j<2 := by decide +kernel

theorem R09p07_bound : ∀ i j : Fin 22,R09p07_digit i j<2 := by
  intro i j
  fin_cases i
  · exact R09p07_bound_00 j
  · exact R09p07_bound_01 j
  · exact R09p07_bound_02 j
  · exact R09p07_bound_03 j
  · exact R09p07_bound_04 j
  · exact R09p07_bound_05 j
  · exact R09p07_bound_06 j
  · exact R09p07_bound_07 j
  · exact R09p07_bound_08 j
  · exact R09p07_bound_09 j
  · exact R09p07_bound_10 j
  · exact R09p07_bound_11 j
  · exact R09p07_bound_12 j
  · exact R09p07_bound_13 j
  · exact R09p07_bound_14 j
  · exact R09p07_bound_15 j
  · exact R09p07_bound_16 j
  · exact R09p07_bound_17 j
  · exact R09p07_bound_18 j
  · exact R09p07_bound_19 j
  · exact R09p07_bound_20 j
  · exact R09p07_bound_21 j

private theorem R09p07_row_00 : pack 32 (R09p07_digit 0)=R09p07_rowCode 0 := by decide +kernel

private theorem R09p07_row_01 : pack 32 (R09p07_digit 1)=R09p07_rowCode 1 := by decide +kernel

private theorem R09p07_row_02 : pack 32 (R09p07_digit 2)=R09p07_rowCode 2 := by decide +kernel

private theorem R09p07_row_03 : pack 32 (R09p07_digit 3)=R09p07_rowCode 3 := by decide +kernel

private theorem R09p07_row_04 : pack 32 (R09p07_digit 4)=R09p07_rowCode 4 := by decide +kernel

private theorem R09p07_row_05 : pack 32 (R09p07_digit 5)=R09p07_rowCode 5 := by decide +kernel

private theorem R09p07_row_06 : pack 32 (R09p07_digit 6)=R09p07_rowCode 6 := by decide +kernel

private theorem R09p07_row_07 : pack 32 (R09p07_digit 7)=R09p07_rowCode 7 := by decide +kernel

private theorem R09p07_row_08 : pack 32 (R09p07_digit 8)=R09p07_rowCode 8 := by decide +kernel

private theorem R09p07_row_09 : pack 32 (R09p07_digit 9)=R09p07_rowCode 9 := by decide +kernel

private theorem R09p07_row_10 : pack 32 (R09p07_digit 10)=R09p07_rowCode 10 := by decide +kernel

private theorem R09p07_row_11 : pack 32 (R09p07_digit 11)=R09p07_rowCode 11 := by decide +kernel

private theorem R09p07_row_12 : pack 32 (R09p07_digit 12)=R09p07_rowCode 12 := by decide +kernel

private theorem R09p07_row_13 : pack 32 (R09p07_digit 13)=R09p07_rowCode 13 := by decide +kernel

private theorem R09p07_row_14 : pack 32 (R09p07_digit 14)=R09p07_rowCode 14 := by decide +kernel

private theorem R09p07_row_15 : pack 32 (R09p07_digit 15)=R09p07_rowCode 15 := by decide +kernel

private theorem R09p07_row_16 : pack 32 (R09p07_digit 16)=R09p07_rowCode 16 := by decide +kernel

private theorem R09p07_row_17 : pack 32 (R09p07_digit 17)=R09p07_rowCode 17 := by decide +kernel

private theorem R09p07_row_18 : pack 32 (R09p07_digit 18)=R09p07_rowCode 18 := by decide +kernel

private theorem R09p07_row_19 : pack 32 (R09p07_digit 19)=R09p07_rowCode 19 := by decide +kernel

private theorem R09p07_row_20 : pack 32 (R09p07_digit 20)=R09p07_rowCode 20 := by decide +kernel

private theorem R09p07_row_21 : pack 32 (R09p07_digit 21)=R09p07_rowCode 21 := by decide +kernel

theorem R09p07_row_binding : ∀ i : Fin 22,pack 32 (R09p07_digit i)=R09p07_rowCode i := by
  intro i
  fin_cases i
  · exact R09p07_row_00
  · exact R09p07_row_01
  · exact R09p07_row_02
  · exact R09p07_row_03
  · exact R09p07_row_04
  · exact R09p07_row_05
  · exact R09p07_row_06
  · exact R09p07_row_07
  · exact R09p07_row_08
  · exact R09p07_row_09
  · exact R09p07_row_10
  · exact R09p07_row_11
  · exact R09p07_row_12
  · exact R09p07_row_13
  · exact R09p07_row_14
  · exact R09p07_row_15
  · exact R09p07_row_16
  · exact R09p07_row_17
  · exact R09p07_row_18
  · exact R09p07_row_19
  · exact R09p07_row_20
  · exact R09p07_row_21

private theorem R09p07_column_00 : reversePack 32 (fun j : Fin 22 => R09p07_digit j 0)=R09p07_columnCode 0 := by decide +kernel

private theorem R09p07_column_01 : reversePack 32 (fun j : Fin 22 => R09p07_digit j 1)=R09p07_columnCode 1 := by decide +kernel

private theorem R09p07_column_02 : reversePack 32 (fun j : Fin 22 => R09p07_digit j 2)=R09p07_columnCode 2 := by decide +kernel

private theorem R09p07_column_03 : reversePack 32 (fun j : Fin 22 => R09p07_digit j 3)=R09p07_columnCode 3 := by decide +kernel

private theorem R09p07_column_04 : reversePack 32 (fun j : Fin 22 => R09p07_digit j 4)=R09p07_columnCode 4 := by decide +kernel

private theorem R09p07_column_05 : reversePack 32 (fun j : Fin 22 => R09p07_digit j 5)=R09p07_columnCode 5 := by decide +kernel

private theorem R09p07_column_06 : reversePack 32 (fun j : Fin 22 => R09p07_digit j 6)=R09p07_columnCode 6 := by decide +kernel

private theorem R09p07_column_07 : reversePack 32 (fun j : Fin 22 => R09p07_digit j 7)=R09p07_columnCode 7 := by decide +kernel

private theorem R09p07_column_08 : reversePack 32 (fun j : Fin 22 => R09p07_digit j 8)=R09p07_columnCode 8 := by decide +kernel

private theorem R09p07_column_09 : reversePack 32 (fun j : Fin 22 => R09p07_digit j 9)=R09p07_columnCode 9 := by decide +kernel

private theorem R09p07_column_10 : reversePack 32 (fun j : Fin 22 => R09p07_digit j 10)=R09p07_columnCode 10 := by decide +kernel

private theorem R09p07_column_11 : reversePack 32 (fun j : Fin 22 => R09p07_digit j 11)=R09p07_columnCode 11 := by decide +kernel

private theorem R09p07_column_12 : reversePack 32 (fun j : Fin 22 => R09p07_digit j 12)=R09p07_columnCode 12 := by decide +kernel

private theorem R09p07_column_13 : reversePack 32 (fun j : Fin 22 => R09p07_digit j 13)=R09p07_columnCode 13 := by decide +kernel

private theorem R09p07_column_14 : reversePack 32 (fun j : Fin 22 => R09p07_digit j 14)=R09p07_columnCode 14 := by decide +kernel

private theorem R09p07_column_15 : reversePack 32 (fun j : Fin 22 => R09p07_digit j 15)=R09p07_columnCode 15 := by decide +kernel

private theorem R09p07_column_16 : reversePack 32 (fun j : Fin 22 => R09p07_digit j 16)=R09p07_columnCode 16 := by decide +kernel

private theorem R09p07_column_17 : reversePack 32 (fun j : Fin 22 => R09p07_digit j 17)=R09p07_columnCode 17 := by decide +kernel

private theorem R09p07_column_18 : reversePack 32 (fun j : Fin 22 => R09p07_digit j 18)=R09p07_columnCode 18 := by decide +kernel

private theorem R09p07_column_19 : reversePack 32 (fun j : Fin 22 => R09p07_digit j 19)=R09p07_columnCode 19 := by decide +kernel

private theorem R09p07_column_20 : reversePack 32 (fun j : Fin 22 => R09p07_digit j 20)=R09p07_columnCode 20 := by decide +kernel

private theorem R09p07_column_21 : reversePack 32 (fun j : Fin 22 => R09p07_digit j 21)=R09p07_columnCode 21 := by decide +kernel

theorem R09p07_column_binding : ∀ i : Fin 22,reversePack 32 (fun j : Fin 22 => R09p07_digit j i)=R09p07_columnCode i := by
  intro i
  fin_cases i
  · exact R09p07_column_00
  · exact R09p07_column_01
  · exact R09p07_column_02
  · exact R09p07_column_03
  · exact R09p07_column_04
  · exact R09p07_column_05
  · exact R09p07_column_06
  · exact R09p07_column_07
  · exact R09p07_column_08
  · exact R09p07_column_09
  · exact R09p07_column_10
  · exact R09p07_column_11
  · exact R09p07_column_12
  · exact R09p07_column_13
  · exact R09p07_column_14
  · exact R09p07_column_15
  · exact R09p07_column_16
  · exact R09p07_column_17
  · exact R09p07_column_18
  · exact R09p07_column_19
  · exact R09p07_column_20
  · exact R09p07_column_21

def R09p07_data : PackedData 22 2 32 where
  raw := R09p07_digit
  digit_lt := R09p07_bound
  rowCode := R09p07_rowCode
  columnCode := R09p07_columnCode
  row_binding := R09p07_row_binding
  column_binding := R09p07_column_binding

def R09p08_lowColumnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 2787330
  | 1 => 3388148
  | 2 => 3298045
  | 3 => 3021240
  | 4 => 3073789
  | 5 => 4035232
  | 6 => 3706888
  | 7 => 3920325
  | 8 => 3888815
  | 9 => 2672644
  | 10 => 54984
  | 11 => 3706159
  | 12 => 17671
  | 13 => 2371787
  | 14 => 3709327
  | 15 => 29238
  | 16 => 2492272
  | 17 => 3852728
  | 18 => 4140092
  | 19 => 1838784
  | 20 => 1549171
  | 21 => 3307952
  | _ => 0

def R09p08_rowCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1267650601446903461797031838720
  | 1 => 1267650639225835324719832760321
  | 2 => 1237978999997850569342452768
  | 3 => 1276626883035313070832387072
  | 4 => 41833747679901834775386032997408
  | 5 => 41833747679901870805282597143584
  | 6 => 1307265890448075799004336620576
  | 7 => 40604471975404186920723508397088
  | 8 => 41832509703265398103207367966720
  | 9 => 1307265928190114174879264670752
  | 10 => 40853230223427241001891135488
  | 11 => 40605709915406613749798566658049
  | 12 => 40564819246299758946751380227104
  | 13 => 41833707785386680980770686763040
  | 14 => 40564857930709654462708013073408
  | 15 => 1267689287035085880264471085089
  | 16 => 1268888540267514782905507250208
  | 17 => 41833747642122902913562742653985
  | 18 => 1308503830487360053345002749952
  | 19 => 40890708103272903039043796993
  | 20 => 41873360515634843117245876405280
  | 21 => 40566097043112194684913368204321
  | _ => 0

def R09p08_columnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1267650600228230527397684839425
  | 1 => 39654014769855893023709200417
  | 2 => 40605711162112482120126851711009
  | 3 => 1277835808818932986774848513
  | 4 => 40605711162112518114840083989505
  | 5 => 1210107564192036672275489
  | 6 => 1237940039285415460344955937
  | 7 => 40604433327556890023733106836513
  | 8 => 41873323038935588019329855128609
  | 9 => 39614081257133294732112299009
  | 10 => 1237978999997849470903517184
  | 11 => 41873323037790738055937470235681
  | 12 => 41872083888825631935166775558144
  | 13 => 41833707786530379149624561664001
  | 14 => 41873321830045474068413059957793
  | 15 => 1307304576038561810879090786304
  | 16 => 39932369061584168973008897
  | 17 => 1277835808818897837836207137
  | 18 => 40891915848501987630908474401
  | 19 => 38960713559876105700384
  | 20 => 41832509739900595805863778746400
  | 21 => 39895769533553845747056673
  | _ => 0

def R09p08_digit (i j : Fin 22) : ℕ := packedDigit 1 (R09p08_lowColumnCode j) i.val

private theorem R09p08_bound_00 : ∀ j : Fin 22,R09p08_digit 0 j<2 := by decide +kernel

private theorem R09p08_bound_01 : ∀ j : Fin 22,R09p08_digit 1 j<2 := by decide +kernel

private theorem R09p08_bound_02 : ∀ j : Fin 22,R09p08_digit 2 j<2 := by decide +kernel

private theorem R09p08_bound_03 : ∀ j : Fin 22,R09p08_digit 3 j<2 := by decide +kernel

private theorem R09p08_bound_04 : ∀ j : Fin 22,R09p08_digit 4 j<2 := by decide +kernel

private theorem R09p08_bound_05 : ∀ j : Fin 22,R09p08_digit 5 j<2 := by decide +kernel

private theorem R09p08_bound_06 : ∀ j : Fin 22,R09p08_digit 6 j<2 := by decide +kernel

private theorem R09p08_bound_07 : ∀ j : Fin 22,R09p08_digit 7 j<2 := by decide +kernel

private theorem R09p08_bound_08 : ∀ j : Fin 22,R09p08_digit 8 j<2 := by decide +kernel

private theorem R09p08_bound_09 : ∀ j : Fin 22,R09p08_digit 9 j<2 := by decide +kernel

private theorem R09p08_bound_10 : ∀ j : Fin 22,R09p08_digit 10 j<2 := by decide +kernel

private theorem R09p08_bound_11 : ∀ j : Fin 22,R09p08_digit 11 j<2 := by decide +kernel

private theorem R09p08_bound_12 : ∀ j : Fin 22,R09p08_digit 12 j<2 := by decide +kernel

private theorem R09p08_bound_13 : ∀ j : Fin 22,R09p08_digit 13 j<2 := by decide +kernel

private theorem R09p08_bound_14 : ∀ j : Fin 22,R09p08_digit 14 j<2 := by decide +kernel

private theorem R09p08_bound_15 : ∀ j : Fin 22,R09p08_digit 15 j<2 := by decide +kernel

private theorem R09p08_bound_16 : ∀ j : Fin 22,R09p08_digit 16 j<2 := by decide +kernel

private theorem R09p08_bound_17 : ∀ j : Fin 22,R09p08_digit 17 j<2 := by decide +kernel

private theorem R09p08_bound_18 : ∀ j : Fin 22,R09p08_digit 18 j<2 := by decide +kernel

private theorem R09p08_bound_19 : ∀ j : Fin 22,R09p08_digit 19 j<2 := by decide +kernel

private theorem R09p08_bound_20 : ∀ j : Fin 22,R09p08_digit 20 j<2 := by decide +kernel

private theorem R09p08_bound_21 : ∀ j : Fin 22,R09p08_digit 21 j<2 := by decide +kernel

theorem R09p08_bound : ∀ i j : Fin 22,R09p08_digit i j<2 := by
  intro i j
  fin_cases i
  · exact R09p08_bound_00 j
  · exact R09p08_bound_01 j
  · exact R09p08_bound_02 j
  · exact R09p08_bound_03 j
  · exact R09p08_bound_04 j
  · exact R09p08_bound_05 j
  · exact R09p08_bound_06 j
  · exact R09p08_bound_07 j
  · exact R09p08_bound_08 j
  · exact R09p08_bound_09 j
  · exact R09p08_bound_10 j
  · exact R09p08_bound_11 j
  · exact R09p08_bound_12 j
  · exact R09p08_bound_13 j
  · exact R09p08_bound_14 j
  · exact R09p08_bound_15 j
  · exact R09p08_bound_16 j
  · exact R09p08_bound_17 j
  · exact R09p08_bound_18 j
  · exact R09p08_bound_19 j
  · exact R09p08_bound_20 j
  · exact R09p08_bound_21 j

private theorem R09p08_row_00 : pack 32 (R09p08_digit 0)=R09p08_rowCode 0 := by decide +kernel

private theorem R09p08_row_01 : pack 32 (R09p08_digit 1)=R09p08_rowCode 1 := by decide +kernel

private theorem R09p08_row_02 : pack 32 (R09p08_digit 2)=R09p08_rowCode 2 := by decide +kernel

private theorem R09p08_row_03 : pack 32 (R09p08_digit 3)=R09p08_rowCode 3 := by decide +kernel

private theorem R09p08_row_04 : pack 32 (R09p08_digit 4)=R09p08_rowCode 4 := by decide +kernel

private theorem R09p08_row_05 : pack 32 (R09p08_digit 5)=R09p08_rowCode 5 := by decide +kernel

private theorem R09p08_row_06 : pack 32 (R09p08_digit 6)=R09p08_rowCode 6 := by decide +kernel

private theorem R09p08_row_07 : pack 32 (R09p08_digit 7)=R09p08_rowCode 7 := by decide +kernel

private theorem R09p08_row_08 : pack 32 (R09p08_digit 8)=R09p08_rowCode 8 := by decide +kernel

private theorem R09p08_row_09 : pack 32 (R09p08_digit 9)=R09p08_rowCode 9 := by decide +kernel

private theorem R09p08_row_10 : pack 32 (R09p08_digit 10)=R09p08_rowCode 10 := by decide +kernel

private theorem R09p08_row_11 : pack 32 (R09p08_digit 11)=R09p08_rowCode 11 := by decide +kernel

private theorem R09p08_row_12 : pack 32 (R09p08_digit 12)=R09p08_rowCode 12 := by decide +kernel

private theorem R09p08_row_13 : pack 32 (R09p08_digit 13)=R09p08_rowCode 13 := by decide +kernel

private theorem R09p08_row_14 : pack 32 (R09p08_digit 14)=R09p08_rowCode 14 := by decide +kernel

private theorem R09p08_row_15 : pack 32 (R09p08_digit 15)=R09p08_rowCode 15 := by decide +kernel

private theorem R09p08_row_16 : pack 32 (R09p08_digit 16)=R09p08_rowCode 16 := by decide +kernel

private theorem R09p08_row_17 : pack 32 (R09p08_digit 17)=R09p08_rowCode 17 := by decide +kernel

private theorem R09p08_row_18 : pack 32 (R09p08_digit 18)=R09p08_rowCode 18 := by decide +kernel

private theorem R09p08_row_19 : pack 32 (R09p08_digit 19)=R09p08_rowCode 19 := by decide +kernel

private theorem R09p08_row_20 : pack 32 (R09p08_digit 20)=R09p08_rowCode 20 := by decide +kernel

private theorem R09p08_row_21 : pack 32 (R09p08_digit 21)=R09p08_rowCode 21 := by decide +kernel

theorem R09p08_row_binding : ∀ i : Fin 22,pack 32 (R09p08_digit i)=R09p08_rowCode i := by
  intro i
  fin_cases i
  · exact R09p08_row_00
  · exact R09p08_row_01
  · exact R09p08_row_02
  · exact R09p08_row_03
  · exact R09p08_row_04
  · exact R09p08_row_05
  · exact R09p08_row_06
  · exact R09p08_row_07
  · exact R09p08_row_08
  · exact R09p08_row_09
  · exact R09p08_row_10
  · exact R09p08_row_11
  · exact R09p08_row_12
  · exact R09p08_row_13
  · exact R09p08_row_14
  · exact R09p08_row_15
  · exact R09p08_row_16
  · exact R09p08_row_17
  · exact R09p08_row_18
  · exact R09p08_row_19
  · exact R09p08_row_20
  · exact R09p08_row_21

private theorem R09p08_column_00 : reversePack 32 (fun j : Fin 22 => R09p08_digit j 0)=R09p08_columnCode 0 := by decide +kernel

private theorem R09p08_column_01 : reversePack 32 (fun j : Fin 22 => R09p08_digit j 1)=R09p08_columnCode 1 := by decide +kernel

private theorem R09p08_column_02 : reversePack 32 (fun j : Fin 22 => R09p08_digit j 2)=R09p08_columnCode 2 := by decide +kernel

private theorem R09p08_column_03 : reversePack 32 (fun j : Fin 22 => R09p08_digit j 3)=R09p08_columnCode 3 := by decide +kernel

private theorem R09p08_column_04 : reversePack 32 (fun j : Fin 22 => R09p08_digit j 4)=R09p08_columnCode 4 := by decide +kernel

private theorem R09p08_column_05 : reversePack 32 (fun j : Fin 22 => R09p08_digit j 5)=R09p08_columnCode 5 := by decide +kernel

private theorem R09p08_column_06 : reversePack 32 (fun j : Fin 22 => R09p08_digit j 6)=R09p08_columnCode 6 := by decide +kernel

private theorem R09p08_column_07 : reversePack 32 (fun j : Fin 22 => R09p08_digit j 7)=R09p08_columnCode 7 := by decide +kernel

private theorem R09p08_column_08 : reversePack 32 (fun j : Fin 22 => R09p08_digit j 8)=R09p08_columnCode 8 := by decide +kernel

private theorem R09p08_column_09 : reversePack 32 (fun j : Fin 22 => R09p08_digit j 9)=R09p08_columnCode 9 := by decide +kernel

private theorem R09p08_column_10 : reversePack 32 (fun j : Fin 22 => R09p08_digit j 10)=R09p08_columnCode 10 := by decide +kernel

private theorem R09p08_column_11 : reversePack 32 (fun j : Fin 22 => R09p08_digit j 11)=R09p08_columnCode 11 := by decide +kernel

private theorem R09p08_column_12 : reversePack 32 (fun j : Fin 22 => R09p08_digit j 12)=R09p08_columnCode 12 := by decide +kernel

private theorem R09p08_column_13 : reversePack 32 (fun j : Fin 22 => R09p08_digit j 13)=R09p08_columnCode 13 := by decide +kernel

private theorem R09p08_column_14 : reversePack 32 (fun j : Fin 22 => R09p08_digit j 14)=R09p08_columnCode 14 := by decide +kernel

private theorem R09p08_column_15 : reversePack 32 (fun j : Fin 22 => R09p08_digit j 15)=R09p08_columnCode 15 := by decide +kernel

private theorem R09p08_column_16 : reversePack 32 (fun j : Fin 22 => R09p08_digit j 16)=R09p08_columnCode 16 := by decide +kernel

private theorem R09p08_column_17 : reversePack 32 (fun j : Fin 22 => R09p08_digit j 17)=R09p08_columnCode 17 := by decide +kernel

private theorem R09p08_column_18 : reversePack 32 (fun j : Fin 22 => R09p08_digit j 18)=R09p08_columnCode 18 := by decide +kernel

private theorem R09p08_column_19 : reversePack 32 (fun j : Fin 22 => R09p08_digit j 19)=R09p08_columnCode 19 := by decide +kernel

private theorem R09p08_column_20 : reversePack 32 (fun j : Fin 22 => R09p08_digit j 20)=R09p08_columnCode 20 := by decide +kernel

private theorem R09p08_column_21 : reversePack 32 (fun j : Fin 22 => R09p08_digit j 21)=R09p08_columnCode 21 := by decide +kernel

theorem R09p08_column_binding : ∀ i : Fin 22,reversePack 32 (fun j : Fin 22 => R09p08_digit j i)=R09p08_columnCode i := by
  intro i
  fin_cases i
  · exact R09p08_column_00
  · exact R09p08_column_01
  · exact R09p08_column_02
  · exact R09p08_column_03
  · exact R09p08_column_04
  · exact R09p08_column_05
  · exact R09p08_column_06
  · exact R09p08_column_07
  · exact R09p08_column_08
  · exact R09p08_column_09
  · exact R09p08_column_10
  · exact R09p08_column_11
  · exact R09p08_column_12
  · exact R09p08_column_13
  · exact R09p08_column_14
  · exact R09p08_column_15
  · exact R09p08_column_16
  · exact R09p08_column_17
  · exact R09p08_column_18
  · exact R09p08_column_19
  · exact R09p08_column_20
  · exact R09p08_column_21

def R09p08_data : PackedData 22 2 32 where
  raw := R09p08_digit
  digit_lt := R09p08_bound
  rowCode := R09p08_rowCode
  columnCode := R09p08_columnCode
  row_binding := R09p08_row_binding
  column_binding := R09p08_column_binding

def R09p09_lowColumnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 632949
  | 1 => 117572
  | 2 => 1086083
  | 3 => 2875586
  | 4 => 2618440
  | 5 => 363340
  | 6 => 2541432
  | 7 => 3883080
  | 8 => 1137484
  | 9 => 1441876
  | 10 => 3153920
  | 11 => 3539747
  | 12 => 219888
  | 13 => 1337344
  | 14 => 3528867
  | 15 => 2873331
  | 16 => 3307952
  | 17 => 3182083
  | 18 => 1817459
  | 19 => 3045232
  | 20 => 552960
  | 21 => 1549171
  | _ => 0

def R09p09_rowCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 40566095871928413408774584271873
  | 1 => 40566095871928413408774584304640
  | 2 => 36283917271073
  | 3 => 1134979710976
  | 4 => 40605672475305662831242562764801
  | 5 => 40605672476486290445572620943361
  | 6 => 40605671266379843217747294060577
  | 7 => 1247886496019808354599936
  | 8 => 40605672475304545904450147975200
  | 9 => 40605709952006106879459170714656
  | 10 => 39652804662291699888599072768
  | 11 => 1277835809970694506646863905
  | 12 => 1308503869411142971476241548288
  | 13 => 41873323037790702027139378610177
  | 14 => 1307265929408751079384195039264
  | 15 => 40566095871928377379978673685537
  | 16 => 40566057186303302634482487558177
  | 17 => 40605672475305698860073942548480
  | 18 => 40604433289777994189538604351488
  | 19 => 1308502659303578813559895785473
  | 20 => 40566097043112195810812166669312
  | 21 => 39654014768740089966470660096
  | _ => 0

def R09p09_columnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 40604473220891453289411727328256
  | 1 => 39614119074111567341333512192
  | 2 => 41832469808713314826798669758496
  | 3 => 1267650639187752886306255930369
  | 4 => 1237977818253308348431630337
  | 5 => 40852059113396947581872930816
  | 6 => 1277872408346964479305613313
  | 7 => 1237977818217243266455176225
  | 8 => 40852059113396982799530983456
  | 9 => 39652804662291699887525363744
  | 10 => 1099511627809
  | 11 => 41832471016495436273672407515169
  | 12 => 39933512724849060618436608
  | 13 => 1127033778241568
  | 14 => 41832471017637982645857537785889
  | 15 => 41832509741081223489497429181441
  | 16 => 39895769533553845747056673
  | 17 => 41832469807532760325593812172833
  | 18 => 41832509739900596966948057646112
  | 19 => 39932369061620487216464897
  | 20 => 36318243456000
  | 21 => 41832509739900595805863778746400
  | _ => 0

def R09p09_digit (i j : Fin 22) : ℕ := packedDigit 1 (R09p09_lowColumnCode j) i.val

private theorem R09p09_bound_00 : ∀ j : Fin 22,R09p09_digit 0 j<2 := by decide +kernel

private theorem R09p09_bound_01 : ∀ j : Fin 22,R09p09_digit 1 j<2 := by decide +kernel

private theorem R09p09_bound_02 : ∀ j : Fin 22,R09p09_digit 2 j<2 := by decide +kernel

private theorem R09p09_bound_03 : ∀ j : Fin 22,R09p09_digit 3 j<2 := by decide +kernel

private theorem R09p09_bound_04 : ∀ j : Fin 22,R09p09_digit 4 j<2 := by decide +kernel

private theorem R09p09_bound_05 : ∀ j : Fin 22,R09p09_digit 5 j<2 := by decide +kernel

private theorem R09p09_bound_06 : ∀ j : Fin 22,R09p09_digit 6 j<2 := by decide +kernel

private theorem R09p09_bound_07 : ∀ j : Fin 22,R09p09_digit 7 j<2 := by decide +kernel

private theorem R09p09_bound_08 : ∀ j : Fin 22,R09p09_digit 8 j<2 := by decide +kernel

private theorem R09p09_bound_09 : ∀ j : Fin 22,R09p09_digit 9 j<2 := by decide +kernel

private theorem R09p09_bound_10 : ∀ j : Fin 22,R09p09_digit 10 j<2 := by decide +kernel

private theorem R09p09_bound_11 : ∀ j : Fin 22,R09p09_digit 11 j<2 := by decide +kernel

private theorem R09p09_bound_12 : ∀ j : Fin 22,R09p09_digit 12 j<2 := by decide +kernel

private theorem R09p09_bound_13 : ∀ j : Fin 22,R09p09_digit 13 j<2 := by decide +kernel

private theorem R09p09_bound_14 : ∀ j : Fin 22,R09p09_digit 14 j<2 := by decide +kernel

private theorem R09p09_bound_15 : ∀ j : Fin 22,R09p09_digit 15 j<2 := by decide +kernel

private theorem R09p09_bound_16 : ∀ j : Fin 22,R09p09_digit 16 j<2 := by decide +kernel

private theorem R09p09_bound_17 : ∀ j : Fin 22,R09p09_digit 17 j<2 := by decide +kernel

private theorem R09p09_bound_18 : ∀ j : Fin 22,R09p09_digit 18 j<2 := by decide +kernel

private theorem R09p09_bound_19 : ∀ j : Fin 22,R09p09_digit 19 j<2 := by decide +kernel

private theorem R09p09_bound_20 : ∀ j : Fin 22,R09p09_digit 20 j<2 := by decide +kernel

private theorem R09p09_bound_21 : ∀ j : Fin 22,R09p09_digit 21 j<2 := by decide +kernel

theorem R09p09_bound : ∀ i j : Fin 22,R09p09_digit i j<2 := by
  intro i j
  fin_cases i
  · exact R09p09_bound_00 j
  · exact R09p09_bound_01 j
  · exact R09p09_bound_02 j
  · exact R09p09_bound_03 j
  · exact R09p09_bound_04 j
  · exact R09p09_bound_05 j
  · exact R09p09_bound_06 j
  · exact R09p09_bound_07 j
  · exact R09p09_bound_08 j
  · exact R09p09_bound_09 j
  · exact R09p09_bound_10 j
  · exact R09p09_bound_11 j
  · exact R09p09_bound_12 j
  · exact R09p09_bound_13 j
  · exact R09p09_bound_14 j
  · exact R09p09_bound_15 j
  · exact R09p09_bound_16 j
  · exact R09p09_bound_17 j
  · exact R09p09_bound_18 j
  · exact R09p09_bound_19 j
  · exact R09p09_bound_20 j
  · exact R09p09_bound_21 j

private theorem R09p09_row_00 : pack 32 (R09p09_digit 0)=R09p09_rowCode 0 := by decide +kernel

private theorem R09p09_row_01 : pack 32 (R09p09_digit 1)=R09p09_rowCode 1 := by decide +kernel

private theorem R09p09_row_02 : pack 32 (R09p09_digit 2)=R09p09_rowCode 2 := by decide +kernel

private theorem R09p09_row_03 : pack 32 (R09p09_digit 3)=R09p09_rowCode 3 := by decide +kernel

private theorem R09p09_row_04 : pack 32 (R09p09_digit 4)=R09p09_rowCode 4 := by decide +kernel

private theorem R09p09_row_05 : pack 32 (R09p09_digit 5)=R09p09_rowCode 5 := by decide +kernel

private theorem R09p09_row_06 : pack 32 (R09p09_digit 6)=R09p09_rowCode 6 := by decide +kernel

private theorem R09p09_row_07 : pack 32 (R09p09_digit 7)=R09p09_rowCode 7 := by decide +kernel

private theorem R09p09_row_08 : pack 32 (R09p09_digit 8)=R09p09_rowCode 8 := by decide +kernel

private theorem R09p09_row_09 : pack 32 (R09p09_digit 9)=R09p09_rowCode 9 := by decide +kernel

private theorem R09p09_row_10 : pack 32 (R09p09_digit 10)=R09p09_rowCode 10 := by decide +kernel

private theorem R09p09_row_11 : pack 32 (R09p09_digit 11)=R09p09_rowCode 11 := by decide +kernel

private theorem R09p09_row_12 : pack 32 (R09p09_digit 12)=R09p09_rowCode 12 := by decide +kernel

private theorem R09p09_row_13 : pack 32 (R09p09_digit 13)=R09p09_rowCode 13 := by decide +kernel

private theorem R09p09_row_14 : pack 32 (R09p09_digit 14)=R09p09_rowCode 14 := by decide +kernel

private theorem R09p09_row_15 : pack 32 (R09p09_digit 15)=R09p09_rowCode 15 := by decide +kernel

private theorem R09p09_row_16 : pack 32 (R09p09_digit 16)=R09p09_rowCode 16 := by decide +kernel

private theorem R09p09_row_17 : pack 32 (R09p09_digit 17)=R09p09_rowCode 17 := by decide +kernel

private theorem R09p09_row_18 : pack 32 (R09p09_digit 18)=R09p09_rowCode 18 := by decide +kernel

private theorem R09p09_row_19 : pack 32 (R09p09_digit 19)=R09p09_rowCode 19 := by decide +kernel

private theorem R09p09_row_20 : pack 32 (R09p09_digit 20)=R09p09_rowCode 20 := by decide +kernel

private theorem R09p09_row_21 : pack 32 (R09p09_digit 21)=R09p09_rowCode 21 := by decide +kernel

theorem R09p09_row_binding : ∀ i : Fin 22,pack 32 (R09p09_digit i)=R09p09_rowCode i := by
  intro i
  fin_cases i
  · exact R09p09_row_00
  · exact R09p09_row_01
  · exact R09p09_row_02
  · exact R09p09_row_03
  · exact R09p09_row_04
  · exact R09p09_row_05
  · exact R09p09_row_06
  · exact R09p09_row_07
  · exact R09p09_row_08
  · exact R09p09_row_09
  · exact R09p09_row_10
  · exact R09p09_row_11
  · exact R09p09_row_12
  · exact R09p09_row_13
  · exact R09p09_row_14
  · exact R09p09_row_15
  · exact R09p09_row_16
  · exact R09p09_row_17
  · exact R09p09_row_18
  · exact R09p09_row_19
  · exact R09p09_row_20
  · exact R09p09_row_21

private theorem R09p09_column_00 : reversePack 32 (fun j : Fin 22 => R09p09_digit j 0)=R09p09_columnCode 0 := by decide +kernel

private theorem R09p09_column_01 : reversePack 32 (fun j : Fin 22 => R09p09_digit j 1)=R09p09_columnCode 1 := by decide +kernel

private theorem R09p09_column_02 : reversePack 32 (fun j : Fin 22 => R09p09_digit j 2)=R09p09_columnCode 2 := by decide +kernel

private theorem R09p09_column_03 : reversePack 32 (fun j : Fin 22 => R09p09_digit j 3)=R09p09_columnCode 3 := by decide +kernel

private theorem R09p09_column_04 : reversePack 32 (fun j : Fin 22 => R09p09_digit j 4)=R09p09_columnCode 4 := by decide +kernel

private theorem R09p09_column_05 : reversePack 32 (fun j : Fin 22 => R09p09_digit j 5)=R09p09_columnCode 5 := by decide +kernel

private theorem R09p09_column_06 : reversePack 32 (fun j : Fin 22 => R09p09_digit j 6)=R09p09_columnCode 6 := by decide +kernel

private theorem R09p09_column_07 : reversePack 32 (fun j : Fin 22 => R09p09_digit j 7)=R09p09_columnCode 7 := by decide +kernel

private theorem R09p09_column_08 : reversePack 32 (fun j : Fin 22 => R09p09_digit j 8)=R09p09_columnCode 8 := by decide +kernel

private theorem R09p09_column_09 : reversePack 32 (fun j : Fin 22 => R09p09_digit j 9)=R09p09_columnCode 9 := by decide +kernel

private theorem R09p09_column_10 : reversePack 32 (fun j : Fin 22 => R09p09_digit j 10)=R09p09_columnCode 10 := by decide +kernel

private theorem R09p09_column_11 : reversePack 32 (fun j : Fin 22 => R09p09_digit j 11)=R09p09_columnCode 11 := by decide +kernel

private theorem R09p09_column_12 : reversePack 32 (fun j : Fin 22 => R09p09_digit j 12)=R09p09_columnCode 12 := by decide +kernel

private theorem R09p09_column_13 : reversePack 32 (fun j : Fin 22 => R09p09_digit j 13)=R09p09_columnCode 13 := by decide +kernel

private theorem R09p09_column_14 : reversePack 32 (fun j : Fin 22 => R09p09_digit j 14)=R09p09_columnCode 14 := by decide +kernel

private theorem R09p09_column_15 : reversePack 32 (fun j : Fin 22 => R09p09_digit j 15)=R09p09_columnCode 15 := by decide +kernel

private theorem R09p09_column_16 : reversePack 32 (fun j : Fin 22 => R09p09_digit j 16)=R09p09_columnCode 16 := by decide +kernel

private theorem R09p09_column_17 : reversePack 32 (fun j : Fin 22 => R09p09_digit j 17)=R09p09_columnCode 17 := by decide +kernel

private theorem R09p09_column_18 : reversePack 32 (fun j : Fin 22 => R09p09_digit j 18)=R09p09_columnCode 18 := by decide +kernel

private theorem R09p09_column_19 : reversePack 32 (fun j : Fin 22 => R09p09_digit j 19)=R09p09_columnCode 19 := by decide +kernel

private theorem R09p09_column_20 : reversePack 32 (fun j : Fin 22 => R09p09_digit j 20)=R09p09_columnCode 20 := by decide +kernel

private theorem R09p09_column_21 : reversePack 32 (fun j : Fin 22 => R09p09_digit j 21)=R09p09_columnCode 21 := by decide +kernel

theorem R09p09_column_binding : ∀ i : Fin 22,reversePack 32 (fun j : Fin 22 => R09p09_digit j i)=R09p09_columnCode i := by
  intro i
  fin_cases i
  · exact R09p09_column_00
  · exact R09p09_column_01
  · exact R09p09_column_02
  · exact R09p09_column_03
  · exact R09p09_column_04
  · exact R09p09_column_05
  · exact R09p09_column_06
  · exact R09p09_column_07
  · exact R09p09_column_08
  · exact R09p09_column_09
  · exact R09p09_column_10
  · exact R09p09_column_11
  · exact R09p09_column_12
  · exact R09p09_column_13
  · exact R09p09_column_14
  · exact R09p09_column_15
  · exact R09p09_column_16
  · exact R09p09_column_17
  · exact R09p09_column_18
  · exact R09p09_column_19
  · exact R09p09_column_20
  · exact R09p09_column_21

def R09p09_data : PackedData 22 2 32 where
  raw := R09p09_digit
  digit_lt := R09p09_bound
  rowCode := R09p09_rowCode
  columnCode := R09p09_columnCode
  row_binding := R09p09_row_binding
  column_binding := R09p09_column_binding

end SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoCaches09
