import SymmetricSubgroupAsymptotics.MatrixKroneckerProductReflection
import Mathlib.Tactic.FinCases

/-! Literal14/F5 selected caches; digit bounds and both pack bindings are independently kernel checked. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedCaches01
open MatrixKroneckerProductReflection MatrixKroneckerDotReflection
open MatrixNaturalRowDotReflection SmallNaturalMatrixProductReflection

def C009_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 2362539325537
  | 1 => 1933314693280
  | 2 => 1892243751178
  | 3 => 9720301771
  | 4 => 286760452252
  | 5 => 3259073233
  | 6 => 1125282480640
  | 7 => 549755846912
  | 8 => 1786706542592
  | 9 => 549789434914
  | 10 => 2510832842824
  | 11 => 1653604451618
  | 12 => 2267744960576
  | 13 => 2208737363467
  | _ => 0

def C009_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 60847847790419386928835235807233
  | 1 => 20283648771506241352541830972420
  | 2 => 80467311479657566180944904705
  | 3 => 60847852626122665668809748120580
  | 4 => 3626851245820199542456579
  | 5 => 61165071134485944274986570088962
  | 6 => 3626777459969787431027204
  | 7 => 80468520405188949334456271874
  | 8 => 60847848999345206544563922141698
  | 9 => 3626777458843887524250626
  | 10 => 20283649961542595036791936516096
  | 11 => 20282414439354949726893192249603
  | 12 => 79232998254436284274841945090
  | 13 => 81447484360174260875520819528452
  | _ => 0

def C009_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 20599636588626109310196923957764
  | 1 => 317536460539383713349574394883
  | 2 => 40645285328746429682943118279427
  | 3 => 60927390264202018950881652834304
  | 4 => 81367941891095477385681136845824
  | 5 => 20441795592690823546339843899392
  | 6 => 1208926107845005326614530
  | 7 => 1237940057732124348608675841
  | 8 => 18963252907773419061763
  | 9 => 40881734275248930917873470144513
  | 10 => 79542497413127070706110301188
  | 11 => 40882972215306664168122052771843
  | 12 => 309485083608602838539698436
  | 13 => 60926460600302074688842502307844
  | _ => 0

def C009_digit (i j : Fin 14) : ℕ := packedDigit 3 (C009_lowColumnCode j) i.val

private theorem C009_bound_00 : ∀ j : Fin 14, C009_digit 0 j < 5 := by decide +kernel

private theorem C009_bound_01 : ∀ j : Fin 14, C009_digit 1 j < 5 := by decide +kernel

private theorem C009_bound_02 : ∀ j : Fin 14, C009_digit 2 j < 5 := by decide +kernel

private theorem C009_bound_03 : ∀ j : Fin 14, C009_digit 3 j < 5 := by decide +kernel

private theorem C009_bound_04 : ∀ j : Fin 14, C009_digit 4 j < 5 := by decide +kernel

private theorem C009_bound_05 : ∀ j : Fin 14, C009_digit 5 j < 5 := by decide +kernel

private theorem C009_bound_06 : ∀ j : Fin 14, C009_digit 6 j < 5 := by decide +kernel

private theorem C009_bound_07 : ∀ j : Fin 14, C009_digit 7 j < 5 := by decide +kernel

private theorem C009_bound_08 : ∀ j : Fin 14, C009_digit 8 j < 5 := by decide +kernel

private theorem C009_bound_09 : ∀ j : Fin 14, C009_digit 9 j < 5 := by decide +kernel

private theorem C009_bound_10 : ∀ j : Fin 14, C009_digit 10 j < 5 := by decide +kernel

private theorem C009_bound_11 : ∀ j : Fin 14, C009_digit 11 j < 5 := by decide +kernel

private theorem C009_bound_12 : ∀ j : Fin 14, C009_digit 12 j < 5 := by decide +kernel

private theorem C009_bound_13 : ∀ j : Fin 14, C009_digit 13 j < 5 := by decide +kernel

theorem C009_bound : ∀ i j : Fin 14, C009_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C009_bound_00 j
  · exact C009_bound_01 j
  · exact C009_bound_02 j
  · exact C009_bound_03 j
  · exact C009_bound_04 j
  · exact C009_bound_05 j
  · exact C009_bound_06 j
  · exact C009_bound_07 j
  · exact C009_bound_08 j
  · exact C009_bound_09 j
  · exact C009_bound_10 j
  · exact C009_bound_11 j
  · exact C009_bound_12 j
  · exact C009_bound_13 j

private theorem C009_row_00 : pack 256 (C009_digit 0)=C009_rowCode 0 := by decide +kernel

private theorem C009_row_01 : pack 256 (C009_digit 1)=C009_rowCode 1 := by decide +kernel

private theorem C009_row_02 : pack 256 (C009_digit 2)=C009_rowCode 2 := by decide +kernel

private theorem C009_row_03 : pack 256 (C009_digit 3)=C009_rowCode 3 := by decide +kernel

private theorem C009_row_04 : pack 256 (C009_digit 4)=C009_rowCode 4 := by decide +kernel

private theorem C009_row_05 : pack 256 (C009_digit 5)=C009_rowCode 5 := by decide +kernel

private theorem C009_row_06 : pack 256 (C009_digit 6)=C009_rowCode 6 := by decide +kernel

private theorem C009_row_07 : pack 256 (C009_digit 7)=C009_rowCode 7 := by decide +kernel

private theorem C009_row_08 : pack 256 (C009_digit 8)=C009_rowCode 8 := by decide +kernel

private theorem C009_row_09 : pack 256 (C009_digit 9)=C009_rowCode 9 := by decide +kernel

private theorem C009_row_10 : pack 256 (C009_digit 10)=C009_rowCode 10 := by decide +kernel

private theorem C009_row_11 : pack 256 (C009_digit 11)=C009_rowCode 11 := by decide +kernel

private theorem C009_row_12 : pack 256 (C009_digit 12)=C009_rowCode 12 := by decide +kernel

private theorem C009_row_13 : pack 256 (C009_digit 13)=C009_rowCode 13 := by decide +kernel

theorem C009_row_binding : ∀ i : Fin 14, pack 256 (C009_digit i)=C009_rowCode i := by
  intro i
  fin_cases i
  · exact C009_row_00
  · exact C009_row_01
  · exact C009_row_02
  · exact C009_row_03
  · exact C009_row_04
  · exact C009_row_05
  · exact C009_row_06
  · exact C009_row_07
  · exact C009_row_08
  · exact C009_row_09
  · exact C009_row_10
  · exact C009_row_11
  · exact C009_row_12
  · exact C009_row_13

private theorem C009_column_00 : reversePack 256 (fun j : Fin 14 => C009_digit j 0)=C009_columnCode 0 := by decide +kernel

private theorem C009_column_01 : reversePack 256 (fun j : Fin 14 => C009_digit j 1)=C009_columnCode 1 := by decide +kernel

private theorem C009_column_02 : reversePack 256 (fun j : Fin 14 => C009_digit j 2)=C009_columnCode 2 := by decide +kernel

private theorem C009_column_03 : reversePack 256 (fun j : Fin 14 => C009_digit j 3)=C009_columnCode 3 := by decide +kernel

private theorem C009_column_04 : reversePack 256 (fun j : Fin 14 => C009_digit j 4)=C009_columnCode 4 := by decide +kernel

private theorem C009_column_05 : reversePack 256 (fun j : Fin 14 => C009_digit j 5)=C009_columnCode 5 := by decide +kernel

private theorem C009_column_06 : reversePack 256 (fun j : Fin 14 => C009_digit j 6)=C009_columnCode 6 := by decide +kernel

private theorem C009_column_07 : reversePack 256 (fun j : Fin 14 => C009_digit j 7)=C009_columnCode 7 := by decide +kernel

private theorem C009_column_08 : reversePack 256 (fun j : Fin 14 => C009_digit j 8)=C009_columnCode 8 := by decide +kernel

private theorem C009_column_09 : reversePack 256 (fun j : Fin 14 => C009_digit j 9)=C009_columnCode 9 := by decide +kernel

private theorem C009_column_10 : reversePack 256 (fun j : Fin 14 => C009_digit j 10)=C009_columnCode 10 := by decide +kernel

private theorem C009_column_11 : reversePack 256 (fun j : Fin 14 => C009_digit j 11)=C009_columnCode 11 := by decide +kernel

private theorem C009_column_12 : reversePack 256 (fun j : Fin 14 => C009_digit j 12)=C009_columnCode 12 := by decide +kernel

private theorem C009_column_13 : reversePack 256 (fun j : Fin 14 => C009_digit j 13)=C009_columnCode 13 := by decide +kernel

theorem C009_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C009_digit j i)=C009_columnCode i := by
  intro i
  fin_cases i
  · exact C009_column_00
  · exact C009_column_01
  · exact C009_column_02
  · exact C009_column_03
  · exact C009_column_04
  · exact C009_column_05
  · exact C009_column_06
  · exact C009_column_07
  · exact C009_column_08
  · exact C009_column_09
  · exact C009_column_10
  · exact C009_column_11
  · exact C009_column_12
  · exact C009_column_13

def C009_data : PackedData 14 5 256 where
  raw := C009_digit
  digit_lt := C009_bound
  rowCode := C009_rowCode
  columnCode := C009_columnCode
  row_binding := C009_row_binding
  column_binding := C009_column_binding

def C010_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 1181420734481
  | 1 => 1795872143377
  | 2 => 240694903442
  | 3 => 310901879384
  | 4 => 2337724840161
  | 5 => 2276872792274
  | 6 => 223338305536
  | 7 => 1731182766083
  | 8 => 1677236109824
  | 9 => 225502630417
  | 10 => 2510484935308
  | 11 => 310637113620
  | 12 => 783213801986
  | 13 => 2365520431196
  | _ => 0

def C010_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 81289337520100356867622768345345
  | 1 => 60847848999345206544563922141698
  | 2 => 20283649961542595036791936516096
  | 3 => 81208867790787868235646380344324
  | 4 => 81368252570827269240149642576644
  | 5 => 40882969806844488605192687780867
  | 6 => 238308293339645257315808052226
  | 7 => 80161453247295062800687432193
  | 8 => 81368256197660068032584295252482
  | 9 => 238303457562579822508565922818
  | 10 => 60926768885812650868029544988676
  | 11 => 61086156083740513943017973088513
  | 12 => 40803746484755870051202804941313
  | 13 => 81208871412879780901317716738818
  | _ => 0

def C010_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 20440870783328428120221480452354
  | 1 => 20440870778624652778097120182787
  | 2 => 40723895730185389746691806331648
  | 3 => 237995195719608912549165401088
  | 4 => 20600255558682357259200874152452
  | 5 => 40724208832564973726633191080196
  | 6 => 4840425644941386344170240
  | 7 => 60847233656121614683467115725059
  | 8 => 1208926107848303895052291
  | 9 => 20440867142365278685880123523840
  | 10 => 81209486760789064181692957459460
  | 11 => 81289332693915527139074913862656
  | 12 => 40564820430470263344995978380033
  | 13 => 81367637241788933936179157598724
  | _ => 0

def C010_digit (i j : Fin 14) : ℕ := packedDigit 3 (C010_lowColumnCode j) i.val

private theorem C010_bound_00 : ∀ j : Fin 14, C010_digit 0 j < 5 := by decide +kernel

private theorem C010_bound_01 : ∀ j : Fin 14, C010_digit 1 j < 5 := by decide +kernel

private theorem C010_bound_02 : ∀ j : Fin 14, C010_digit 2 j < 5 := by decide +kernel

private theorem C010_bound_03 : ∀ j : Fin 14, C010_digit 3 j < 5 := by decide +kernel

private theorem C010_bound_04 : ∀ j : Fin 14, C010_digit 4 j < 5 := by decide +kernel

private theorem C010_bound_05 : ∀ j : Fin 14, C010_digit 5 j < 5 := by decide +kernel

private theorem C010_bound_06 : ∀ j : Fin 14, C010_digit 6 j < 5 := by decide +kernel

private theorem C010_bound_07 : ∀ j : Fin 14, C010_digit 7 j < 5 := by decide +kernel

private theorem C010_bound_08 : ∀ j : Fin 14, C010_digit 8 j < 5 := by decide +kernel

private theorem C010_bound_09 : ∀ j : Fin 14, C010_digit 9 j < 5 := by decide +kernel

private theorem C010_bound_10 : ∀ j : Fin 14, C010_digit 10 j < 5 := by decide +kernel

private theorem C010_bound_11 : ∀ j : Fin 14, C010_digit 11 j < 5 := by decide +kernel

private theorem C010_bound_12 : ∀ j : Fin 14, C010_digit 12 j < 5 := by decide +kernel

private theorem C010_bound_13 : ∀ j : Fin 14, C010_digit 13 j < 5 := by decide +kernel

theorem C010_bound : ∀ i j : Fin 14, C010_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C010_bound_00 j
  · exact C010_bound_01 j
  · exact C010_bound_02 j
  · exact C010_bound_03 j
  · exact C010_bound_04 j
  · exact C010_bound_05 j
  · exact C010_bound_06 j
  · exact C010_bound_07 j
  · exact C010_bound_08 j
  · exact C010_bound_09 j
  · exact C010_bound_10 j
  · exact C010_bound_11 j
  · exact C010_bound_12 j
  · exact C010_bound_13 j

private theorem C010_row_00 : pack 256 (C010_digit 0)=C010_rowCode 0 := by decide +kernel

private theorem C010_row_01 : pack 256 (C010_digit 1)=C010_rowCode 1 := by decide +kernel

private theorem C010_row_02 : pack 256 (C010_digit 2)=C010_rowCode 2 := by decide +kernel

private theorem C010_row_03 : pack 256 (C010_digit 3)=C010_rowCode 3 := by decide +kernel

private theorem C010_row_04 : pack 256 (C010_digit 4)=C010_rowCode 4 := by decide +kernel

private theorem C010_row_05 : pack 256 (C010_digit 5)=C010_rowCode 5 := by decide +kernel

private theorem C010_row_06 : pack 256 (C010_digit 6)=C010_rowCode 6 := by decide +kernel

private theorem C010_row_07 : pack 256 (C010_digit 7)=C010_rowCode 7 := by decide +kernel

private theorem C010_row_08 : pack 256 (C010_digit 8)=C010_rowCode 8 := by decide +kernel

private theorem C010_row_09 : pack 256 (C010_digit 9)=C010_rowCode 9 := by decide +kernel

private theorem C010_row_10 : pack 256 (C010_digit 10)=C010_rowCode 10 := by decide +kernel

private theorem C010_row_11 : pack 256 (C010_digit 11)=C010_rowCode 11 := by decide +kernel

private theorem C010_row_12 : pack 256 (C010_digit 12)=C010_rowCode 12 := by decide +kernel

private theorem C010_row_13 : pack 256 (C010_digit 13)=C010_rowCode 13 := by decide +kernel

theorem C010_row_binding : ∀ i : Fin 14, pack 256 (C010_digit i)=C010_rowCode i := by
  intro i
  fin_cases i
  · exact C010_row_00
  · exact C010_row_01
  · exact C010_row_02
  · exact C010_row_03
  · exact C010_row_04
  · exact C010_row_05
  · exact C010_row_06
  · exact C010_row_07
  · exact C010_row_08
  · exact C010_row_09
  · exact C010_row_10
  · exact C010_row_11
  · exact C010_row_12
  · exact C010_row_13

private theorem C010_column_00 : reversePack 256 (fun j : Fin 14 => C010_digit j 0)=C010_columnCode 0 := by decide +kernel

private theorem C010_column_01 : reversePack 256 (fun j : Fin 14 => C010_digit j 1)=C010_columnCode 1 := by decide +kernel

private theorem C010_column_02 : reversePack 256 (fun j : Fin 14 => C010_digit j 2)=C010_columnCode 2 := by decide +kernel

private theorem C010_column_03 : reversePack 256 (fun j : Fin 14 => C010_digit j 3)=C010_columnCode 3 := by decide +kernel

private theorem C010_column_04 : reversePack 256 (fun j : Fin 14 => C010_digit j 4)=C010_columnCode 4 := by decide +kernel

private theorem C010_column_05 : reversePack 256 (fun j : Fin 14 => C010_digit j 5)=C010_columnCode 5 := by decide +kernel

private theorem C010_column_06 : reversePack 256 (fun j : Fin 14 => C010_digit j 6)=C010_columnCode 6 := by decide +kernel

private theorem C010_column_07 : reversePack 256 (fun j : Fin 14 => C010_digit j 7)=C010_columnCode 7 := by decide +kernel

private theorem C010_column_08 : reversePack 256 (fun j : Fin 14 => C010_digit j 8)=C010_columnCode 8 := by decide +kernel

private theorem C010_column_09 : reversePack 256 (fun j : Fin 14 => C010_digit j 9)=C010_columnCode 9 := by decide +kernel

private theorem C010_column_10 : reversePack 256 (fun j : Fin 14 => C010_digit j 10)=C010_columnCode 10 := by decide +kernel

private theorem C010_column_11 : reversePack 256 (fun j : Fin 14 => C010_digit j 11)=C010_columnCode 11 := by decide +kernel

private theorem C010_column_12 : reversePack 256 (fun j : Fin 14 => C010_digit j 12)=C010_columnCode 12 := by decide +kernel

private theorem C010_column_13 : reversePack 256 (fun j : Fin 14 => C010_digit j 13)=C010_columnCode 13 := by decide +kernel

theorem C010_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C010_digit j i)=C010_columnCode i := by
  intro i
  fin_cases i
  · exact C010_column_00
  · exact C010_column_01
  · exact C010_column_02
  · exact C010_column_03
  · exact C010_column_04
  · exact C010_column_05
  · exact C010_column_06
  · exact C010_column_07
  · exact C010_column_08
  · exact C010_column_09
  · exact C010_column_10
  · exact C010_column_11
  · exact C010_column_12
  · exact C010_column_13

def C010_data : PackedData 14 5 256 where
  raw := C010_digit
  digit_lt := C010_bound
  rowCode := C010_rowCode
  columnCode := C010_columnCode
  row_binding := C010_row_binding
  column_binding := C010_column_binding

def C011_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 2277679318116
  | 1 => 1400333734546
  | 2 => 1342314517784
  | 3 => 2209125381722
  | 4 => 1410226325019
  | 5 => 301995239184
  | 6 => 1790079186954
  | 7 => 1813726234128
  | 8 => 2619490961
  | 9 => 1667848541852
  | 10 => 2364919132876
  | 11 => 2474193732834
  | 12 => 1271753621699
  | 13 => 1653751198818
  | _ => 0

def C011_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 40803127519476968247844445094404
  | 1 => 81130877577775924026324444971524
  | 2 => 20521026182483012774106354680321
  | 3 => 40565439400434566647337262907650
  | 4 => 61165383032624967152166840107268
  | 5 => 20282414448873757339664989291008
  | 6 => 238924850156084672540115665153
  | 7 => 40803433377709618418637965689602
  | 8 => 61005994635234392113664426508800
  | 9 => 20520717906417530124623423799554
  | 10 => 81129640837217653799187210436609
  | 11 => 316916286279465336098835923713
  | 12 => 159696682919597967273592292353
  | 13 => 61006927925893420251645076439556
  | _ => 0

def C011_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 81446862986414738172521434120452
  | 1 => 40723895716036664703087565538306
  | 2 => 238924850230087535739783086850
  | 3 => 40802816820874300758222058881028
  | 4 => 61084916925349194220005725832194
  | 5 => 159697901345634890644642268160
  | 6 => 40644052219706573952979323322883
  | 7 => 158459951879775623472692265475
  | 8 => 20441486126588914597560324194304
  | 9 => 81367945503705909400412761489411
  | 10 => 81209796255317260504801938178564
  | 11 => 40882662749131256470120966390788
  | 12 => 60848157284874158257945461391874
  | 13 => 40882043774407405531531248140291
  | _ => 0

def C011_digit (i j : Fin 14) : ℕ := packedDigit 3 (C011_lowColumnCode j) i.val

private theorem C011_bound_00 : ∀ j : Fin 14, C011_digit 0 j < 5 := by decide +kernel

private theorem C011_bound_01 : ∀ j : Fin 14, C011_digit 1 j < 5 := by decide +kernel

private theorem C011_bound_02 : ∀ j : Fin 14, C011_digit 2 j < 5 := by decide +kernel

private theorem C011_bound_03 : ∀ j : Fin 14, C011_digit 3 j < 5 := by decide +kernel

private theorem C011_bound_04 : ∀ j : Fin 14, C011_digit 4 j < 5 := by decide +kernel

private theorem C011_bound_05 : ∀ j : Fin 14, C011_digit 5 j < 5 := by decide +kernel

private theorem C011_bound_06 : ∀ j : Fin 14, C011_digit 6 j < 5 := by decide +kernel

private theorem C011_bound_07 : ∀ j : Fin 14, C011_digit 7 j < 5 := by decide +kernel

private theorem C011_bound_08 : ∀ j : Fin 14, C011_digit 8 j < 5 := by decide +kernel

private theorem C011_bound_09 : ∀ j : Fin 14, C011_digit 9 j < 5 := by decide +kernel

private theorem C011_bound_10 : ∀ j : Fin 14, C011_digit 10 j < 5 := by decide +kernel

private theorem C011_bound_11 : ∀ j : Fin 14, C011_digit 11 j < 5 := by decide +kernel

private theorem C011_bound_12 : ∀ j : Fin 14, C011_digit 12 j < 5 := by decide +kernel

private theorem C011_bound_13 : ∀ j : Fin 14, C011_digit 13 j < 5 := by decide +kernel

theorem C011_bound : ∀ i j : Fin 14, C011_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C011_bound_00 j
  · exact C011_bound_01 j
  · exact C011_bound_02 j
  · exact C011_bound_03 j
  · exact C011_bound_04 j
  · exact C011_bound_05 j
  · exact C011_bound_06 j
  · exact C011_bound_07 j
  · exact C011_bound_08 j
  · exact C011_bound_09 j
  · exact C011_bound_10 j
  · exact C011_bound_11 j
  · exact C011_bound_12 j
  · exact C011_bound_13 j

private theorem C011_row_00 : pack 256 (C011_digit 0)=C011_rowCode 0 := by decide +kernel

private theorem C011_row_01 : pack 256 (C011_digit 1)=C011_rowCode 1 := by decide +kernel

private theorem C011_row_02 : pack 256 (C011_digit 2)=C011_rowCode 2 := by decide +kernel

private theorem C011_row_03 : pack 256 (C011_digit 3)=C011_rowCode 3 := by decide +kernel

private theorem C011_row_04 : pack 256 (C011_digit 4)=C011_rowCode 4 := by decide +kernel

private theorem C011_row_05 : pack 256 (C011_digit 5)=C011_rowCode 5 := by decide +kernel

private theorem C011_row_06 : pack 256 (C011_digit 6)=C011_rowCode 6 := by decide +kernel

private theorem C011_row_07 : pack 256 (C011_digit 7)=C011_rowCode 7 := by decide +kernel

private theorem C011_row_08 : pack 256 (C011_digit 8)=C011_rowCode 8 := by decide +kernel

private theorem C011_row_09 : pack 256 (C011_digit 9)=C011_rowCode 9 := by decide +kernel

private theorem C011_row_10 : pack 256 (C011_digit 10)=C011_rowCode 10 := by decide +kernel

private theorem C011_row_11 : pack 256 (C011_digit 11)=C011_rowCode 11 := by decide +kernel

private theorem C011_row_12 : pack 256 (C011_digit 12)=C011_rowCode 12 := by decide +kernel

private theorem C011_row_13 : pack 256 (C011_digit 13)=C011_rowCode 13 := by decide +kernel

theorem C011_row_binding : ∀ i : Fin 14, pack 256 (C011_digit i)=C011_rowCode i := by
  intro i
  fin_cases i
  · exact C011_row_00
  · exact C011_row_01
  · exact C011_row_02
  · exact C011_row_03
  · exact C011_row_04
  · exact C011_row_05
  · exact C011_row_06
  · exact C011_row_07
  · exact C011_row_08
  · exact C011_row_09
  · exact C011_row_10
  · exact C011_row_11
  · exact C011_row_12
  · exact C011_row_13

private theorem C011_column_00 : reversePack 256 (fun j : Fin 14 => C011_digit j 0)=C011_columnCode 0 := by decide +kernel

private theorem C011_column_01 : reversePack 256 (fun j : Fin 14 => C011_digit j 1)=C011_columnCode 1 := by decide +kernel

private theorem C011_column_02 : reversePack 256 (fun j : Fin 14 => C011_digit j 2)=C011_columnCode 2 := by decide +kernel

private theorem C011_column_03 : reversePack 256 (fun j : Fin 14 => C011_digit j 3)=C011_columnCode 3 := by decide +kernel

private theorem C011_column_04 : reversePack 256 (fun j : Fin 14 => C011_digit j 4)=C011_columnCode 4 := by decide +kernel

private theorem C011_column_05 : reversePack 256 (fun j : Fin 14 => C011_digit j 5)=C011_columnCode 5 := by decide +kernel

private theorem C011_column_06 : reversePack 256 (fun j : Fin 14 => C011_digit j 6)=C011_columnCode 6 := by decide +kernel

private theorem C011_column_07 : reversePack 256 (fun j : Fin 14 => C011_digit j 7)=C011_columnCode 7 := by decide +kernel

private theorem C011_column_08 : reversePack 256 (fun j : Fin 14 => C011_digit j 8)=C011_columnCode 8 := by decide +kernel

private theorem C011_column_09 : reversePack 256 (fun j : Fin 14 => C011_digit j 9)=C011_columnCode 9 := by decide +kernel

private theorem C011_column_10 : reversePack 256 (fun j : Fin 14 => C011_digit j 10)=C011_columnCode 10 := by decide +kernel

private theorem C011_column_11 : reversePack 256 (fun j : Fin 14 => C011_digit j 11)=C011_columnCode 11 := by decide +kernel

private theorem C011_column_12 : reversePack 256 (fun j : Fin 14 => C011_digit j 12)=C011_columnCode 12 := by decide +kernel

private theorem C011_column_13 : reversePack 256 (fun j : Fin 14 => C011_digit j 13)=C011_columnCode 13 := by decide +kernel

theorem C011_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C011_digit j i)=C011_columnCode i := by
  intro i
  fin_cases i
  · exact C011_column_00
  · exact C011_column_01
  · exact C011_column_02
  · exact C011_column_03
  · exact C011_column_04
  · exact C011_column_05
  · exact C011_column_06
  · exact C011_column_07
  · exact C011_column_08
  · exact C011_column_09
  · exact C011_column_10
  · exact C011_column_11
  · exact C011_column_12
  · exact C011_column_13

def C011_data : PackedData 14 5 256 where
  raw := C011_digit
  digit_lt := C011_bound
  rowCode := C011_rowCode
  columnCode := C011_columnCode
  row_binding := C011_row_binding
  column_binding := C011_column_binding

def C012_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 2407522699282
  | 1 => 1756658958482
  | 2 => 218312480866
  | 3 => 790610659426
  | 4 => 2289239728331
  | 5 => 838060087524
  | 6 => 646566674688
  | 7 => 8593114635
  | 8 => 2439728186905
  | 9 => 1403785877579
  | 10 => 657472210650
  | 11 => 30639465556
  | 12 => 2233387583010
  | 13 => 829334257859
  | _ => 0

def C012_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 61006925508060226926437814370818
  | 1 => 317535251631937661486370128386
  | 2 => 60847541927464659072878991442432
  | 3 => 238307103284916887685542707204
  | 4 => 623810519074608926800543744
  | 5 => 20599944855283608366921449210114
  | 6 => 60926458191840116421296673522178
  | 7 => 20441488530218186764329249079300
  | 8 => 623805778261943829592801539
  | 9 => 60848469183031482359930704494593
  | 10 => 81130881204516345550554718733314
  | 11 => 317845955030759172127959614464
  | 12 => 81129639642477307759995258077443
  | 13 => 20599323472153067613576415412996
  | _ => 0

def C012_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 40723280368072186714136554504964
  | 1 => 40723894502370103073580404441347
  | 2 => 40882046182796153563931515880192
  | 3 => 40882046197000145656262890357505
  | 4 => 60927385438017548381101284786436
  | 5 => 81447484360192707619611775927297
  | 6 => 1237940057732970976890781953
  | 7 => 60926460600265469709247659966464
  | 8 => 20520097736916728729092923589380
  | 9 => 60926771298923333036640064177154
  | 10 => 40803435795597935809894214271233
  | 11 => 81288406651978297964356100620288
  | 12 => 40881735484211716638995032309764
  | 13 => 60848157266003138505391680259073
  | _ => 0

def C012_digit (i j : Fin 14) : ℕ := packedDigit 3 (C012_lowColumnCode j) i.val

private theorem C012_bound_00 : ∀ j : Fin 14, C012_digit 0 j < 5 := by decide +kernel

private theorem C012_bound_01 : ∀ j : Fin 14, C012_digit 1 j < 5 := by decide +kernel

private theorem C012_bound_02 : ∀ j : Fin 14, C012_digit 2 j < 5 := by decide +kernel

private theorem C012_bound_03 : ∀ j : Fin 14, C012_digit 3 j < 5 := by decide +kernel

private theorem C012_bound_04 : ∀ j : Fin 14, C012_digit 4 j < 5 := by decide +kernel

private theorem C012_bound_05 : ∀ j : Fin 14, C012_digit 5 j < 5 := by decide +kernel

private theorem C012_bound_06 : ∀ j : Fin 14, C012_digit 6 j < 5 := by decide +kernel

private theorem C012_bound_07 : ∀ j : Fin 14, C012_digit 7 j < 5 := by decide +kernel

private theorem C012_bound_08 : ∀ j : Fin 14, C012_digit 8 j < 5 := by decide +kernel

private theorem C012_bound_09 : ∀ j : Fin 14, C012_digit 9 j < 5 := by decide +kernel

private theorem C012_bound_10 : ∀ j : Fin 14, C012_digit 10 j < 5 := by decide +kernel

private theorem C012_bound_11 : ∀ j : Fin 14, C012_digit 11 j < 5 := by decide +kernel

private theorem C012_bound_12 : ∀ j : Fin 14, C012_digit 12 j < 5 := by decide +kernel

private theorem C012_bound_13 : ∀ j : Fin 14, C012_digit 13 j < 5 := by decide +kernel

theorem C012_bound : ∀ i j : Fin 14, C012_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C012_bound_00 j
  · exact C012_bound_01 j
  · exact C012_bound_02 j
  · exact C012_bound_03 j
  · exact C012_bound_04 j
  · exact C012_bound_05 j
  · exact C012_bound_06 j
  · exact C012_bound_07 j
  · exact C012_bound_08 j
  · exact C012_bound_09 j
  · exact C012_bound_10 j
  · exact C012_bound_11 j
  · exact C012_bound_12 j
  · exact C012_bound_13 j

private theorem C012_row_00 : pack 256 (C012_digit 0)=C012_rowCode 0 := by decide +kernel

private theorem C012_row_01 : pack 256 (C012_digit 1)=C012_rowCode 1 := by decide +kernel

private theorem C012_row_02 : pack 256 (C012_digit 2)=C012_rowCode 2 := by decide +kernel

private theorem C012_row_03 : pack 256 (C012_digit 3)=C012_rowCode 3 := by decide +kernel

private theorem C012_row_04 : pack 256 (C012_digit 4)=C012_rowCode 4 := by decide +kernel

private theorem C012_row_05 : pack 256 (C012_digit 5)=C012_rowCode 5 := by decide +kernel

private theorem C012_row_06 : pack 256 (C012_digit 6)=C012_rowCode 6 := by decide +kernel

private theorem C012_row_07 : pack 256 (C012_digit 7)=C012_rowCode 7 := by decide +kernel

private theorem C012_row_08 : pack 256 (C012_digit 8)=C012_rowCode 8 := by decide +kernel

private theorem C012_row_09 : pack 256 (C012_digit 9)=C012_rowCode 9 := by decide +kernel

private theorem C012_row_10 : pack 256 (C012_digit 10)=C012_rowCode 10 := by decide +kernel

private theorem C012_row_11 : pack 256 (C012_digit 11)=C012_rowCode 11 := by decide +kernel

private theorem C012_row_12 : pack 256 (C012_digit 12)=C012_rowCode 12 := by decide +kernel

private theorem C012_row_13 : pack 256 (C012_digit 13)=C012_rowCode 13 := by decide +kernel

theorem C012_row_binding : ∀ i : Fin 14, pack 256 (C012_digit i)=C012_rowCode i := by
  intro i
  fin_cases i
  · exact C012_row_00
  · exact C012_row_01
  · exact C012_row_02
  · exact C012_row_03
  · exact C012_row_04
  · exact C012_row_05
  · exact C012_row_06
  · exact C012_row_07
  · exact C012_row_08
  · exact C012_row_09
  · exact C012_row_10
  · exact C012_row_11
  · exact C012_row_12
  · exact C012_row_13

private theorem C012_column_00 : reversePack 256 (fun j : Fin 14 => C012_digit j 0)=C012_columnCode 0 := by decide +kernel

private theorem C012_column_01 : reversePack 256 (fun j : Fin 14 => C012_digit j 1)=C012_columnCode 1 := by decide +kernel

private theorem C012_column_02 : reversePack 256 (fun j : Fin 14 => C012_digit j 2)=C012_columnCode 2 := by decide +kernel

private theorem C012_column_03 : reversePack 256 (fun j : Fin 14 => C012_digit j 3)=C012_columnCode 3 := by decide +kernel

private theorem C012_column_04 : reversePack 256 (fun j : Fin 14 => C012_digit j 4)=C012_columnCode 4 := by decide +kernel

private theorem C012_column_05 : reversePack 256 (fun j : Fin 14 => C012_digit j 5)=C012_columnCode 5 := by decide +kernel

private theorem C012_column_06 : reversePack 256 (fun j : Fin 14 => C012_digit j 6)=C012_columnCode 6 := by decide +kernel

private theorem C012_column_07 : reversePack 256 (fun j : Fin 14 => C012_digit j 7)=C012_columnCode 7 := by decide +kernel

private theorem C012_column_08 : reversePack 256 (fun j : Fin 14 => C012_digit j 8)=C012_columnCode 8 := by decide +kernel

private theorem C012_column_09 : reversePack 256 (fun j : Fin 14 => C012_digit j 9)=C012_columnCode 9 := by decide +kernel

private theorem C012_column_10 : reversePack 256 (fun j : Fin 14 => C012_digit j 10)=C012_columnCode 10 := by decide +kernel

private theorem C012_column_11 : reversePack 256 (fun j : Fin 14 => C012_digit j 11)=C012_columnCode 11 := by decide +kernel

private theorem C012_column_12 : reversePack 256 (fun j : Fin 14 => C012_digit j 12)=C012_columnCode 12 := by decide +kernel

private theorem C012_column_13 : reversePack 256 (fun j : Fin 14 => C012_digit j 13)=C012_columnCode 13 := by decide +kernel

theorem C012_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C012_digit j i)=C012_columnCode i := by
  intro i
  fin_cases i
  · exact C012_column_00
  · exact C012_column_01
  · exact C012_column_02
  · exact C012_column_03
  · exact C012_column_04
  · exact C012_column_05
  · exact C012_column_06
  · exact C012_column_07
  · exact C012_column_08
  · exact C012_column_09
  · exact C012_column_10
  · exact C012_column_11
  · exact C012_column_12
  · exact C012_column_13

def C012_data : PackedData 14 5 256 where
  raw := C012_digit
  digit_lt := C012_bound
  rowCode := C012_rowCode
  columnCode := C012_columnCode
  row_binding := C012_row_binding
  column_binding := C012_column_binding

def C013_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 1799088870040
  | 1 => 1875296694852
  | 2 => 2345077622818
  | 3 => 27919401746
  | 4 => 2199024173585
  | 5 => 154641973760
  | 6 => 1649401659392
  | 7 => 1099528404992
  | 8 => 1125286249500
  | 9 => 2278652773148
  | 10 => 8590197794
  | 11 => 27120738458
  | 12 => 549755813888
  | 13 => 2233387583010
  | _ => 0

def C013_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 40565440614137875675068049261568
  | 1 => 81130571719561863870350566359043
  | 2 => 618988909108621616097526018
  | 3 => 60847231233565910473220991222017
  | 4 => 618970019642694535563444993
  | 5 => 81130566888580951896911092187395
  | 6 => 20282720307068937837544745271555
  | 7 => 40566057156824252685354663150336
  | 8 => 9444805024432840048642
  | 9 => 618974742009454482071487492
  | 10 => 309494454554310808048763395
  | 11 => 81130568083339672062914201715201
  | 12 => 4722366485068668601090
  | 13 => 81208866596047450412638735172355
  | _ => 0

def C013_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 238304671266178207636397294083
  | 1 => 81129949122727941750205731439363
  | 2 => 40881736711971662516931124068868
  | 3 => 40724514700186440730939255619584
  | 4 => 20440867137680021862840465883140
  | 5 => 1227852179879779616555520
  | 6 => 4294967299
  | 7 => 1099511627778
  | 8 => 81367325320056598848187144536066
  | 9 => 81368562051188511360109930152196
  | 10 => 40881734275212109485121065779200
  | 11 => 40803122674365922932275554746368
  | 12 => 1
  | 13 => 40881735484211716638995032309764
  | _ => 0

def C013_digit (i j : Fin 14) : ℕ := packedDigit 3 (C013_lowColumnCode j) i.val

private theorem C013_bound_00 : ∀ j : Fin 14, C013_digit 0 j < 5 := by decide +kernel

private theorem C013_bound_01 : ∀ j : Fin 14, C013_digit 1 j < 5 := by decide +kernel

private theorem C013_bound_02 : ∀ j : Fin 14, C013_digit 2 j < 5 := by decide +kernel

private theorem C013_bound_03 : ∀ j : Fin 14, C013_digit 3 j < 5 := by decide +kernel

private theorem C013_bound_04 : ∀ j : Fin 14, C013_digit 4 j < 5 := by decide +kernel

private theorem C013_bound_05 : ∀ j : Fin 14, C013_digit 5 j < 5 := by decide +kernel

private theorem C013_bound_06 : ∀ j : Fin 14, C013_digit 6 j < 5 := by decide +kernel

private theorem C013_bound_07 : ∀ j : Fin 14, C013_digit 7 j < 5 := by decide +kernel

private theorem C013_bound_08 : ∀ j : Fin 14, C013_digit 8 j < 5 := by decide +kernel

private theorem C013_bound_09 : ∀ j : Fin 14, C013_digit 9 j < 5 := by decide +kernel

private theorem C013_bound_10 : ∀ j : Fin 14, C013_digit 10 j < 5 := by decide +kernel

private theorem C013_bound_11 : ∀ j : Fin 14, C013_digit 11 j < 5 := by decide +kernel

private theorem C013_bound_12 : ∀ j : Fin 14, C013_digit 12 j < 5 := by decide +kernel

private theorem C013_bound_13 : ∀ j : Fin 14, C013_digit 13 j < 5 := by decide +kernel

theorem C013_bound : ∀ i j : Fin 14, C013_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C013_bound_00 j
  · exact C013_bound_01 j
  · exact C013_bound_02 j
  · exact C013_bound_03 j
  · exact C013_bound_04 j
  · exact C013_bound_05 j
  · exact C013_bound_06 j
  · exact C013_bound_07 j
  · exact C013_bound_08 j
  · exact C013_bound_09 j
  · exact C013_bound_10 j
  · exact C013_bound_11 j
  · exact C013_bound_12 j
  · exact C013_bound_13 j

private theorem C013_row_00 : pack 256 (C013_digit 0)=C013_rowCode 0 := by decide +kernel

private theorem C013_row_01 : pack 256 (C013_digit 1)=C013_rowCode 1 := by decide +kernel

private theorem C013_row_02 : pack 256 (C013_digit 2)=C013_rowCode 2 := by decide +kernel

private theorem C013_row_03 : pack 256 (C013_digit 3)=C013_rowCode 3 := by decide +kernel

private theorem C013_row_04 : pack 256 (C013_digit 4)=C013_rowCode 4 := by decide +kernel

private theorem C013_row_05 : pack 256 (C013_digit 5)=C013_rowCode 5 := by decide +kernel

private theorem C013_row_06 : pack 256 (C013_digit 6)=C013_rowCode 6 := by decide +kernel

private theorem C013_row_07 : pack 256 (C013_digit 7)=C013_rowCode 7 := by decide +kernel

private theorem C013_row_08 : pack 256 (C013_digit 8)=C013_rowCode 8 := by decide +kernel

private theorem C013_row_09 : pack 256 (C013_digit 9)=C013_rowCode 9 := by decide +kernel

private theorem C013_row_10 : pack 256 (C013_digit 10)=C013_rowCode 10 := by decide +kernel

private theorem C013_row_11 : pack 256 (C013_digit 11)=C013_rowCode 11 := by decide +kernel

private theorem C013_row_12 : pack 256 (C013_digit 12)=C013_rowCode 12 := by decide +kernel

private theorem C013_row_13 : pack 256 (C013_digit 13)=C013_rowCode 13 := by decide +kernel

theorem C013_row_binding : ∀ i : Fin 14, pack 256 (C013_digit i)=C013_rowCode i := by
  intro i
  fin_cases i
  · exact C013_row_00
  · exact C013_row_01
  · exact C013_row_02
  · exact C013_row_03
  · exact C013_row_04
  · exact C013_row_05
  · exact C013_row_06
  · exact C013_row_07
  · exact C013_row_08
  · exact C013_row_09
  · exact C013_row_10
  · exact C013_row_11
  · exact C013_row_12
  · exact C013_row_13

private theorem C013_column_00 : reversePack 256 (fun j : Fin 14 => C013_digit j 0)=C013_columnCode 0 := by decide +kernel

private theorem C013_column_01 : reversePack 256 (fun j : Fin 14 => C013_digit j 1)=C013_columnCode 1 := by decide +kernel

private theorem C013_column_02 : reversePack 256 (fun j : Fin 14 => C013_digit j 2)=C013_columnCode 2 := by decide +kernel

private theorem C013_column_03 : reversePack 256 (fun j : Fin 14 => C013_digit j 3)=C013_columnCode 3 := by decide +kernel

private theorem C013_column_04 : reversePack 256 (fun j : Fin 14 => C013_digit j 4)=C013_columnCode 4 := by decide +kernel

private theorem C013_column_05 : reversePack 256 (fun j : Fin 14 => C013_digit j 5)=C013_columnCode 5 := by decide +kernel

private theorem C013_column_06 : reversePack 256 (fun j : Fin 14 => C013_digit j 6)=C013_columnCode 6 := by decide +kernel

private theorem C013_column_07 : reversePack 256 (fun j : Fin 14 => C013_digit j 7)=C013_columnCode 7 := by decide +kernel

private theorem C013_column_08 : reversePack 256 (fun j : Fin 14 => C013_digit j 8)=C013_columnCode 8 := by decide +kernel

private theorem C013_column_09 : reversePack 256 (fun j : Fin 14 => C013_digit j 9)=C013_columnCode 9 := by decide +kernel

private theorem C013_column_10 : reversePack 256 (fun j : Fin 14 => C013_digit j 10)=C013_columnCode 10 := by decide +kernel

private theorem C013_column_11 : reversePack 256 (fun j : Fin 14 => C013_digit j 11)=C013_columnCode 11 := by decide +kernel

private theorem C013_column_12 : reversePack 256 (fun j : Fin 14 => C013_digit j 12)=C013_columnCode 12 := by decide +kernel

private theorem C013_column_13 : reversePack 256 (fun j : Fin 14 => C013_digit j 13)=C013_columnCode 13 := by decide +kernel

theorem C013_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C013_digit j i)=C013_columnCode i := by
  intro i
  fin_cases i
  · exact C013_column_00
  · exact C013_column_01
  · exact C013_column_02
  · exact C013_column_03
  · exact C013_column_04
  · exact C013_column_05
  · exact C013_column_06
  · exact C013_column_07
  · exact C013_column_08
  · exact C013_column_09
  · exact C013_column_10
  · exact C013_column_11
  · exact C013_column_12
  · exact C013_column_13

def C013_data : PackedData 14 5 256 where
  raw := C013_digit
  digit_lt := C013_bound
  rowCode := C013_rowCode
  columnCode := C013_columnCode
  row_binding := C013_row_binding
  column_binding := C013_column_binding

def C014_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 2276735920152
  | 1 => 554344452801
  | 2 => 707915163267
  | 3 => 240990590050
  | 4 => 860254513228
  | 5 => 2270093640200
  | 6 => 1125822496779
  | 7 => 586666051234
  | 8 => 1048576
  | 9 => 1813758686883
  | 10 => 26114140242
  | 11 => 726034614340
  | 12 => 2235539404900
  | 13 => 1327701009610
  | _ => 0

def C014_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 40882972229418567216041082159360
  | 1 => 20599324690450121448013359480835
  | 2 => 60926767676849793650064875455232
  | 3 => 40882974647270277659568050995460
  | 4 => 40802506126864872538551026319618
  | 5 => 60847852626122881559034503102978
  | 6 => 20441486126588986369277044064258
  | 7 => 20599327103579106245500838347776
  | 8 => 20283342913273878853559704027392
  | 9 => 81129950322190726052771602235907
  | 10 => 81289332684397006351512031659008
  | 11 => 40882973438344530945858366210049
  | 12 => 60847847790419386928835235807233
  | 13 => 40882041356537391616892671688964
  | _ => 0

def C014_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 237689332727842040385001029892
  | 1 => 20283339272366215171807740166145
  | 2 => 60847851417196989890101269103105
  | 3 => 40882043764962816400613091574528
  | 4 => 81209180907352710178968000791553
  | 5 => 79229371440084238100070400260
  | 6 => 60926456973469276172402431295490
  | 7 => 40882354454212912022121737355265
  | 8 => 288230376151711744
  | 9 => 61164764072013452172200698380803
  | 10 => 40723589862563562456601724125184
  | 11 => 81129952735356819106012820931073
  | 12 => 81446865399544083539445556707332
  | 13 => 40644978252198853988098762736386
  | _ => 0

def C014_digit (i j : Fin 14) : ℕ := packedDigit 3 (C014_lowColumnCode j) i.val

private theorem C014_bound_00 : ∀ j : Fin 14, C014_digit 0 j < 5 := by decide +kernel

private theorem C014_bound_01 : ∀ j : Fin 14, C014_digit 1 j < 5 := by decide +kernel

private theorem C014_bound_02 : ∀ j : Fin 14, C014_digit 2 j < 5 := by decide +kernel

private theorem C014_bound_03 : ∀ j : Fin 14, C014_digit 3 j < 5 := by decide +kernel

private theorem C014_bound_04 : ∀ j : Fin 14, C014_digit 4 j < 5 := by decide +kernel

private theorem C014_bound_05 : ∀ j : Fin 14, C014_digit 5 j < 5 := by decide +kernel

private theorem C014_bound_06 : ∀ j : Fin 14, C014_digit 6 j < 5 := by decide +kernel

private theorem C014_bound_07 : ∀ j : Fin 14, C014_digit 7 j < 5 := by decide +kernel

private theorem C014_bound_08 : ∀ j : Fin 14, C014_digit 8 j < 5 := by decide +kernel

private theorem C014_bound_09 : ∀ j : Fin 14, C014_digit 9 j < 5 := by decide +kernel

private theorem C014_bound_10 : ∀ j : Fin 14, C014_digit 10 j < 5 := by decide +kernel

private theorem C014_bound_11 : ∀ j : Fin 14, C014_digit 11 j < 5 := by decide +kernel

private theorem C014_bound_12 : ∀ j : Fin 14, C014_digit 12 j < 5 := by decide +kernel

private theorem C014_bound_13 : ∀ j : Fin 14, C014_digit 13 j < 5 := by decide +kernel

theorem C014_bound : ∀ i j : Fin 14, C014_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C014_bound_00 j
  · exact C014_bound_01 j
  · exact C014_bound_02 j
  · exact C014_bound_03 j
  · exact C014_bound_04 j
  · exact C014_bound_05 j
  · exact C014_bound_06 j
  · exact C014_bound_07 j
  · exact C014_bound_08 j
  · exact C014_bound_09 j
  · exact C014_bound_10 j
  · exact C014_bound_11 j
  · exact C014_bound_12 j
  · exact C014_bound_13 j

private theorem C014_row_00 : pack 256 (C014_digit 0)=C014_rowCode 0 := by decide +kernel

private theorem C014_row_01 : pack 256 (C014_digit 1)=C014_rowCode 1 := by decide +kernel

private theorem C014_row_02 : pack 256 (C014_digit 2)=C014_rowCode 2 := by decide +kernel

private theorem C014_row_03 : pack 256 (C014_digit 3)=C014_rowCode 3 := by decide +kernel

private theorem C014_row_04 : pack 256 (C014_digit 4)=C014_rowCode 4 := by decide +kernel

private theorem C014_row_05 : pack 256 (C014_digit 5)=C014_rowCode 5 := by decide +kernel

private theorem C014_row_06 : pack 256 (C014_digit 6)=C014_rowCode 6 := by decide +kernel

private theorem C014_row_07 : pack 256 (C014_digit 7)=C014_rowCode 7 := by decide +kernel

private theorem C014_row_08 : pack 256 (C014_digit 8)=C014_rowCode 8 := by decide +kernel

private theorem C014_row_09 : pack 256 (C014_digit 9)=C014_rowCode 9 := by decide +kernel

private theorem C014_row_10 : pack 256 (C014_digit 10)=C014_rowCode 10 := by decide +kernel

private theorem C014_row_11 : pack 256 (C014_digit 11)=C014_rowCode 11 := by decide +kernel

private theorem C014_row_12 : pack 256 (C014_digit 12)=C014_rowCode 12 := by decide +kernel

private theorem C014_row_13 : pack 256 (C014_digit 13)=C014_rowCode 13 := by decide +kernel

theorem C014_row_binding : ∀ i : Fin 14, pack 256 (C014_digit i)=C014_rowCode i := by
  intro i
  fin_cases i
  · exact C014_row_00
  · exact C014_row_01
  · exact C014_row_02
  · exact C014_row_03
  · exact C014_row_04
  · exact C014_row_05
  · exact C014_row_06
  · exact C014_row_07
  · exact C014_row_08
  · exact C014_row_09
  · exact C014_row_10
  · exact C014_row_11
  · exact C014_row_12
  · exact C014_row_13

private theorem C014_column_00 : reversePack 256 (fun j : Fin 14 => C014_digit j 0)=C014_columnCode 0 := by decide +kernel

private theorem C014_column_01 : reversePack 256 (fun j : Fin 14 => C014_digit j 1)=C014_columnCode 1 := by decide +kernel

private theorem C014_column_02 : reversePack 256 (fun j : Fin 14 => C014_digit j 2)=C014_columnCode 2 := by decide +kernel

private theorem C014_column_03 : reversePack 256 (fun j : Fin 14 => C014_digit j 3)=C014_columnCode 3 := by decide +kernel

private theorem C014_column_04 : reversePack 256 (fun j : Fin 14 => C014_digit j 4)=C014_columnCode 4 := by decide +kernel

private theorem C014_column_05 : reversePack 256 (fun j : Fin 14 => C014_digit j 5)=C014_columnCode 5 := by decide +kernel

private theorem C014_column_06 : reversePack 256 (fun j : Fin 14 => C014_digit j 6)=C014_columnCode 6 := by decide +kernel

private theorem C014_column_07 : reversePack 256 (fun j : Fin 14 => C014_digit j 7)=C014_columnCode 7 := by decide +kernel

private theorem C014_column_08 : reversePack 256 (fun j : Fin 14 => C014_digit j 8)=C014_columnCode 8 := by decide +kernel

private theorem C014_column_09 : reversePack 256 (fun j : Fin 14 => C014_digit j 9)=C014_columnCode 9 := by decide +kernel

private theorem C014_column_10 : reversePack 256 (fun j : Fin 14 => C014_digit j 10)=C014_columnCode 10 := by decide +kernel

private theorem C014_column_11 : reversePack 256 (fun j : Fin 14 => C014_digit j 11)=C014_columnCode 11 := by decide +kernel

private theorem C014_column_12 : reversePack 256 (fun j : Fin 14 => C014_digit j 12)=C014_columnCode 12 := by decide +kernel

private theorem C014_column_13 : reversePack 256 (fun j : Fin 14 => C014_digit j 13)=C014_columnCode 13 := by decide +kernel

theorem C014_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C014_digit j i)=C014_columnCode i := by
  intro i
  fin_cases i
  · exact C014_column_00
  · exact C014_column_01
  · exact C014_column_02
  · exact C014_column_03
  · exact C014_column_04
  · exact C014_column_05
  · exact C014_column_06
  · exact C014_column_07
  · exact C014_column_08
  · exact C014_column_09
  · exact C014_column_10
  · exact C014_column_11
  · exact C014_column_12
  · exact C014_column_13

def C014_data : PackedData 14 5 256 where
  raw := C014_digit
  digit_lt := C014_bound
  rowCode := C014_rowCode
  columnCode := C014_columnCode
  row_binding := C014_row_binding
  column_binding := C014_column_binding

end SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedCaches01
