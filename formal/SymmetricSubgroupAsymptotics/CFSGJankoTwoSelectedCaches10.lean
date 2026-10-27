import SymmetricSubgroupAsymptotics.MatrixKroneckerProductReflection
import Mathlib.Tactic.FinCases

/-! Literal14/F5 selected caches; digit bounds and both pack bindings are independently kernel checked. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedCaches10
open MatrixKroneckerProductReflection MatrixKroneckerDotReflection
open MatrixNaturalRowDotReflection SmallNaturalMatrixProductReflection

def C089_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 1189203161185
  | 1 => 1178184517914
  | 2 => 147648299236
  | 3 => 2484711044113
  | 4 => 2233976537624
  | 5 => 2276523574033
  | 6 => 310320342784
  | 7 => 1396005709922
  | 8 => 2484839956641
  | 9 => 2499807912539
  | 10 => 2510832842824
  | 11 => 1961207052481
  | 12 => 1884424311488
  | 13 => 1169779082521
  | _ => 0

def C089_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 20282719102847182077986225783297
  | 1 => 60847230034122005543962796098308
  | 2 => 81368252570864091517314041840641
  | 3 => 40645290150282824583054211679232
  | 4 => 81209798668446533532665635930115
  | 5 => 158767033149788168840016036352
  | 6 => 20600254344960600354886550356226
  | 7 => 40802506117420356874796603277824
  | 8 => 81129949108616109635093229732098
  | 9 => 60848470382512640781658261553668
  | 10 => 20520715479102927356122263257347
  | 11 => 238927277471048286459566031106
  | 12 => 20521336885900569540668537569537
  | 13 => 40803437004542273381774795997698
  | _ => 0

def C089_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 20599631752885792685403416953090
  | 1 => 40803746470625663809266261229826
  | 2 => 81447479538656529172653915832832
  | 3 => 20440868360754566806946938160132
  | 4 => 237685715376526150702742110212
  | 5 => 20442105077682198429913592168708
  | 6 => 1241576280069175063422960640
  | 7 => 40882046187536894728878508082178
  | 8 => 20599941242636283144413542155268
  | 9 => 61085224001933662838948052009988
  | 10 => 79542497413127070706110301188
  | 11 => 20283342908570175284251608744963
  | 12 => 929668714832695653545739011
  | 13 => 20521334467974926602694652068098
  | _ => 0

def C089_digit (i j : Fin 14) : ℕ := packedDigit 3 (C089_lowColumnCode j) i.val

private theorem C089_bound_00 : ∀ j : Fin 14, C089_digit 0 j < 5 := by decide +kernel

private theorem C089_bound_01 : ∀ j : Fin 14, C089_digit 1 j < 5 := by decide +kernel

private theorem C089_bound_02 : ∀ j : Fin 14, C089_digit 2 j < 5 := by decide +kernel

private theorem C089_bound_03 : ∀ j : Fin 14, C089_digit 3 j < 5 := by decide +kernel

private theorem C089_bound_04 : ∀ j : Fin 14, C089_digit 4 j < 5 := by decide +kernel

private theorem C089_bound_05 : ∀ j : Fin 14, C089_digit 5 j < 5 := by decide +kernel

private theorem C089_bound_06 : ∀ j : Fin 14, C089_digit 6 j < 5 := by decide +kernel

private theorem C089_bound_07 : ∀ j : Fin 14, C089_digit 7 j < 5 := by decide +kernel

private theorem C089_bound_08 : ∀ j : Fin 14, C089_digit 8 j < 5 := by decide +kernel

private theorem C089_bound_09 : ∀ j : Fin 14, C089_digit 9 j < 5 := by decide +kernel

private theorem C089_bound_10 : ∀ j : Fin 14, C089_digit 10 j < 5 := by decide +kernel

private theorem C089_bound_11 : ∀ j : Fin 14, C089_digit 11 j < 5 := by decide +kernel

private theorem C089_bound_12 : ∀ j : Fin 14, C089_digit 12 j < 5 := by decide +kernel

private theorem C089_bound_13 : ∀ j : Fin 14, C089_digit 13 j < 5 := by decide +kernel

theorem C089_bound : ∀ i j : Fin 14, C089_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C089_bound_00 j
  · exact C089_bound_01 j
  · exact C089_bound_02 j
  · exact C089_bound_03 j
  · exact C089_bound_04 j
  · exact C089_bound_05 j
  · exact C089_bound_06 j
  · exact C089_bound_07 j
  · exact C089_bound_08 j
  · exact C089_bound_09 j
  · exact C089_bound_10 j
  · exact C089_bound_11 j
  · exact C089_bound_12 j
  · exact C089_bound_13 j

private theorem C089_row_00 : pack 256 (C089_digit 0)=C089_rowCode 0 := by decide +kernel

private theorem C089_row_01 : pack 256 (C089_digit 1)=C089_rowCode 1 := by decide +kernel

private theorem C089_row_02 : pack 256 (C089_digit 2)=C089_rowCode 2 := by decide +kernel

private theorem C089_row_03 : pack 256 (C089_digit 3)=C089_rowCode 3 := by decide +kernel

private theorem C089_row_04 : pack 256 (C089_digit 4)=C089_rowCode 4 := by decide +kernel

private theorem C089_row_05 : pack 256 (C089_digit 5)=C089_rowCode 5 := by decide +kernel

private theorem C089_row_06 : pack 256 (C089_digit 6)=C089_rowCode 6 := by decide +kernel

private theorem C089_row_07 : pack 256 (C089_digit 7)=C089_rowCode 7 := by decide +kernel

private theorem C089_row_08 : pack 256 (C089_digit 8)=C089_rowCode 8 := by decide +kernel

private theorem C089_row_09 : pack 256 (C089_digit 9)=C089_rowCode 9 := by decide +kernel

private theorem C089_row_10 : pack 256 (C089_digit 10)=C089_rowCode 10 := by decide +kernel

private theorem C089_row_11 : pack 256 (C089_digit 11)=C089_rowCode 11 := by decide +kernel

private theorem C089_row_12 : pack 256 (C089_digit 12)=C089_rowCode 12 := by decide +kernel

private theorem C089_row_13 : pack 256 (C089_digit 13)=C089_rowCode 13 := by decide +kernel

theorem C089_row_binding : ∀ i : Fin 14, pack 256 (C089_digit i)=C089_rowCode i := by
  intro i
  fin_cases i
  · exact C089_row_00
  · exact C089_row_01
  · exact C089_row_02
  · exact C089_row_03
  · exact C089_row_04
  · exact C089_row_05
  · exact C089_row_06
  · exact C089_row_07
  · exact C089_row_08
  · exact C089_row_09
  · exact C089_row_10
  · exact C089_row_11
  · exact C089_row_12
  · exact C089_row_13

private theorem C089_column_00 : reversePack 256 (fun j : Fin 14 => C089_digit j 0)=C089_columnCode 0 := by decide +kernel

private theorem C089_column_01 : reversePack 256 (fun j : Fin 14 => C089_digit j 1)=C089_columnCode 1 := by decide +kernel

private theorem C089_column_02 : reversePack 256 (fun j : Fin 14 => C089_digit j 2)=C089_columnCode 2 := by decide +kernel

private theorem C089_column_03 : reversePack 256 (fun j : Fin 14 => C089_digit j 3)=C089_columnCode 3 := by decide +kernel

private theorem C089_column_04 : reversePack 256 (fun j : Fin 14 => C089_digit j 4)=C089_columnCode 4 := by decide +kernel

private theorem C089_column_05 : reversePack 256 (fun j : Fin 14 => C089_digit j 5)=C089_columnCode 5 := by decide +kernel

private theorem C089_column_06 : reversePack 256 (fun j : Fin 14 => C089_digit j 6)=C089_columnCode 6 := by decide +kernel

private theorem C089_column_07 : reversePack 256 (fun j : Fin 14 => C089_digit j 7)=C089_columnCode 7 := by decide +kernel

private theorem C089_column_08 : reversePack 256 (fun j : Fin 14 => C089_digit j 8)=C089_columnCode 8 := by decide +kernel

private theorem C089_column_09 : reversePack 256 (fun j : Fin 14 => C089_digit j 9)=C089_columnCode 9 := by decide +kernel

private theorem C089_column_10 : reversePack 256 (fun j : Fin 14 => C089_digit j 10)=C089_columnCode 10 := by decide +kernel

private theorem C089_column_11 : reversePack 256 (fun j : Fin 14 => C089_digit j 11)=C089_columnCode 11 := by decide +kernel

private theorem C089_column_12 : reversePack 256 (fun j : Fin 14 => C089_digit j 12)=C089_columnCode 12 := by decide +kernel

private theorem C089_column_13 : reversePack 256 (fun j : Fin 14 => C089_digit j 13)=C089_columnCode 13 := by decide +kernel

theorem C089_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C089_digit j i)=C089_columnCode i := by
  intro i
  fin_cases i
  · exact C089_column_00
  · exact C089_column_01
  · exact C089_column_02
  · exact C089_column_03
  · exact C089_column_04
  · exact C089_column_05
  · exact C089_column_06
  · exact C089_column_07
  · exact C089_column_08
  · exact C089_column_09
  · exact C089_column_10
  · exact C089_column_11
  · exact C089_column_12
  · exact C089_column_13

def C089_data : PackedData 14 5 256 where
  raw := C089_digit
  digit_lt := C089_bound
  rowCode := C089_rowCode
  columnCode := C089_columnCode
  row_binding := C089_row_binding
  column_binding := C089_column_binding

def C090_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 578114360017
  | 1 => 1258851438788
  | 2 => 70404583563
  | 3 => 98316949516
  | 4 => 656079660572
  | 5 => 310320342784
  | 6 => 2484839956641
  | 7 => 2499807912539
  | 8 => 2276523574033
  | 9 => 2510832842824
  | 10 => 1396005709922
  | 11 => 1884424311488
  | 12 => 1169779082521
  | 13 => 1961207052481
  | _ => 0

def C090_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 20361640184036237189147191870465
  | 1 => 237689328005548741009317363714
  | 2 => 61165071129763578356157800121091
  | 3 => 81288409079256294911019331878913
  | 4 => 61164453378040773888447552356609
  | 5 => 20283029787356609155096182325506
  | 6 => 60927698554453263399598067810563
  | 7 => 159388416335596814246191760130
  | 8 => 20599322258486435615316470137090
  | 9 => 81367324125260912854950538904323
  | 10 => 40644980669995081209012610466818
  | 11 => 81130569306395914094478186512899
  | 12 => 81209799886761890563336129544704
  | 13 => 61006616027828185475547138097665
  | _ => 0

def C090_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 20441795597394959457930761666561
  | 1 => 81130566874377031861069966082562
  | 2 => 60927075957674753571471717564672
  | 3 => 81208871417602003550474313335040
  | 4 => 81367326538408632909462400925953
  | 5 => 1241576280069175063422960640
  | 6 => 20599941242636283144413542155268
  | 7 => 61085224001933662838948052009988
  | 8 => 20442105077682198429913592168708
  | 9 => 79542497413127070706110301188
  | 10 => 40882046187536894728878508082178
  | 11 => 929668714832695653545739011
  | 12 => 20521334467974926602694652068098
  | 13 => 20283342908570175284251608744963
  | _ => 0

def C090_digit (i j : Fin 14) : ℕ := packedDigit 3 (C090_lowColumnCode j) i.val

private theorem C090_bound_00 : ∀ j : Fin 14, C090_digit 0 j < 5 := by decide +kernel

private theorem C090_bound_01 : ∀ j : Fin 14, C090_digit 1 j < 5 := by decide +kernel

private theorem C090_bound_02 : ∀ j : Fin 14, C090_digit 2 j < 5 := by decide +kernel

private theorem C090_bound_03 : ∀ j : Fin 14, C090_digit 3 j < 5 := by decide +kernel

private theorem C090_bound_04 : ∀ j : Fin 14, C090_digit 4 j < 5 := by decide +kernel

private theorem C090_bound_05 : ∀ j : Fin 14, C090_digit 5 j < 5 := by decide +kernel

private theorem C090_bound_06 : ∀ j : Fin 14, C090_digit 6 j < 5 := by decide +kernel

private theorem C090_bound_07 : ∀ j : Fin 14, C090_digit 7 j < 5 := by decide +kernel

private theorem C090_bound_08 : ∀ j : Fin 14, C090_digit 8 j < 5 := by decide +kernel

private theorem C090_bound_09 : ∀ j : Fin 14, C090_digit 9 j < 5 := by decide +kernel

private theorem C090_bound_10 : ∀ j : Fin 14, C090_digit 10 j < 5 := by decide +kernel

private theorem C090_bound_11 : ∀ j : Fin 14, C090_digit 11 j < 5 := by decide +kernel

private theorem C090_bound_12 : ∀ j : Fin 14, C090_digit 12 j < 5 := by decide +kernel

private theorem C090_bound_13 : ∀ j : Fin 14, C090_digit 13 j < 5 := by decide +kernel

theorem C090_bound : ∀ i j : Fin 14, C090_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C090_bound_00 j
  · exact C090_bound_01 j
  · exact C090_bound_02 j
  · exact C090_bound_03 j
  · exact C090_bound_04 j
  · exact C090_bound_05 j
  · exact C090_bound_06 j
  · exact C090_bound_07 j
  · exact C090_bound_08 j
  · exact C090_bound_09 j
  · exact C090_bound_10 j
  · exact C090_bound_11 j
  · exact C090_bound_12 j
  · exact C090_bound_13 j

private theorem C090_row_00 : pack 256 (C090_digit 0)=C090_rowCode 0 := by decide +kernel

private theorem C090_row_01 : pack 256 (C090_digit 1)=C090_rowCode 1 := by decide +kernel

private theorem C090_row_02 : pack 256 (C090_digit 2)=C090_rowCode 2 := by decide +kernel

private theorem C090_row_03 : pack 256 (C090_digit 3)=C090_rowCode 3 := by decide +kernel

private theorem C090_row_04 : pack 256 (C090_digit 4)=C090_rowCode 4 := by decide +kernel

private theorem C090_row_05 : pack 256 (C090_digit 5)=C090_rowCode 5 := by decide +kernel

private theorem C090_row_06 : pack 256 (C090_digit 6)=C090_rowCode 6 := by decide +kernel

private theorem C090_row_07 : pack 256 (C090_digit 7)=C090_rowCode 7 := by decide +kernel

private theorem C090_row_08 : pack 256 (C090_digit 8)=C090_rowCode 8 := by decide +kernel

private theorem C090_row_09 : pack 256 (C090_digit 9)=C090_rowCode 9 := by decide +kernel

private theorem C090_row_10 : pack 256 (C090_digit 10)=C090_rowCode 10 := by decide +kernel

private theorem C090_row_11 : pack 256 (C090_digit 11)=C090_rowCode 11 := by decide +kernel

private theorem C090_row_12 : pack 256 (C090_digit 12)=C090_rowCode 12 := by decide +kernel

private theorem C090_row_13 : pack 256 (C090_digit 13)=C090_rowCode 13 := by decide +kernel

theorem C090_row_binding : ∀ i : Fin 14, pack 256 (C090_digit i)=C090_rowCode i := by
  intro i
  fin_cases i
  · exact C090_row_00
  · exact C090_row_01
  · exact C090_row_02
  · exact C090_row_03
  · exact C090_row_04
  · exact C090_row_05
  · exact C090_row_06
  · exact C090_row_07
  · exact C090_row_08
  · exact C090_row_09
  · exact C090_row_10
  · exact C090_row_11
  · exact C090_row_12
  · exact C090_row_13

private theorem C090_column_00 : reversePack 256 (fun j : Fin 14 => C090_digit j 0)=C090_columnCode 0 := by decide +kernel

private theorem C090_column_01 : reversePack 256 (fun j : Fin 14 => C090_digit j 1)=C090_columnCode 1 := by decide +kernel

private theorem C090_column_02 : reversePack 256 (fun j : Fin 14 => C090_digit j 2)=C090_columnCode 2 := by decide +kernel

private theorem C090_column_03 : reversePack 256 (fun j : Fin 14 => C090_digit j 3)=C090_columnCode 3 := by decide +kernel

private theorem C090_column_04 : reversePack 256 (fun j : Fin 14 => C090_digit j 4)=C090_columnCode 4 := by decide +kernel

private theorem C090_column_05 : reversePack 256 (fun j : Fin 14 => C090_digit j 5)=C090_columnCode 5 := by decide +kernel

private theorem C090_column_06 : reversePack 256 (fun j : Fin 14 => C090_digit j 6)=C090_columnCode 6 := by decide +kernel

private theorem C090_column_07 : reversePack 256 (fun j : Fin 14 => C090_digit j 7)=C090_columnCode 7 := by decide +kernel

private theorem C090_column_08 : reversePack 256 (fun j : Fin 14 => C090_digit j 8)=C090_columnCode 8 := by decide +kernel

private theorem C090_column_09 : reversePack 256 (fun j : Fin 14 => C090_digit j 9)=C090_columnCode 9 := by decide +kernel

private theorem C090_column_10 : reversePack 256 (fun j : Fin 14 => C090_digit j 10)=C090_columnCode 10 := by decide +kernel

private theorem C090_column_11 : reversePack 256 (fun j : Fin 14 => C090_digit j 11)=C090_columnCode 11 := by decide +kernel

private theorem C090_column_12 : reversePack 256 (fun j : Fin 14 => C090_digit j 12)=C090_columnCode 12 := by decide +kernel

private theorem C090_column_13 : reversePack 256 (fun j : Fin 14 => C090_digit j 13)=C090_columnCode 13 := by decide +kernel

theorem C090_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C090_digit j i)=C090_columnCode i := by
  intro i
  fin_cases i
  · exact C090_column_00
  · exact C090_column_01
  · exact C090_column_02
  · exact C090_column_03
  · exact C090_column_04
  · exact C090_column_05
  · exact C090_column_06
  · exact C090_column_07
  · exact C090_column_08
  · exact C090_column_09
  · exact C090_column_10
  · exact C090_column_11
  · exact C090_column_12
  · exact C090_column_13

def C090_data : PackedData 14 5 256 where
  raw := C090_digit
  digit_lt := C090_bound
  rowCode := C090_rowCode
  columnCode := C090_columnCode
  row_binding := C090_row_binding
  column_binding := C090_column_binding

def C091_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 647521707265
  | 1 => 563116885530
  | 2 => 156953355268
  | 3 => 636752082696
  | 4 => 1868737431624
  | 5 => 1804163220692
  | 6 => 166467847377
  | 7 => 1731182766083
  | 8 => 1410920658978
  | 9 => 1258765423769
  | 10 => 1873948816410
  | 11 => 1401773098760
  | 12 => 1169779082521
  | 13 => 1961207052481
  | _ => 0

def C091_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 20361640188777050420471346233857
  | 1 => 237997613570960191793943020288
  | 2 => 61165379410496087815957946302468
  | 3 => 81289025622035122373017104155394
  | 4 => 61164145092567379422299440677890
  | 5 => 20282413230447648918342729990914
  | 6 => 60927698545063870663889455742979
  | 7 => 158765819538712015953318707970
  | 8 => 20599322272616785128016058713091
  | 9 => 81368563269485276401242160038656
  | 10 => 40644358082679894639630224589827
  | 11 => 81130569297006377806509977501955
  | 12 => 81210108153456282822335017385985
  | 13 => 61006307742262484111034075316481
  | _ => 0

def C091_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 20283649971024438226397861970177
  | 1 => 40802507340568399717098296770561
  | 2 => 81129640841976913209453361365504
  | 3 => 80469743553449088110490157313
  | 4 => 79542502190834067271894237955
  | 5 => 81289025612590101737643951915523
  | 6 => 20441796820506109092447599657472
  | 7 => 60847233656121614683467115725059
  | 8 => 40881736707249439867774611751938
  | 9 => 20520715483788184463944022360578
  | 10 => 40802506126920428943554268758787
  | 11 => 80469729331297073624292459522
  | 12 => 20521334467974926602694652068098
  | 13 => 20283342908570175284251608744963
  | _ => 0

def C091_digit (i j : Fin 14) : ℕ := packedDigit 3 (C091_lowColumnCode j) i.val

private theorem C091_bound_00 : ∀ j : Fin 14, C091_digit 0 j < 5 := by decide +kernel

private theorem C091_bound_01 : ∀ j : Fin 14, C091_digit 1 j < 5 := by decide +kernel

private theorem C091_bound_02 : ∀ j : Fin 14, C091_digit 2 j < 5 := by decide +kernel

private theorem C091_bound_03 : ∀ j : Fin 14, C091_digit 3 j < 5 := by decide +kernel

private theorem C091_bound_04 : ∀ j : Fin 14, C091_digit 4 j < 5 := by decide +kernel

private theorem C091_bound_05 : ∀ j : Fin 14, C091_digit 5 j < 5 := by decide +kernel

private theorem C091_bound_06 : ∀ j : Fin 14, C091_digit 6 j < 5 := by decide +kernel

private theorem C091_bound_07 : ∀ j : Fin 14, C091_digit 7 j < 5 := by decide +kernel

private theorem C091_bound_08 : ∀ j : Fin 14, C091_digit 8 j < 5 := by decide +kernel

private theorem C091_bound_09 : ∀ j : Fin 14, C091_digit 9 j < 5 := by decide +kernel

private theorem C091_bound_10 : ∀ j : Fin 14, C091_digit 10 j < 5 := by decide +kernel

private theorem C091_bound_11 : ∀ j : Fin 14, C091_digit 11 j < 5 := by decide +kernel

private theorem C091_bound_12 : ∀ j : Fin 14, C091_digit 12 j < 5 := by decide +kernel

private theorem C091_bound_13 : ∀ j : Fin 14, C091_digit 13 j < 5 := by decide +kernel

theorem C091_bound : ∀ i j : Fin 14, C091_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C091_bound_00 j
  · exact C091_bound_01 j
  · exact C091_bound_02 j
  · exact C091_bound_03 j
  · exact C091_bound_04 j
  · exact C091_bound_05 j
  · exact C091_bound_06 j
  · exact C091_bound_07 j
  · exact C091_bound_08 j
  · exact C091_bound_09 j
  · exact C091_bound_10 j
  · exact C091_bound_11 j
  · exact C091_bound_12 j
  · exact C091_bound_13 j

private theorem C091_row_00 : pack 256 (C091_digit 0)=C091_rowCode 0 := by decide +kernel

private theorem C091_row_01 : pack 256 (C091_digit 1)=C091_rowCode 1 := by decide +kernel

private theorem C091_row_02 : pack 256 (C091_digit 2)=C091_rowCode 2 := by decide +kernel

private theorem C091_row_03 : pack 256 (C091_digit 3)=C091_rowCode 3 := by decide +kernel

private theorem C091_row_04 : pack 256 (C091_digit 4)=C091_rowCode 4 := by decide +kernel

private theorem C091_row_05 : pack 256 (C091_digit 5)=C091_rowCode 5 := by decide +kernel

private theorem C091_row_06 : pack 256 (C091_digit 6)=C091_rowCode 6 := by decide +kernel

private theorem C091_row_07 : pack 256 (C091_digit 7)=C091_rowCode 7 := by decide +kernel

private theorem C091_row_08 : pack 256 (C091_digit 8)=C091_rowCode 8 := by decide +kernel

private theorem C091_row_09 : pack 256 (C091_digit 9)=C091_rowCode 9 := by decide +kernel

private theorem C091_row_10 : pack 256 (C091_digit 10)=C091_rowCode 10 := by decide +kernel

private theorem C091_row_11 : pack 256 (C091_digit 11)=C091_rowCode 11 := by decide +kernel

private theorem C091_row_12 : pack 256 (C091_digit 12)=C091_rowCode 12 := by decide +kernel

private theorem C091_row_13 : pack 256 (C091_digit 13)=C091_rowCode 13 := by decide +kernel

theorem C091_row_binding : ∀ i : Fin 14, pack 256 (C091_digit i)=C091_rowCode i := by
  intro i
  fin_cases i
  · exact C091_row_00
  · exact C091_row_01
  · exact C091_row_02
  · exact C091_row_03
  · exact C091_row_04
  · exact C091_row_05
  · exact C091_row_06
  · exact C091_row_07
  · exact C091_row_08
  · exact C091_row_09
  · exact C091_row_10
  · exact C091_row_11
  · exact C091_row_12
  · exact C091_row_13

private theorem C091_column_00 : reversePack 256 (fun j : Fin 14 => C091_digit j 0)=C091_columnCode 0 := by decide +kernel

private theorem C091_column_01 : reversePack 256 (fun j : Fin 14 => C091_digit j 1)=C091_columnCode 1 := by decide +kernel

private theorem C091_column_02 : reversePack 256 (fun j : Fin 14 => C091_digit j 2)=C091_columnCode 2 := by decide +kernel

private theorem C091_column_03 : reversePack 256 (fun j : Fin 14 => C091_digit j 3)=C091_columnCode 3 := by decide +kernel

private theorem C091_column_04 : reversePack 256 (fun j : Fin 14 => C091_digit j 4)=C091_columnCode 4 := by decide +kernel

private theorem C091_column_05 : reversePack 256 (fun j : Fin 14 => C091_digit j 5)=C091_columnCode 5 := by decide +kernel

private theorem C091_column_06 : reversePack 256 (fun j : Fin 14 => C091_digit j 6)=C091_columnCode 6 := by decide +kernel

private theorem C091_column_07 : reversePack 256 (fun j : Fin 14 => C091_digit j 7)=C091_columnCode 7 := by decide +kernel

private theorem C091_column_08 : reversePack 256 (fun j : Fin 14 => C091_digit j 8)=C091_columnCode 8 := by decide +kernel

private theorem C091_column_09 : reversePack 256 (fun j : Fin 14 => C091_digit j 9)=C091_columnCode 9 := by decide +kernel

private theorem C091_column_10 : reversePack 256 (fun j : Fin 14 => C091_digit j 10)=C091_columnCode 10 := by decide +kernel

private theorem C091_column_11 : reversePack 256 (fun j : Fin 14 => C091_digit j 11)=C091_columnCode 11 := by decide +kernel

private theorem C091_column_12 : reversePack 256 (fun j : Fin 14 => C091_digit j 12)=C091_columnCode 12 := by decide +kernel

private theorem C091_column_13 : reversePack 256 (fun j : Fin 14 => C091_digit j 13)=C091_columnCode 13 := by decide +kernel

theorem C091_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C091_digit j i)=C091_columnCode i := by
  intro i
  fin_cases i
  · exact C091_column_00
  · exact C091_column_01
  · exact C091_column_02
  · exact C091_column_03
  · exact C091_column_04
  · exact C091_column_05
  · exact C091_column_06
  · exact C091_column_07
  · exact C091_column_08
  · exact C091_column_09
  · exact C091_column_10
  · exact C091_column_11
  · exact C091_column_12
  · exact C091_column_13

def C091_data : PackedData 14 5 256 where
  raw := C091_digit
  digit_lt := C091_bound
  rowCode := C091_rowCode
  columnCode := C091_columnCode
  row_binding := C091_row_binding
  column_binding := C091_column_binding

def C092_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 792712061467
  | 1 => 716782318304
  | 2 => 1721382217876
  | 3 => 1272724362016
  | 4 => 1866432399552
  | 5 => 1410920658978
  | 6 => 1804163220692
  | 7 => 1873948816410
  | 8 => 166467847377
  | 9 => 1731182766083
  | 10 => 1258765423769
  | 11 => 1961207052481
  | 12 => 1401773098760
  | 13 => 1169779082521
  | _ => 0

def C092_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 20282720311773002819614802182147
  | 1 => 60926460600283844681600421987331
  | 2 => 81447481937600183387286715630336
  | 3 => 40803744071663562572387655614721
  | 4 => 81130568088080701463756328272642
  | 5 => 309489787745359958227551236
  | 6 => 20600251927108960565985338721028
  | 7 => 40644049806595604963570871370754
  | 8 => 81129952744801407954360717148929
  | 9 => 61165381828347870875635121456130
  | 10 => 20362261590833734133696321225474
  | 11 => 238924850211569019945092121348
  | 12 => 20600562616359129095014772179459
  | 13 => 40724206419380289255574035693825
  | _ => 0

def C092_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 61084914516942432635719929561857
  | 1 => 317842328253444727111084605953
  | 2 => 81288718554802865331997830545667
  | 3 => 318151803763120254766287159810
  | 4 => 933309696139516692991640323
  | 5 => 40881736707249439867774611751938
  | 6 => 81289025612590101737643951915523
  | 7 => 40802506126920428943554268758787
  | 8 => 20441796820506109092447599657472
  | 9 => 60847233656121614683467115725059
  | 10 => 20520715483788184463944022360578
  | 11 => 20283342908570175284251608744963
  | 12 => 80469729331297073624292459522
  | 13 => 20521334467974926602694652068098
  | _ => 0

def C092_digit (i j : Fin 14) : ℕ := packedDigit 3 (C092_lowColumnCode j) i.val

private theorem C092_bound_00 : ∀ j : Fin 14, C092_digit 0 j < 5 := by decide +kernel

private theorem C092_bound_01 : ∀ j : Fin 14, C092_digit 1 j < 5 := by decide +kernel

private theorem C092_bound_02 : ∀ j : Fin 14, C092_digit 2 j < 5 := by decide +kernel

private theorem C092_bound_03 : ∀ j : Fin 14, C092_digit 3 j < 5 := by decide +kernel

private theorem C092_bound_04 : ∀ j : Fin 14, C092_digit 4 j < 5 := by decide +kernel

private theorem C092_bound_05 : ∀ j : Fin 14, C092_digit 5 j < 5 := by decide +kernel

private theorem C092_bound_06 : ∀ j : Fin 14, C092_digit 6 j < 5 := by decide +kernel

private theorem C092_bound_07 : ∀ j : Fin 14, C092_digit 7 j < 5 := by decide +kernel

private theorem C092_bound_08 : ∀ j : Fin 14, C092_digit 8 j < 5 := by decide +kernel

private theorem C092_bound_09 : ∀ j : Fin 14, C092_digit 9 j < 5 := by decide +kernel

private theorem C092_bound_10 : ∀ j : Fin 14, C092_digit 10 j < 5 := by decide +kernel

private theorem C092_bound_11 : ∀ j : Fin 14, C092_digit 11 j < 5 := by decide +kernel

private theorem C092_bound_12 : ∀ j : Fin 14, C092_digit 12 j < 5 := by decide +kernel

private theorem C092_bound_13 : ∀ j : Fin 14, C092_digit 13 j < 5 := by decide +kernel

theorem C092_bound : ∀ i j : Fin 14, C092_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C092_bound_00 j
  · exact C092_bound_01 j
  · exact C092_bound_02 j
  · exact C092_bound_03 j
  · exact C092_bound_04 j
  · exact C092_bound_05 j
  · exact C092_bound_06 j
  · exact C092_bound_07 j
  · exact C092_bound_08 j
  · exact C092_bound_09 j
  · exact C092_bound_10 j
  · exact C092_bound_11 j
  · exact C092_bound_12 j
  · exact C092_bound_13 j

private theorem C092_row_00 : pack 256 (C092_digit 0)=C092_rowCode 0 := by decide +kernel

private theorem C092_row_01 : pack 256 (C092_digit 1)=C092_rowCode 1 := by decide +kernel

private theorem C092_row_02 : pack 256 (C092_digit 2)=C092_rowCode 2 := by decide +kernel

private theorem C092_row_03 : pack 256 (C092_digit 3)=C092_rowCode 3 := by decide +kernel

private theorem C092_row_04 : pack 256 (C092_digit 4)=C092_rowCode 4 := by decide +kernel

private theorem C092_row_05 : pack 256 (C092_digit 5)=C092_rowCode 5 := by decide +kernel

private theorem C092_row_06 : pack 256 (C092_digit 6)=C092_rowCode 6 := by decide +kernel

private theorem C092_row_07 : pack 256 (C092_digit 7)=C092_rowCode 7 := by decide +kernel

private theorem C092_row_08 : pack 256 (C092_digit 8)=C092_rowCode 8 := by decide +kernel

private theorem C092_row_09 : pack 256 (C092_digit 9)=C092_rowCode 9 := by decide +kernel

private theorem C092_row_10 : pack 256 (C092_digit 10)=C092_rowCode 10 := by decide +kernel

private theorem C092_row_11 : pack 256 (C092_digit 11)=C092_rowCode 11 := by decide +kernel

private theorem C092_row_12 : pack 256 (C092_digit 12)=C092_rowCode 12 := by decide +kernel

private theorem C092_row_13 : pack 256 (C092_digit 13)=C092_rowCode 13 := by decide +kernel

theorem C092_row_binding : ∀ i : Fin 14, pack 256 (C092_digit i)=C092_rowCode i := by
  intro i
  fin_cases i
  · exact C092_row_00
  · exact C092_row_01
  · exact C092_row_02
  · exact C092_row_03
  · exact C092_row_04
  · exact C092_row_05
  · exact C092_row_06
  · exact C092_row_07
  · exact C092_row_08
  · exact C092_row_09
  · exact C092_row_10
  · exact C092_row_11
  · exact C092_row_12
  · exact C092_row_13

private theorem C092_column_00 : reversePack 256 (fun j : Fin 14 => C092_digit j 0)=C092_columnCode 0 := by decide +kernel

private theorem C092_column_01 : reversePack 256 (fun j : Fin 14 => C092_digit j 1)=C092_columnCode 1 := by decide +kernel

private theorem C092_column_02 : reversePack 256 (fun j : Fin 14 => C092_digit j 2)=C092_columnCode 2 := by decide +kernel

private theorem C092_column_03 : reversePack 256 (fun j : Fin 14 => C092_digit j 3)=C092_columnCode 3 := by decide +kernel

private theorem C092_column_04 : reversePack 256 (fun j : Fin 14 => C092_digit j 4)=C092_columnCode 4 := by decide +kernel

private theorem C092_column_05 : reversePack 256 (fun j : Fin 14 => C092_digit j 5)=C092_columnCode 5 := by decide +kernel

private theorem C092_column_06 : reversePack 256 (fun j : Fin 14 => C092_digit j 6)=C092_columnCode 6 := by decide +kernel

private theorem C092_column_07 : reversePack 256 (fun j : Fin 14 => C092_digit j 7)=C092_columnCode 7 := by decide +kernel

private theorem C092_column_08 : reversePack 256 (fun j : Fin 14 => C092_digit j 8)=C092_columnCode 8 := by decide +kernel

private theorem C092_column_09 : reversePack 256 (fun j : Fin 14 => C092_digit j 9)=C092_columnCode 9 := by decide +kernel

private theorem C092_column_10 : reversePack 256 (fun j : Fin 14 => C092_digit j 10)=C092_columnCode 10 := by decide +kernel

private theorem C092_column_11 : reversePack 256 (fun j : Fin 14 => C092_digit j 11)=C092_columnCode 11 := by decide +kernel

private theorem C092_column_12 : reversePack 256 (fun j : Fin 14 => C092_digit j 12)=C092_columnCode 12 := by decide +kernel

private theorem C092_column_13 : reversePack 256 (fun j : Fin 14 => C092_digit j 13)=C092_columnCode 13 := by decide +kernel

theorem C092_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C092_digit j i)=C092_columnCode i := by
  intro i
  fin_cases i
  · exact C092_column_00
  · exact C092_column_01
  · exact C092_column_02
  · exact C092_column_03
  · exact C092_column_04
  · exact C092_column_05
  · exact C092_column_06
  · exact C092_column_07
  · exact C092_column_08
  · exact C092_column_09
  · exact C092_column_10
  · exact C092_column_11
  · exact C092_column_12
  · exact C092_column_13

def C092_data : PackedData 14 5 256 where
  raw := C092_digit
  digit_lt := C092_bound
  rowCode := C092_rowCode
  columnCode := C092_columnCode
  row_binding := C092_row_binding
  column_binding := C092_column_binding

def C093_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 567242260611
  | 1 => 2362439963236
  | 2 => 647505264898
  | 3 => 576776450723
  | 4 => 1101981057536
  | 5 => 1788908807394
  | 6 => 2212451431050
  | 7 => 1127431931492
  | 8 => 656610037964
  | 9 => 2220653888545
  | 10 => 1396005709922
  | 11 => 1823222277408
  | 12 => 1401773098760
  | 13 => 1169779082521
  | _ => 0

def C093_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 20282412026299751907895262970883
  | 1 => 60927699768120040640028428207104
  | 2 => 81447790213684256897130943480066
  | 3 => 40803127510014004431528998732032
  | 4 => 81130259821385877137361098506496
  | 5 => 1218444628635866794033668
  | 6 => 20599635374940957102915822289153
  | 7 => 40645288946079155279612113715970
  | 8 => 81129638419347494926043813381122
  | 9 => 61164142674734042821918101340418
  | 10 => 20362261590833807317190265995264
  | 11 => 238924854952454018605150044930
  | 12 => 20599946059450095669248308347392
  | 13 => 40724206424121030707493528994817
  | _ => 0

def C093_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 60847847781048513561025646297089
  | 1 => 81446861763358712883299454484996
  | 2 => 40566057166306167931467999674625
  | 3 => 61164761654198634652771683598337
  | 4 => 1208944554873861171052546
  | 5 => 40882662739760094028609890550275
  | 6 => 40644667562985508015526912262148
  | 7 => 81446864176525022665671392296962
  | 8 => 81209795036946563528869948948737
  | 9 => 20599324690486871102447679569924
  | 10 => 40882046187536894728878508082178
  | 11 => 318153017392788109140693352963
  | 12 => 80469729331297073624292459522
  | 13 => 20521334467974926602694652068098
  | _ => 0

def C093_digit (i j : Fin 14) : ℕ := packedDigit 3 (C093_lowColumnCode j) i.val

private theorem C093_bound_00 : ∀ j : Fin 14, C093_digit 0 j < 5 := by decide +kernel

private theorem C093_bound_01 : ∀ j : Fin 14, C093_digit 1 j < 5 := by decide +kernel

private theorem C093_bound_02 : ∀ j : Fin 14, C093_digit 2 j < 5 := by decide +kernel

private theorem C093_bound_03 : ∀ j : Fin 14, C093_digit 3 j < 5 := by decide +kernel

private theorem C093_bound_04 : ∀ j : Fin 14, C093_digit 4 j < 5 := by decide +kernel

private theorem C093_bound_05 : ∀ j : Fin 14, C093_digit 5 j < 5 := by decide +kernel

private theorem C093_bound_06 : ∀ j : Fin 14, C093_digit 6 j < 5 := by decide +kernel

private theorem C093_bound_07 : ∀ j : Fin 14, C093_digit 7 j < 5 := by decide +kernel

private theorem C093_bound_08 : ∀ j : Fin 14, C093_digit 8 j < 5 := by decide +kernel

private theorem C093_bound_09 : ∀ j : Fin 14, C093_digit 9 j < 5 := by decide +kernel

private theorem C093_bound_10 : ∀ j : Fin 14, C093_digit 10 j < 5 := by decide +kernel

private theorem C093_bound_11 : ∀ j : Fin 14, C093_digit 11 j < 5 := by decide +kernel

private theorem C093_bound_12 : ∀ j : Fin 14, C093_digit 12 j < 5 := by decide +kernel

private theorem C093_bound_13 : ∀ j : Fin 14, C093_digit 13 j < 5 := by decide +kernel

theorem C093_bound : ∀ i j : Fin 14, C093_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C093_bound_00 j
  · exact C093_bound_01 j
  · exact C093_bound_02 j
  · exact C093_bound_03 j
  · exact C093_bound_04 j
  · exact C093_bound_05 j
  · exact C093_bound_06 j
  · exact C093_bound_07 j
  · exact C093_bound_08 j
  · exact C093_bound_09 j
  · exact C093_bound_10 j
  · exact C093_bound_11 j
  · exact C093_bound_12 j
  · exact C093_bound_13 j

private theorem C093_row_00 : pack 256 (C093_digit 0)=C093_rowCode 0 := by decide +kernel

private theorem C093_row_01 : pack 256 (C093_digit 1)=C093_rowCode 1 := by decide +kernel

private theorem C093_row_02 : pack 256 (C093_digit 2)=C093_rowCode 2 := by decide +kernel

private theorem C093_row_03 : pack 256 (C093_digit 3)=C093_rowCode 3 := by decide +kernel

private theorem C093_row_04 : pack 256 (C093_digit 4)=C093_rowCode 4 := by decide +kernel

private theorem C093_row_05 : pack 256 (C093_digit 5)=C093_rowCode 5 := by decide +kernel

private theorem C093_row_06 : pack 256 (C093_digit 6)=C093_rowCode 6 := by decide +kernel

private theorem C093_row_07 : pack 256 (C093_digit 7)=C093_rowCode 7 := by decide +kernel

private theorem C093_row_08 : pack 256 (C093_digit 8)=C093_rowCode 8 := by decide +kernel

private theorem C093_row_09 : pack 256 (C093_digit 9)=C093_rowCode 9 := by decide +kernel

private theorem C093_row_10 : pack 256 (C093_digit 10)=C093_rowCode 10 := by decide +kernel

private theorem C093_row_11 : pack 256 (C093_digit 11)=C093_rowCode 11 := by decide +kernel

private theorem C093_row_12 : pack 256 (C093_digit 12)=C093_rowCode 12 := by decide +kernel

private theorem C093_row_13 : pack 256 (C093_digit 13)=C093_rowCode 13 := by decide +kernel

theorem C093_row_binding : ∀ i : Fin 14, pack 256 (C093_digit i)=C093_rowCode i := by
  intro i
  fin_cases i
  · exact C093_row_00
  · exact C093_row_01
  · exact C093_row_02
  · exact C093_row_03
  · exact C093_row_04
  · exact C093_row_05
  · exact C093_row_06
  · exact C093_row_07
  · exact C093_row_08
  · exact C093_row_09
  · exact C093_row_10
  · exact C093_row_11
  · exact C093_row_12
  · exact C093_row_13

private theorem C093_column_00 : reversePack 256 (fun j : Fin 14 => C093_digit j 0)=C093_columnCode 0 := by decide +kernel

private theorem C093_column_01 : reversePack 256 (fun j : Fin 14 => C093_digit j 1)=C093_columnCode 1 := by decide +kernel

private theorem C093_column_02 : reversePack 256 (fun j : Fin 14 => C093_digit j 2)=C093_columnCode 2 := by decide +kernel

private theorem C093_column_03 : reversePack 256 (fun j : Fin 14 => C093_digit j 3)=C093_columnCode 3 := by decide +kernel

private theorem C093_column_04 : reversePack 256 (fun j : Fin 14 => C093_digit j 4)=C093_columnCode 4 := by decide +kernel

private theorem C093_column_05 : reversePack 256 (fun j : Fin 14 => C093_digit j 5)=C093_columnCode 5 := by decide +kernel

private theorem C093_column_06 : reversePack 256 (fun j : Fin 14 => C093_digit j 6)=C093_columnCode 6 := by decide +kernel

private theorem C093_column_07 : reversePack 256 (fun j : Fin 14 => C093_digit j 7)=C093_columnCode 7 := by decide +kernel

private theorem C093_column_08 : reversePack 256 (fun j : Fin 14 => C093_digit j 8)=C093_columnCode 8 := by decide +kernel

private theorem C093_column_09 : reversePack 256 (fun j : Fin 14 => C093_digit j 9)=C093_columnCode 9 := by decide +kernel

private theorem C093_column_10 : reversePack 256 (fun j : Fin 14 => C093_digit j 10)=C093_columnCode 10 := by decide +kernel

private theorem C093_column_11 : reversePack 256 (fun j : Fin 14 => C093_digit j 11)=C093_columnCode 11 := by decide +kernel

private theorem C093_column_12 : reversePack 256 (fun j : Fin 14 => C093_digit j 12)=C093_columnCode 12 := by decide +kernel

private theorem C093_column_13 : reversePack 256 (fun j : Fin 14 => C093_digit j 13)=C093_columnCode 13 := by decide +kernel

theorem C093_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C093_digit j i)=C093_columnCode i := by
  intro i
  fin_cases i
  · exact C093_column_00
  · exact C093_column_01
  · exact C093_column_02
  · exact C093_column_03
  · exact C093_column_04
  · exact C093_column_05
  · exact C093_column_06
  · exact C093_column_07
  · exact C093_column_08
  · exact C093_column_09
  · exact C093_column_10
  · exact C093_column_11
  · exact C093_column_12
  · exact C093_column_13

def C093_data : PackedData 14 5 256 where
  raw := C093_digit
  digit_lt := C093_bound
  rowCode := C093_rowCode
  columnCode := C093_columnCode
  row_binding := C093_row_binding
  column_binding := C093_column_binding

def C094_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 853914794056
  | 1 => 690742102024
  | 2 => 166449678538
  | 3 => 568164950218
  | 4 => 2221087959242
  | 5 => 2212451431050
  | 6 => 656610037964
  | 7 => 2220653888545
  | 8 => 1788908807394
  | 9 => 1396005709922
  | 10 => 1127431931492
  | 11 => 1401773098760
  | 12 => 1169779082521
  | 13 => 1823222277408
  | _ => 0

def C094_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 79233007699242435698543951872
  | 1 => 81367637241826115932883431522561
  | 2 => 81447790218406551602794917462017
  | 3 => 40724207633065295938106056508420
  | 4 => 40881731866842313167313674698755
  | 5 => 4840499577162072028413955
  | 6 => 20362879347168369293582546437122
  | 7 => 81288405447774988385921286603522
  | 8 => 316912650112469921677220840193
  | 9 => 238922432304518063834364117506
  | 10 => 40644359291605714258657445872387
  | 11 => 81130570505858482782818112045059
  | 12 => 40645285328783250266863922446852
  | 13 => 61006306533355183580651431395585
  | _ => 0

def C094_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 79542497449948501255213220865
  | 1 => 79232998217831874218499768833
  | 2 => 40644980660569010878641281892864
  | 3 => 40644975834328768296228745248769
  | 4 => 40644980670013671789002754228228
  | 5 => 40644667562985508015526912262148
  | 6 => 81209795036946563528869948948737
  | 7 => 20599324690486871102447679569924
  | 8 => 40882662739760094028609890550275
  | 9 => 40882046187536894728878508082178
  | 10 => 81446864176525022665671392296962
  | 11 => 80469729331297073624292459522
  | 12 => 20521334467974926602694652068098
  | 13 => 318153017392788109140693352963
  | _ => 0

def C094_digit (i j : Fin 14) : ℕ := packedDigit 3 (C094_lowColumnCode j) i.val

private theorem C094_bound_00 : ∀ j : Fin 14, C094_digit 0 j < 5 := by decide +kernel

private theorem C094_bound_01 : ∀ j : Fin 14, C094_digit 1 j < 5 := by decide +kernel

private theorem C094_bound_02 : ∀ j : Fin 14, C094_digit 2 j < 5 := by decide +kernel

private theorem C094_bound_03 : ∀ j : Fin 14, C094_digit 3 j < 5 := by decide +kernel

private theorem C094_bound_04 : ∀ j : Fin 14, C094_digit 4 j < 5 := by decide +kernel

private theorem C094_bound_05 : ∀ j : Fin 14, C094_digit 5 j < 5 := by decide +kernel

private theorem C094_bound_06 : ∀ j : Fin 14, C094_digit 6 j < 5 := by decide +kernel

private theorem C094_bound_07 : ∀ j : Fin 14, C094_digit 7 j < 5 := by decide +kernel

private theorem C094_bound_08 : ∀ j : Fin 14, C094_digit 8 j < 5 := by decide +kernel

private theorem C094_bound_09 : ∀ j : Fin 14, C094_digit 9 j < 5 := by decide +kernel

private theorem C094_bound_10 : ∀ j : Fin 14, C094_digit 10 j < 5 := by decide +kernel

private theorem C094_bound_11 : ∀ j : Fin 14, C094_digit 11 j < 5 := by decide +kernel

private theorem C094_bound_12 : ∀ j : Fin 14, C094_digit 12 j < 5 := by decide +kernel

private theorem C094_bound_13 : ∀ j : Fin 14, C094_digit 13 j < 5 := by decide +kernel

theorem C094_bound : ∀ i j : Fin 14, C094_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C094_bound_00 j
  · exact C094_bound_01 j
  · exact C094_bound_02 j
  · exact C094_bound_03 j
  · exact C094_bound_04 j
  · exact C094_bound_05 j
  · exact C094_bound_06 j
  · exact C094_bound_07 j
  · exact C094_bound_08 j
  · exact C094_bound_09 j
  · exact C094_bound_10 j
  · exact C094_bound_11 j
  · exact C094_bound_12 j
  · exact C094_bound_13 j

private theorem C094_row_00 : pack 256 (C094_digit 0)=C094_rowCode 0 := by decide +kernel

private theorem C094_row_01 : pack 256 (C094_digit 1)=C094_rowCode 1 := by decide +kernel

private theorem C094_row_02 : pack 256 (C094_digit 2)=C094_rowCode 2 := by decide +kernel

private theorem C094_row_03 : pack 256 (C094_digit 3)=C094_rowCode 3 := by decide +kernel

private theorem C094_row_04 : pack 256 (C094_digit 4)=C094_rowCode 4 := by decide +kernel

private theorem C094_row_05 : pack 256 (C094_digit 5)=C094_rowCode 5 := by decide +kernel

private theorem C094_row_06 : pack 256 (C094_digit 6)=C094_rowCode 6 := by decide +kernel

private theorem C094_row_07 : pack 256 (C094_digit 7)=C094_rowCode 7 := by decide +kernel

private theorem C094_row_08 : pack 256 (C094_digit 8)=C094_rowCode 8 := by decide +kernel

private theorem C094_row_09 : pack 256 (C094_digit 9)=C094_rowCode 9 := by decide +kernel

private theorem C094_row_10 : pack 256 (C094_digit 10)=C094_rowCode 10 := by decide +kernel

private theorem C094_row_11 : pack 256 (C094_digit 11)=C094_rowCode 11 := by decide +kernel

private theorem C094_row_12 : pack 256 (C094_digit 12)=C094_rowCode 12 := by decide +kernel

private theorem C094_row_13 : pack 256 (C094_digit 13)=C094_rowCode 13 := by decide +kernel

theorem C094_row_binding : ∀ i : Fin 14, pack 256 (C094_digit i)=C094_rowCode i := by
  intro i
  fin_cases i
  · exact C094_row_00
  · exact C094_row_01
  · exact C094_row_02
  · exact C094_row_03
  · exact C094_row_04
  · exact C094_row_05
  · exact C094_row_06
  · exact C094_row_07
  · exact C094_row_08
  · exact C094_row_09
  · exact C094_row_10
  · exact C094_row_11
  · exact C094_row_12
  · exact C094_row_13

private theorem C094_column_00 : reversePack 256 (fun j : Fin 14 => C094_digit j 0)=C094_columnCode 0 := by decide +kernel

private theorem C094_column_01 : reversePack 256 (fun j : Fin 14 => C094_digit j 1)=C094_columnCode 1 := by decide +kernel

private theorem C094_column_02 : reversePack 256 (fun j : Fin 14 => C094_digit j 2)=C094_columnCode 2 := by decide +kernel

private theorem C094_column_03 : reversePack 256 (fun j : Fin 14 => C094_digit j 3)=C094_columnCode 3 := by decide +kernel

private theorem C094_column_04 : reversePack 256 (fun j : Fin 14 => C094_digit j 4)=C094_columnCode 4 := by decide +kernel

private theorem C094_column_05 : reversePack 256 (fun j : Fin 14 => C094_digit j 5)=C094_columnCode 5 := by decide +kernel

private theorem C094_column_06 : reversePack 256 (fun j : Fin 14 => C094_digit j 6)=C094_columnCode 6 := by decide +kernel

private theorem C094_column_07 : reversePack 256 (fun j : Fin 14 => C094_digit j 7)=C094_columnCode 7 := by decide +kernel

private theorem C094_column_08 : reversePack 256 (fun j : Fin 14 => C094_digit j 8)=C094_columnCode 8 := by decide +kernel

private theorem C094_column_09 : reversePack 256 (fun j : Fin 14 => C094_digit j 9)=C094_columnCode 9 := by decide +kernel

private theorem C094_column_10 : reversePack 256 (fun j : Fin 14 => C094_digit j 10)=C094_columnCode 10 := by decide +kernel

private theorem C094_column_11 : reversePack 256 (fun j : Fin 14 => C094_digit j 11)=C094_columnCode 11 := by decide +kernel

private theorem C094_column_12 : reversePack 256 (fun j : Fin 14 => C094_digit j 12)=C094_columnCode 12 := by decide +kernel

private theorem C094_column_13 : reversePack 256 (fun j : Fin 14 => C094_digit j 13)=C094_columnCode 13 := by decide +kernel

theorem C094_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C094_digit j i)=C094_columnCode i := by
  intro i
  fin_cases i
  · exact C094_column_00
  · exact C094_column_01
  · exact C094_column_02
  · exact C094_column_03
  · exact C094_column_04
  · exact C094_column_05
  · exact C094_column_06
  · exact C094_column_07
  · exact C094_column_08
  · exact C094_column_09
  · exact C094_column_10
  · exact C094_column_11
  · exact C094_column_12
  · exact C094_column_13

def C094_data : PackedData 14 5 256 where
  raw := C094_digit
  digit_lt := C094_bound
  rowCode := C094_rowCode
  columnCode := C094_columnCode
  row_binding := C094_row_binding
  column_binding := C094_column_binding

end SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedCaches10
