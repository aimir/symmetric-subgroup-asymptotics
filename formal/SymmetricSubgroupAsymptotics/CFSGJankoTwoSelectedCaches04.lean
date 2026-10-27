import SymmetricSubgroupAsymptotics.MatrixKroneckerProductReflection
import Mathlib.Tactic.FinCases

/-! Literal14/F5 selected caches; digit bounds and both pack bindings are independently kernel checked. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedCaches04
open MatrixKroneckerProductReflection MatrixKroneckerDotReflection
open MatrixNaturalRowDotReflection SmallNaturalMatrixProductReflection

def C027_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 579173459992
  | 1 => 1875343675424
  | 2 => 2434215747672
  | 3 => 1797444707619
  | 4 => 1197832975904
  | 5 => 2286399665307
  | 6 => 618664366362
  | 7 => 1747415348899
  | 8 => 1875879444692
  | 9 => 158048207385
  | 10 => 1326526834834
  | 11 => 1941467906585
  | 12 => 294208443425
  | 13 => 563085678153
  | _ => 0

def C027_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 20361949673823765534063005270016
  | 1 => 20600253140794113053659169489923
  | 2 => 20282412021558795128713802481664
  | 3 => 61005999461419222408477966073860
  | 4 => 20362878143020328736416006799618
  | 5 => 60927078361359293070633303343875
  | 6 => 20599324681005388483377859134467
  | 7 => 81210105740271597783932106703107
  | 8 => 40564822853025750815111922189057
  | 9 => 60847541927464874401240453219331
  | 10 => 81288098380635325069588225524227
  | 11 => 20441487326033323647410886607363
  | 12 => 318154226373947112669873111808
  | 13 => 20283340476588330379296681231105
  | _ => 0

def C027_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 237689332746361687577240731649
  | 1 => 316912654835052580631826531075
  | 2 => 237993982016083426137488950020
  | 3 => 61165381828403282602491744682499
  | 4 => 316916291020207350972628009218
  | 5 => 61085534700610116744122936197380
  | 6 => 40803741639644751835813919064321
  | 7 => 61164764072050344813732787585283
  | 8 => 81289023213572587366508119851779
  | 9 => 20520095319009893946851036627456
  | 10 => 40723899347536561525596971205378
  | 11 => 20520095319046643596887259743235
  | 12 => 20599324676301468742374293373952
  | 13 => 20361950882730994851293738106881
  | _ => 0

def C027_digit (i j : Fin 14) : ℕ := packedDigit 3 (C027_lowColumnCode j) i.val

private theorem C027_bound_00 : ∀ j : Fin 14, C027_digit 0 j < 5 := by decide +kernel

private theorem C027_bound_01 : ∀ j : Fin 14, C027_digit 1 j < 5 := by decide +kernel

private theorem C027_bound_02 : ∀ j : Fin 14, C027_digit 2 j < 5 := by decide +kernel

private theorem C027_bound_03 : ∀ j : Fin 14, C027_digit 3 j < 5 := by decide +kernel

private theorem C027_bound_04 : ∀ j : Fin 14, C027_digit 4 j < 5 := by decide +kernel

private theorem C027_bound_05 : ∀ j : Fin 14, C027_digit 5 j < 5 := by decide +kernel

private theorem C027_bound_06 : ∀ j : Fin 14, C027_digit 6 j < 5 := by decide +kernel

private theorem C027_bound_07 : ∀ j : Fin 14, C027_digit 7 j < 5 := by decide +kernel

private theorem C027_bound_08 : ∀ j : Fin 14, C027_digit 8 j < 5 := by decide +kernel

private theorem C027_bound_09 : ∀ j : Fin 14, C027_digit 9 j < 5 := by decide +kernel

private theorem C027_bound_10 : ∀ j : Fin 14, C027_digit 10 j < 5 := by decide +kernel

private theorem C027_bound_11 : ∀ j : Fin 14, C027_digit 11 j < 5 := by decide +kernel

private theorem C027_bound_12 : ∀ j : Fin 14, C027_digit 12 j < 5 := by decide +kernel

private theorem C027_bound_13 : ∀ j : Fin 14, C027_digit 13 j < 5 := by decide +kernel

theorem C027_bound : ∀ i j : Fin 14, C027_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C027_bound_00 j
  · exact C027_bound_01 j
  · exact C027_bound_02 j
  · exact C027_bound_03 j
  · exact C027_bound_04 j
  · exact C027_bound_05 j
  · exact C027_bound_06 j
  · exact C027_bound_07 j
  · exact C027_bound_08 j
  · exact C027_bound_09 j
  · exact C027_bound_10 j
  · exact C027_bound_11 j
  · exact C027_bound_12 j
  · exact C027_bound_13 j

private theorem C027_row_00 : pack 256 (C027_digit 0)=C027_rowCode 0 := by decide +kernel

private theorem C027_row_01 : pack 256 (C027_digit 1)=C027_rowCode 1 := by decide +kernel

private theorem C027_row_02 : pack 256 (C027_digit 2)=C027_rowCode 2 := by decide +kernel

private theorem C027_row_03 : pack 256 (C027_digit 3)=C027_rowCode 3 := by decide +kernel

private theorem C027_row_04 : pack 256 (C027_digit 4)=C027_rowCode 4 := by decide +kernel

private theorem C027_row_05 : pack 256 (C027_digit 5)=C027_rowCode 5 := by decide +kernel

private theorem C027_row_06 : pack 256 (C027_digit 6)=C027_rowCode 6 := by decide +kernel

private theorem C027_row_07 : pack 256 (C027_digit 7)=C027_rowCode 7 := by decide +kernel

private theorem C027_row_08 : pack 256 (C027_digit 8)=C027_rowCode 8 := by decide +kernel

private theorem C027_row_09 : pack 256 (C027_digit 9)=C027_rowCode 9 := by decide +kernel

private theorem C027_row_10 : pack 256 (C027_digit 10)=C027_rowCode 10 := by decide +kernel

private theorem C027_row_11 : pack 256 (C027_digit 11)=C027_rowCode 11 := by decide +kernel

private theorem C027_row_12 : pack 256 (C027_digit 12)=C027_rowCode 12 := by decide +kernel

private theorem C027_row_13 : pack 256 (C027_digit 13)=C027_rowCode 13 := by decide +kernel

theorem C027_row_binding : ∀ i : Fin 14, pack 256 (C027_digit i)=C027_rowCode i := by
  intro i
  fin_cases i
  · exact C027_row_00
  · exact C027_row_01
  · exact C027_row_02
  · exact C027_row_03
  · exact C027_row_04
  · exact C027_row_05
  · exact C027_row_06
  · exact C027_row_07
  · exact C027_row_08
  · exact C027_row_09
  · exact C027_row_10
  · exact C027_row_11
  · exact C027_row_12
  · exact C027_row_13

private theorem C027_column_00 : reversePack 256 (fun j : Fin 14 => C027_digit j 0)=C027_columnCode 0 := by decide +kernel

private theorem C027_column_01 : reversePack 256 (fun j : Fin 14 => C027_digit j 1)=C027_columnCode 1 := by decide +kernel

private theorem C027_column_02 : reversePack 256 (fun j : Fin 14 => C027_digit j 2)=C027_columnCode 2 := by decide +kernel

private theorem C027_column_03 : reversePack 256 (fun j : Fin 14 => C027_digit j 3)=C027_columnCode 3 := by decide +kernel

private theorem C027_column_04 : reversePack 256 (fun j : Fin 14 => C027_digit j 4)=C027_columnCode 4 := by decide +kernel

private theorem C027_column_05 : reversePack 256 (fun j : Fin 14 => C027_digit j 5)=C027_columnCode 5 := by decide +kernel

private theorem C027_column_06 : reversePack 256 (fun j : Fin 14 => C027_digit j 6)=C027_columnCode 6 := by decide +kernel

private theorem C027_column_07 : reversePack 256 (fun j : Fin 14 => C027_digit j 7)=C027_columnCode 7 := by decide +kernel

private theorem C027_column_08 : reversePack 256 (fun j : Fin 14 => C027_digit j 8)=C027_columnCode 8 := by decide +kernel

private theorem C027_column_09 : reversePack 256 (fun j : Fin 14 => C027_digit j 9)=C027_columnCode 9 := by decide +kernel

private theorem C027_column_10 : reversePack 256 (fun j : Fin 14 => C027_digit j 10)=C027_columnCode 10 := by decide +kernel

private theorem C027_column_11 : reversePack 256 (fun j : Fin 14 => C027_digit j 11)=C027_columnCode 11 := by decide +kernel

private theorem C027_column_12 : reversePack 256 (fun j : Fin 14 => C027_digit j 12)=C027_columnCode 12 := by decide +kernel

private theorem C027_column_13 : reversePack 256 (fun j : Fin 14 => C027_digit j 13)=C027_columnCode 13 := by decide +kernel

theorem C027_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C027_digit j i)=C027_columnCode i := by
  intro i
  fin_cases i
  · exact C027_column_00
  · exact C027_column_01
  · exact C027_column_02
  · exact C027_column_03
  · exact C027_column_04
  · exact C027_column_05
  · exact C027_column_06
  · exact C027_column_07
  · exact C027_column_08
  · exact C027_column_09
  · exact C027_column_10
  · exact C027_column_11
  · exact C027_column_12
  · exact C027_column_13

def C027_data : PackedData 14 5 256 where
  raw := C027_digit
  digit_lt := C027_bound
  rowCode := C027_rowCode
  columnCode := C027_columnCode
  row_binding := C027_row_binding
  column_binding := C027_column_binding

def C029_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 653445936739
  | 1 => 622288539680
  | 2 => 219316496010
  | 3 => 1868319564866
  | 4 => 2484941492488
  | 5 => 176669467427
  | 6 => 1395754139
  | 7 => 224601949187
  | 8 => 6391307
  | 9 => 1099578736640
  | 10 => 304306264321
  | 11 => 1738675926676
  | 12 => 218173608530
  | 13 => 106703500938
  | _ => 0

def C029_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 40724514681352531770712405442563
  | 1 => 20441484898718289382172769977348
  | 2 => 40644671175540526901507391619073
  | 3 => 60927390264257503014616874287107
  | 4 => 60927386637424847491850150478083
  | 5 => 81288716127562049544215358079747
  | 6 => 20441489734403409608475494449666
  | 7 => 79537647579570313745540448771
  | 8 => 317224571808200875594487956228
  | 9 => 60927079570266449768410899416068
  | 10 => 61085845380304799507191802626816
  | 11 => 81209489173918191686997956952068
  | 12 => 20520408411907779415311674179841
  | 13 => 928464474197000962694971649
  | _ => 0

def C029_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 61164454587021933456030475485441
  | 1 => 316912654834908746918744031489
  | 2 => 40644669976059584363398997017344
  | 3 => 40565131119683394547749717345027
  | 4 => 80466107349919352022687089668
  | 5 => 61165380619495982354696507752960
  | 6 => 61085534686424714951397583355904
  | 7 => 60847231247751745461428764672768
  | 8 => 60926460600302075529968880713728
  | 9 => 4398046511106
  | 10 => 20283652384153782466344023950336
  | 11 => 81288717350636449239528626061571
  | 12 => 40723586231026914854861998719744
  | 13 => 40644669980855665202023767474432
  | _ => 0

def C029_digit (i j : Fin 14) : ℕ := packedDigit 3 (C029_lowColumnCode j) i.val

private theorem C029_bound_00 : ∀ j : Fin 14, C029_digit 0 j < 5 := by decide +kernel

private theorem C029_bound_01 : ∀ j : Fin 14, C029_digit 1 j < 5 := by decide +kernel

private theorem C029_bound_02 : ∀ j : Fin 14, C029_digit 2 j < 5 := by decide +kernel

private theorem C029_bound_03 : ∀ j : Fin 14, C029_digit 3 j < 5 := by decide +kernel

private theorem C029_bound_04 : ∀ j : Fin 14, C029_digit 4 j < 5 := by decide +kernel

private theorem C029_bound_05 : ∀ j : Fin 14, C029_digit 5 j < 5 := by decide +kernel

private theorem C029_bound_06 : ∀ j : Fin 14, C029_digit 6 j < 5 := by decide +kernel

private theorem C029_bound_07 : ∀ j : Fin 14, C029_digit 7 j < 5 := by decide +kernel

private theorem C029_bound_08 : ∀ j : Fin 14, C029_digit 8 j < 5 := by decide +kernel

private theorem C029_bound_09 : ∀ j : Fin 14, C029_digit 9 j < 5 := by decide +kernel

private theorem C029_bound_10 : ∀ j : Fin 14, C029_digit 10 j < 5 := by decide +kernel

private theorem C029_bound_11 : ∀ j : Fin 14, C029_digit 11 j < 5 := by decide +kernel

private theorem C029_bound_12 : ∀ j : Fin 14, C029_digit 12 j < 5 := by decide +kernel

private theorem C029_bound_13 : ∀ j : Fin 14, C029_digit 13 j < 5 := by decide +kernel

theorem C029_bound : ∀ i j : Fin 14, C029_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C029_bound_00 j
  · exact C029_bound_01 j
  · exact C029_bound_02 j
  · exact C029_bound_03 j
  · exact C029_bound_04 j
  · exact C029_bound_05 j
  · exact C029_bound_06 j
  · exact C029_bound_07 j
  · exact C029_bound_08 j
  · exact C029_bound_09 j
  · exact C029_bound_10 j
  · exact C029_bound_11 j
  · exact C029_bound_12 j
  · exact C029_bound_13 j

private theorem C029_row_00 : pack 256 (C029_digit 0)=C029_rowCode 0 := by decide +kernel

private theorem C029_row_01 : pack 256 (C029_digit 1)=C029_rowCode 1 := by decide +kernel

private theorem C029_row_02 : pack 256 (C029_digit 2)=C029_rowCode 2 := by decide +kernel

private theorem C029_row_03 : pack 256 (C029_digit 3)=C029_rowCode 3 := by decide +kernel

private theorem C029_row_04 : pack 256 (C029_digit 4)=C029_rowCode 4 := by decide +kernel

private theorem C029_row_05 : pack 256 (C029_digit 5)=C029_rowCode 5 := by decide +kernel

private theorem C029_row_06 : pack 256 (C029_digit 6)=C029_rowCode 6 := by decide +kernel

private theorem C029_row_07 : pack 256 (C029_digit 7)=C029_rowCode 7 := by decide +kernel

private theorem C029_row_08 : pack 256 (C029_digit 8)=C029_rowCode 8 := by decide +kernel

private theorem C029_row_09 : pack 256 (C029_digit 9)=C029_rowCode 9 := by decide +kernel

private theorem C029_row_10 : pack 256 (C029_digit 10)=C029_rowCode 10 := by decide +kernel

private theorem C029_row_11 : pack 256 (C029_digit 11)=C029_rowCode 11 := by decide +kernel

private theorem C029_row_12 : pack 256 (C029_digit 12)=C029_rowCode 12 := by decide +kernel

private theorem C029_row_13 : pack 256 (C029_digit 13)=C029_rowCode 13 := by decide +kernel

theorem C029_row_binding : ∀ i : Fin 14, pack 256 (C029_digit i)=C029_rowCode i := by
  intro i
  fin_cases i
  · exact C029_row_00
  · exact C029_row_01
  · exact C029_row_02
  · exact C029_row_03
  · exact C029_row_04
  · exact C029_row_05
  · exact C029_row_06
  · exact C029_row_07
  · exact C029_row_08
  · exact C029_row_09
  · exact C029_row_10
  · exact C029_row_11
  · exact C029_row_12
  · exact C029_row_13

private theorem C029_column_00 : reversePack 256 (fun j : Fin 14 => C029_digit j 0)=C029_columnCode 0 := by decide +kernel

private theorem C029_column_01 : reversePack 256 (fun j : Fin 14 => C029_digit j 1)=C029_columnCode 1 := by decide +kernel

private theorem C029_column_02 : reversePack 256 (fun j : Fin 14 => C029_digit j 2)=C029_columnCode 2 := by decide +kernel

private theorem C029_column_03 : reversePack 256 (fun j : Fin 14 => C029_digit j 3)=C029_columnCode 3 := by decide +kernel

private theorem C029_column_04 : reversePack 256 (fun j : Fin 14 => C029_digit j 4)=C029_columnCode 4 := by decide +kernel

private theorem C029_column_05 : reversePack 256 (fun j : Fin 14 => C029_digit j 5)=C029_columnCode 5 := by decide +kernel

private theorem C029_column_06 : reversePack 256 (fun j : Fin 14 => C029_digit j 6)=C029_columnCode 6 := by decide +kernel

private theorem C029_column_07 : reversePack 256 (fun j : Fin 14 => C029_digit j 7)=C029_columnCode 7 := by decide +kernel

private theorem C029_column_08 : reversePack 256 (fun j : Fin 14 => C029_digit j 8)=C029_columnCode 8 := by decide +kernel

private theorem C029_column_09 : reversePack 256 (fun j : Fin 14 => C029_digit j 9)=C029_columnCode 9 := by decide +kernel

private theorem C029_column_10 : reversePack 256 (fun j : Fin 14 => C029_digit j 10)=C029_columnCode 10 := by decide +kernel

private theorem C029_column_11 : reversePack 256 (fun j : Fin 14 => C029_digit j 11)=C029_columnCode 11 := by decide +kernel

private theorem C029_column_12 : reversePack 256 (fun j : Fin 14 => C029_digit j 12)=C029_columnCode 12 := by decide +kernel

private theorem C029_column_13 : reversePack 256 (fun j : Fin 14 => C029_digit j 13)=C029_columnCode 13 := by decide +kernel

theorem C029_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C029_digit j i)=C029_columnCode i := by
  intro i
  fin_cases i
  · exact C029_column_00
  · exact C029_column_01
  · exact C029_column_02
  · exact C029_column_03
  · exact C029_column_04
  · exact C029_column_05
  · exact C029_column_06
  · exact C029_column_07
  · exact C029_column_08
  · exact C029_column_09
  · exact C029_column_10
  · exact C029_column_11
  · exact C029_column_12
  · exact C029_column_13

def C029_data : PackedData 14 5 256 where
  raw := C029_digit
  digit_lt := C029_bound
  rowCode := C029_rowCode
  columnCode := C029_columnCode
  row_binding := C029_row_binding
  column_binding := C029_column_binding

def C030_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 842225715274
  | 1 => 312650044707
  | 2 => 26072847952
  | 3 => 236813305377
  | 4 => 1875227186336
  | 5 => 549791826068
  | 6 => 155057390744
  | 7 => 1392777773770
  | 8 => 2358110077091
  | 9 => 2226981511428
  | 10 => 288172132419
  | 11 => 166909330515
  | 12 => 717433733712
  | 13 => 1688510014113
  | _ => 0

def C030_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 20283341704403543586326798402306
  | 1 => 81288713709728712941643619238913
  | 2 => 40644358082679822302751626429441
  | 3 => 20362261571888928530747575435780
  | 4 => 40566061992564712859100743008512
  | 5 => 81447792640925504469739581211137
  | 6 => 40566058375231771090740572324100
  | 7 => 238926068563530456282504889092
  | 8 => 61006923085504452346356657423104
  | 9 => 81209798658946388558581877309699
  | 10 => 81447484364915073539522877719296
  | 11 => 81368252580308895973308010529794
  | 12 => 159080130788632105327695758340
  | 13 => 60926456992432672633509189255169
  | _ => 0

def C030_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 40644361690549441089436123268097
  | 1 => 61165381823662326108088091018240
  | 2 => 158769441538463579596747112448
  | 3 => 20599325899375869007260404613888
  | 4 => 317534042650706320000538510083
  | 5 => 81288713709710265634602709155841
  | 6 => 238305875414147273457353753088
  | 7 => 40644977052736213800695164437506
  | 8 => 61164760449921466039361450672644
  | 9 => 81130876364127882606950752649220
  | 10 => 60847543150612990141158807110656
  | 11 => 61005997057808542789816375509504
  | 12 => 158767019037957457808141255169
  | 13 => 20599942442172854139626037968899
  | _ => 0

def C030_digit (i j : Fin 14) : ℕ := packedDigit 3 (C030_lowColumnCode j) i.val

private theorem C030_bound_00 : ∀ j : Fin 14, C030_digit 0 j < 5 := by decide +kernel

private theorem C030_bound_01 : ∀ j : Fin 14, C030_digit 1 j < 5 := by decide +kernel

private theorem C030_bound_02 : ∀ j : Fin 14, C030_digit 2 j < 5 := by decide +kernel

private theorem C030_bound_03 : ∀ j : Fin 14, C030_digit 3 j < 5 := by decide +kernel

private theorem C030_bound_04 : ∀ j : Fin 14, C030_digit 4 j < 5 := by decide +kernel

private theorem C030_bound_05 : ∀ j : Fin 14, C030_digit 5 j < 5 := by decide +kernel

private theorem C030_bound_06 : ∀ j : Fin 14, C030_digit 6 j < 5 := by decide +kernel

private theorem C030_bound_07 : ∀ j : Fin 14, C030_digit 7 j < 5 := by decide +kernel

private theorem C030_bound_08 : ∀ j : Fin 14, C030_digit 8 j < 5 := by decide +kernel

private theorem C030_bound_09 : ∀ j : Fin 14, C030_digit 9 j < 5 := by decide +kernel

private theorem C030_bound_10 : ∀ j : Fin 14, C030_digit 10 j < 5 := by decide +kernel

private theorem C030_bound_11 : ∀ j : Fin 14, C030_digit 11 j < 5 := by decide +kernel

private theorem C030_bound_12 : ∀ j : Fin 14, C030_digit 12 j < 5 := by decide +kernel

private theorem C030_bound_13 : ∀ j : Fin 14, C030_digit 13 j < 5 := by decide +kernel

theorem C030_bound : ∀ i j : Fin 14, C030_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C030_bound_00 j
  · exact C030_bound_01 j
  · exact C030_bound_02 j
  · exact C030_bound_03 j
  · exact C030_bound_04 j
  · exact C030_bound_05 j
  · exact C030_bound_06 j
  · exact C030_bound_07 j
  · exact C030_bound_08 j
  · exact C030_bound_09 j
  · exact C030_bound_10 j
  · exact C030_bound_11 j
  · exact C030_bound_12 j
  · exact C030_bound_13 j

private theorem C030_row_00 : pack 256 (C030_digit 0)=C030_rowCode 0 := by decide +kernel

private theorem C030_row_01 : pack 256 (C030_digit 1)=C030_rowCode 1 := by decide +kernel

private theorem C030_row_02 : pack 256 (C030_digit 2)=C030_rowCode 2 := by decide +kernel

private theorem C030_row_03 : pack 256 (C030_digit 3)=C030_rowCode 3 := by decide +kernel

private theorem C030_row_04 : pack 256 (C030_digit 4)=C030_rowCode 4 := by decide +kernel

private theorem C030_row_05 : pack 256 (C030_digit 5)=C030_rowCode 5 := by decide +kernel

private theorem C030_row_06 : pack 256 (C030_digit 6)=C030_rowCode 6 := by decide +kernel

private theorem C030_row_07 : pack 256 (C030_digit 7)=C030_rowCode 7 := by decide +kernel

private theorem C030_row_08 : pack 256 (C030_digit 8)=C030_rowCode 8 := by decide +kernel

private theorem C030_row_09 : pack 256 (C030_digit 9)=C030_rowCode 9 := by decide +kernel

private theorem C030_row_10 : pack 256 (C030_digit 10)=C030_rowCode 10 := by decide +kernel

private theorem C030_row_11 : pack 256 (C030_digit 11)=C030_rowCode 11 := by decide +kernel

private theorem C030_row_12 : pack 256 (C030_digit 12)=C030_rowCode 12 := by decide +kernel

private theorem C030_row_13 : pack 256 (C030_digit 13)=C030_rowCode 13 := by decide +kernel

theorem C030_row_binding : ∀ i : Fin 14, pack 256 (C030_digit i)=C030_rowCode i := by
  intro i
  fin_cases i
  · exact C030_row_00
  · exact C030_row_01
  · exact C030_row_02
  · exact C030_row_03
  · exact C030_row_04
  · exact C030_row_05
  · exact C030_row_06
  · exact C030_row_07
  · exact C030_row_08
  · exact C030_row_09
  · exact C030_row_10
  · exact C030_row_11
  · exact C030_row_12
  · exact C030_row_13

private theorem C030_column_00 : reversePack 256 (fun j : Fin 14 => C030_digit j 0)=C030_columnCode 0 := by decide +kernel

private theorem C030_column_01 : reversePack 256 (fun j : Fin 14 => C030_digit j 1)=C030_columnCode 1 := by decide +kernel

private theorem C030_column_02 : reversePack 256 (fun j : Fin 14 => C030_digit j 2)=C030_columnCode 2 := by decide +kernel

private theorem C030_column_03 : reversePack 256 (fun j : Fin 14 => C030_digit j 3)=C030_columnCode 3 := by decide +kernel

private theorem C030_column_04 : reversePack 256 (fun j : Fin 14 => C030_digit j 4)=C030_columnCode 4 := by decide +kernel

private theorem C030_column_05 : reversePack 256 (fun j : Fin 14 => C030_digit j 5)=C030_columnCode 5 := by decide +kernel

private theorem C030_column_06 : reversePack 256 (fun j : Fin 14 => C030_digit j 6)=C030_columnCode 6 := by decide +kernel

private theorem C030_column_07 : reversePack 256 (fun j : Fin 14 => C030_digit j 7)=C030_columnCode 7 := by decide +kernel

private theorem C030_column_08 : reversePack 256 (fun j : Fin 14 => C030_digit j 8)=C030_columnCode 8 := by decide +kernel

private theorem C030_column_09 : reversePack 256 (fun j : Fin 14 => C030_digit j 9)=C030_columnCode 9 := by decide +kernel

private theorem C030_column_10 : reversePack 256 (fun j : Fin 14 => C030_digit j 10)=C030_columnCode 10 := by decide +kernel

private theorem C030_column_11 : reversePack 256 (fun j : Fin 14 => C030_digit j 11)=C030_columnCode 11 := by decide +kernel

private theorem C030_column_12 : reversePack 256 (fun j : Fin 14 => C030_digit j 12)=C030_columnCode 12 := by decide +kernel

private theorem C030_column_13 : reversePack 256 (fun j : Fin 14 => C030_digit j 13)=C030_columnCode 13 := by decide +kernel

theorem C030_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C030_digit j i)=C030_columnCode i := by
  intro i
  fin_cases i
  · exact C030_column_00
  · exact C030_column_01
  · exact C030_column_02
  · exact C030_column_03
  · exact C030_column_04
  · exact C030_column_05
  · exact C030_column_06
  · exact C030_column_07
  · exact C030_column_08
  · exact C030_column_09
  · exact C030_column_10
  · exact C030_column_11
  · exact C030_column_12
  · exact C030_column_13

def C030_data : PackedData 14 5 256 where
  raw := C030_digit
  digit_lt := C030_bound
  rowCode := C030_rowCode
  columnCode := C030_columnCode
  row_binding := C030_row_binding
  column_binding := C030_column_binding

def C031_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 1875349483547
  | 1 => 285918380571
  | 2 => 1237392176866
  | 3 => 837688602785
  | 4 => 714613528274
  | 5 => 1403689476740
  | 6 => 2365992485956
  | 7 => 1237241145571
  | 8 => 844284662786
  | 9 => 825225417315
  | 10 => 1745267767051
  | 11 => 137640810753
  | 12 => 1324096178312
  | 13 => 1403701512291
  | _ => 0

def C031_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 60847541936946501700643031483139
  | 1 => 81208867804936519809875113673475
  | 2 => 20442108709145345877264614752256
  | 3 => 81447792636240032035781170364672
  | 4 => 81446864181191977705354136060931
  | 5 => 40564820421007083353703740342276
  | 6 => 159080135510998308917042480130
  | 7 => 20440865938161969952991243010052
  | 8 => 61006925508096976297193839395331
  | 9 => 40644360500531390037374498177540
  | 10 => 60926458182431989559939718709762
  | 11 => 61005688762797893126800151675138
  | 12 => 81367943100058334603654413288451
  | 13 => 40723279163850286837203787186179
  | _ => 0

def C031_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 61084913312738835953929890693891
  | 1 => 61084914526313378063313939792896
  | 2 => 40882663953408496297804163973634
  | 3 => 20599941237950810428967303054337
  | 4 => 40724207618898197053546602627585
  | 5 => 81130258603052362160336718201858
  | 6 => 81129950336357680540680905228804
  | 7 => 61165074761245173108333428605442
  | 8 => 40564821629932831473688813634561
  | 9 => 61164452159688595432716890014721
  | 10 => 60927698554471854258868443087107
  | 11 => 20283652384116744865198911783424
  | 12 => 79851987126796098067637601026
  | 13 => 61164455800651528130209505281026
  | _ => 0

def C031_digit (i j : Fin 14) : ℕ := packedDigit 3 (C031_lowColumnCode j) i.val

private theorem C031_bound_00 : ∀ j : Fin 14, C031_digit 0 j < 5 := by decide +kernel

private theorem C031_bound_01 : ∀ j : Fin 14, C031_digit 1 j < 5 := by decide +kernel

private theorem C031_bound_02 : ∀ j : Fin 14, C031_digit 2 j < 5 := by decide +kernel

private theorem C031_bound_03 : ∀ j : Fin 14, C031_digit 3 j < 5 := by decide +kernel

private theorem C031_bound_04 : ∀ j : Fin 14, C031_digit 4 j < 5 := by decide +kernel

private theorem C031_bound_05 : ∀ j : Fin 14, C031_digit 5 j < 5 := by decide +kernel

private theorem C031_bound_06 : ∀ j : Fin 14, C031_digit 6 j < 5 := by decide +kernel

private theorem C031_bound_07 : ∀ j : Fin 14, C031_digit 7 j < 5 := by decide +kernel

private theorem C031_bound_08 : ∀ j : Fin 14, C031_digit 8 j < 5 := by decide +kernel

private theorem C031_bound_09 : ∀ j : Fin 14, C031_digit 9 j < 5 := by decide +kernel

private theorem C031_bound_10 : ∀ j : Fin 14, C031_digit 10 j < 5 := by decide +kernel

private theorem C031_bound_11 : ∀ j : Fin 14, C031_digit 11 j < 5 := by decide +kernel

private theorem C031_bound_12 : ∀ j : Fin 14, C031_digit 12 j < 5 := by decide +kernel

private theorem C031_bound_13 : ∀ j : Fin 14, C031_digit 13 j < 5 := by decide +kernel

theorem C031_bound : ∀ i j : Fin 14, C031_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C031_bound_00 j
  · exact C031_bound_01 j
  · exact C031_bound_02 j
  · exact C031_bound_03 j
  · exact C031_bound_04 j
  · exact C031_bound_05 j
  · exact C031_bound_06 j
  · exact C031_bound_07 j
  · exact C031_bound_08 j
  · exact C031_bound_09 j
  · exact C031_bound_10 j
  · exact C031_bound_11 j
  · exact C031_bound_12 j
  · exact C031_bound_13 j

private theorem C031_row_00 : pack 256 (C031_digit 0)=C031_rowCode 0 := by decide +kernel

private theorem C031_row_01 : pack 256 (C031_digit 1)=C031_rowCode 1 := by decide +kernel

private theorem C031_row_02 : pack 256 (C031_digit 2)=C031_rowCode 2 := by decide +kernel

private theorem C031_row_03 : pack 256 (C031_digit 3)=C031_rowCode 3 := by decide +kernel

private theorem C031_row_04 : pack 256 (C031_digit 4)=C031_rowCode 4 := by decide +kernel

private theorem C031_row_05 : pack 256 (C031_digit 5)=C031_rowCode 5 := by decide +kernel

private theorem C031_row_06 : pack 256 (C031_digit 6)=C031_rowCode 6 := by decide +kernel

private theorem C031_row_07 : pack 256 (C031_digit 7)=C031_rowCode 7 := by decide +kernel

private theorem C031_row_08 : pack 256 (C031_digit 8)=C031_rowCode 8 := by decide +kernel

private theorem C031_row_09 : pack 256 (C031_digit 9)=C031_rowCode 9 := by decide +kernel

private theorem C031_row_10 : pack 256 (C031_digit 10)=C031_rowCode 10 := by decide +kernel

private theorem C031_row_11 : pack 256 (C031_digit 11)=C031_rowCode 11 := by decide +kernel

private theorem C031_row_12 : pack 256 (C031_digit 12)=C031_rowCode 12 := by decide +kernel

private theorem C031_row_13 : pack 256 (C031_digit 13)=C031_rowCode 13 := by decide +kernel

theorem C031_row_binding : ∀ i : Fin 14, pack 256 (C031_digit i)=C031_rowCode i := by
  intro i
  fin_cases i
  · exact C031_row_00
  · exact C031_row_01
  · exact C031_row_02
  · exact C031_row_03
  · exact C031_row_04
  · exact C031_row_05
  · exact C031_row_06
  · exact C031_row_07
  · exact C031_row_08
  · exact C031_row_09
  · exact C031_row_10
  · exact C031_row_11
  · exact C031_row_12
  · exact C031_row_13

private theorem C031_column_00 : reversePack 256 (fun j : Fin 14 => C031_digit j 0)=C031_columnCode 0 := by decide +kernel

private theorem C031_column_01 : reversePack 256 (fun j : Fin 14 => C031_digit j 1)=C031_columnCode 1 := by decide +kernel

private theorem C031_column_02 : reversePack 256 (fun j : Fin 14 => C031_digit j 2)=C031_columnCode 2 := by decide +kernel

private theorem C031_column_03 : reversePack 256 (fun j : Fin 14 => C031_digit j 3)=C031_columnCode 3 := by decide +kernel

private theorem C031_column_04 : reversePack 256 (fun j : Fin 14 => C031_digit j 4)=C031_columnCode 4 := by decide +kernel

private theorem C031_column_05 : reversePack 256 (fun j : Fin 14 => C031_digit j 5)=C031_columnCode 5 := by decide +kernel

private theorem C031_column_06 : reversePack 256 (fun j : Fin 14 => C031_digit j 6)=C031_columnCode 6 := by decide +kernel

private theorem C031_column_07 : reversePack 256 (fun j : Fin 14 => C031_digit j 7)=C031_columnCode 7 := by decide +kernel

private theorem C031_column_08 : reversePack 256 (fun j : Fin 14 => C031_digit j 8)=C031_columnCode 8 := by decide +kernel

private theorem C031_column_09 : reversePack 256 (fun j : Fin 14 => C031_digit j 9)=C031_columnCode 9 := by decide +kernel

private theorem C031_column_10 : reversePack 256 (fun j : Fin 14 => C031_digit j 10)=C031_columnCode 10 := by decide +kernel

private theorem C031_column_11 : reversePack 256 (fun j : Fin 14 => C031_digit j 11)=C031_columnCode 11 := by decide +kernel

private theorem C031_column_12 : reversePack 256 (fun j : Fin 14 => C031_digit j 12)=C031_columnCode 12 := by decide +kernel

private theorem C031_column_13 : reversePack 256 (fun j : Fin 14 => C031_digit j 13)=C031_columnCode 13 := by decide +kernel

theorem C031_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C031_digit j i)=C031_columnCode i := by
  intro i
  fin_cases i
  · exact C031_column_00
  · exact C031_column_01
  · exact C031_column_02
  · exact C031_column_03
  · exact C031_column_04
  · exact C031_column_05
  · exact C031_column_06
  · exact C031_column_07
  · exact C031_column_08
  · exact C031_column_09
  · exact C031_column_10
  · exact C031_column_11
  · exact C031_column_12
  · exact C031_column_13

def C031_data : PackedData 14 5 256 where
  raw := C031_digit
  digit_lt := C031_bound
  rowCode := C031_rowCode
  columnCode := C031_columnCode
  row_binding := C031_row_binding
  column_binding := C031_column_binding

def C032_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 842391165060
  | 1 => 1188688892963
  | 2 => 1808525203546
  | 3 => 293476045922
  | 4 => 138836739200
  | 5 => 1752355644939
  | 6 => 768028587737
  | 7 => 172403732744
  | 8 => 2280780763137
  | 9 => 714376037584
  | 10 => 2405773718683
  | 11 => 1926366377232
  | 12 => 4723679770
  | 13 => 2362701914244
  | _ => 0

def C032_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 81288098366431116243710871995140
  | 1 => 238307093784700415663442953216
  | 2 => 40566059579361653980846375370754
  | 3 => 79849559830280070460722119172
  | 4 => 40724207633046922097133663355137
  | 5 => 81368564478429399770648318902786
  | 6 => 237686905394721600531276496899
  | 7 => 317843527678973846188758139651
  | 8 => 81210108162845891726436320150274
  | 9 => 61084918143664551246286813265924
  | 10 => 317531624872854344105350923008
  | 11 => 60847228825140845980773607670274
  | 12 => 40566060783583409742591100584196
  | 13 => 81130571710135577933449873523201
  | _ => 0

def C032_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 81130262225089079834883465020417
  | 1 => 61164143883622968670214858866946
  | 2 => 40802818020300048021510523322883
  | 3 => 40882043764981263989107452937216
  | 4 => 621387890017460102755254784
  | 5 => 60926460609728506148297514418435
  | 6 => 20521026187242560973309170746113
  | 7 => 80466116720937401268757070336
  | 8 => 20282409608392483933469456531716
  | 9 => 159387216835991645159241744897
  | 10 => 61085534700591670566301993009924
  | 11 => 159696697160340558447120483331
  | 12 => 40802504913272243973059212476416
  | 13 => 81130257394144844332371514950148
  | _ => 0

def C032_digit (i j : Fin 14) : ℕ := packedDigit 3 (C032_lowColumnCode j) i.val

private theorem C032_bound_00 : ∀ j : Fin 14, C032_digit 0 j < 5 := by decide +kernel

private theorem C032_bound_01 : ∀ j : Fin 14, C032_digit 1 j < 5 := by decide +kernel

private theorem C032_bound_02 : ∀ j : Fin 14, C032_digit 2 j < 5 := by decide +kernel

private theorem C032_bound_03 : ∀ j : Fin 14, C032_digit 3 j < 5 := by decide +kernel

private theorem C032_bound_04 : ∀ j : Fin 14, C032_digit 4 j < 5 := by decide +kernel

private theorem C032_bound_05 : ∀ j : Fin 14, C032_digit 5 j < 5 := by decide +kernel

private theorem C032_bound_06 : ∀ j : Fin 14, C032_digit 6 j < 5 := by decide +kernel

private theorem C032_bound_07 : ∀ j : Fin 14, C032_digit 7 j < 5 := by decide +kernel

private theorem C032_bound_08 : ∀ j : Fin 14, C032_digit 8 j < 5 := by decide +kernel

private theorem C032_bound_09 : ∀ j : Fin 14, C032_digit 9 j < 5 := by decide +kernel

private theorem C032_bound_10 : ∀ j : Fin 14, C032_digit 10 j < 5 := by decide +kernel

private theorem C032_bound_11 : ∀ j : Fin 14, C032_digit 11 j < 5 := by decide +kernel

private theorem C032_bound_12 : ∀ j : Fin 14, C032_digit 12 j < 5 := by decide +kernel

private theorem C032_bound_13 : ∀ j : Fin 14, C032_digit 13 j < 5 := by decide +kernel

theorem C032_bound : ∀ i j : Fin 14, C032_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C032_bound_00 j
  · exact C032_bound_01 j
  · exact C032_bound_02 j
  · exact C032_bound_03 j
  · exact C032_bound_04 j
  · exact C032_bound_05 j
  · exact C032_bound_06 j
  · exact C032_bound_07 j
  · exact C032_bound_08 j
  · exact C032_bound_09 j
  · exact C032_bound_10 j
  · exact C032_bound_11 j
  · exact C032_bound_12 j
  · exact C032_bound_13 j

private theorem C032_row_00 : pack 256 (C032_digit 0)=C032_rowCode 0 := by decide +kernel

private theorem C032_row_01 : pack 256 (C032_digit 1)=C032_rowCode 1 := by decide +kernel

private theorem C032_row_02 : pack 256 (C032_digit 2)=C032_rowCode 2 := by decide +kernel

private theorem C032_row_03 : pack 256 (C032_digit 3)=C032_rowCode 3 := by decide +kernel

private theorem C032_row_04 : pack 256 (C032_digit 4)=C032_rowCode 4 := by decide +kernel

private theorem C032_row_05 : pack 256 (C032_digit 5)=C032_rowCode 5 := by decide +kernel

private theorem C032_row_06 : pack 256 (C032_digit 6)=C032_rowCode 6 := by decide +kernel

private theorem C032_row_07 : pack 256 (C032_digit 7)=C032_rowCode 7 := by decide +kernel

private theorem C032_row_08 : pack 256 (C032_digit 8)=C032_rowCode 8 := by decide +kernel

private theorem C032_row_09 : pack 256 (C032_digit 9)=C032_rowCode 9 := by decide +kernel

private theorem C032_row_10 : pack 256 (C032_digit 10)=C032_rowCode 10 := by decide +kernel

private theorem C032_row_11 : pack 256 (C032_digit 11)=C032_rowCode 11 := by decide +kernel

private theorem C032_row_12 : pack 256 (C032_digit 12)=C032_rowCode 12 := by decide +kernel

private theorem C032_row_13 : pack 256 (C032_digit 13)=C032_rowCode 13 := by decide +kernel

theorem C032_row_binding : ∀ i : Fin 14, pack 256 (C032_digit i)=C032_rowCode i := by
  intro i
  fin_cases i
  · exact C032_row_00
  · exact C032_row_01
  · exact C032_row_02
  · exact C032_row_03
  · exact C032_row_04
  · exact C032_row_05
  · exact C032_row_06
  · exact C032_row_07
  · exact C032_row_08
  · exact C032_row_09
  · exact C032_row_10
  · exact C032_row_11
  · exact C032_row_12
  · exact C032_row_13

private theorem C032_column_00 : reversePack 256 (fun j : Fin 14 => C032_digit j 0)=C032_columnCode 0 := by decide +kernel

private theorem C032_column_01 : reversePack 256 (fun j : Fin 14 => C032_digit j 1)=C032_columnCode 1 := by decide +kernel

private theorem C032_column_02 : reversePack 256 (fun j : Fin 14 => C032_digit j 2)=C032_columnCode 2 := by decide +kernel

private theorem C032_column_03 : reversePack 256 (fun j : Fin 14 => C032_digit j 3)=C032_columnCode 3 := by decide +kernel

private theorem C032_column_04 : reversePack 256 (fun j : Fin 14 => C032_digit j 4)=C032_columnCode 4 := by decide +kernel

private theorem C032_column_05 : reversePack 256 (fun j : Fin 14 => C032_digit j 5)=C032_columnCode 5 := by decide +kernel

private theorem C032_column_06 : reversePack 256 (fun j : Fin 14 => C032_digit j 6)=C032_columnCode 6 := by decide +kernel

private theorem C032_column_07 : reversePack 256 (fun j : Fin 14 => C032_digit j 7)=C032_columnCode 7 := by decide +kernel

private theorem C032_column_08 : reversePack 256 (fun j : Fin 14 => C032_digit j 8)=C032_columnCode 8 := by decide +kernel

private theorem C032_column_09 : reversePack 256 (fun j : Fin 14 => C032_digit j 9)=C032_columnCode 9 := by decide +kernel

private theorem C032_column_10 : reversePack 256 (fun j : Fin 14 => C032_digit j 10)=C032_columnCode 10 := by decide +kernel

private theorem C032_column_11 : reversePack 256 (fun j : Fin 14 => C032_digit j 11)=C032_columnCode 11 := by decide +kernel

private theorem C032_column_12 : reversePack 256 (fun j : Fin 14 => C032_digit j 12)=C032_columnCode 12 := by decide +kernel

private theorem C032_column_13 : reversePack 256 (fun j : Fin 14 => C032_digit j 13)=C032_columnCode 13 := by decide +kernel

theorem C032_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C032_digit j i)=C032_columnCode i := by
  intro i
  fin_cases i
  · exact C032_column_00
  · exact C032_column_01
  · exact C032_column_02
  · exact C032_column_03
  · exact C032_column_04
  · exact C032_column_05
  · exact C032_column_06
  · exact C032_column_07
  · exact C032_column_08
  · exact C032_column_09
  · exact C032_column_10
  · exact C032_column_11
  · exact C032_column_12
  · exact C032_column_13

def C032_data : PackedData 14 5 256 where
  raw := C032_digit
  digit_lt := C032_bound
  rowCode := C032_rowCode
  columnCode := C032_columnCode
  row_binding := C032_row_binding
  column_binding := C032_column_binding

def C033_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 1393119306320
  | 1 => 1126898434819
  | 2 => 243207022144
  | 3 => 1952669536473
  | 4 => 2348886804563
  | 5 => 850605129994
  | 6 => 69131413196
  | 7 => 73089955905
  | 8 => 1737772316865
  | 9 => 1206902864139
  | 10 => 1788258392066
  | 11 => 688740643466
  | 12 => 1344364986652
  | 13 => 29536917155
  | _ => 0

def C033_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 61164762863068969920000243532544
  | 1 => 81367632391881662819091135594498
  | 2 => 40882350846324919958527197381633
  | 3 => 60847543150631653058018858434817
  | 4 => 20600251931886667845134150926338
  | 5 => 61084916925312157461082275906307
  | 6 => 40644356859605134091189217198080
  | 7 => 81367637222899757356595735036675
  | 8 => 159699105549087463860904919044
  | 9 => 81130570496468945652645521261571
  | 10 => 61164452173874357231928899404033
  | 11 => 61164141479938428045144810062594
  | 12 => 238305880154960502595503980548
  | 13 => 158769446315882063220497711618
  | _ => 0

def C033_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 158767028464243681681284924418
  | 1 => 60848467959975457343409083318274
  | 2 => 313121250532519330453914368
  | 3 => 20521022550964957157549762872323
  | 4 => 61005999475586395042784181551620
  | 5 => 40645285328746428559237906105345
  | 6 => 81209798668428159409131572166912
  | 7 => 20282723938531870806439630995712
  | 8 => 20283342908588622593469999874307
  | 9 => 60927699763379010955529448325378
  | 10 => 40564824047784327151812830298627
  | 11 => 40644667562930239282343569261057
  | 12 => 81368560861133639156762304316162
  | 13 => 61164764062587022112436890304512
  | _ => 0

def C033_digit (i j : Fin 14) : ℕ := packedDigit 3 (C033_lowColumnCode j) i.val

private theorem C033_bound_00 : ∀ j : Fin 14, C033_digit 0 j < 5 := by decide +kernel

private theorem C033_bound_01 : ∀ j : Fin 14, C033_digit 1 j < 5 := by decide +kernel

private theorem C033_bound_02 : ∀ j : Fin 14, C033_digit 2 j < 5 := by decide +kernel

private theorem C033_bound_03 : ∀ j : Fin 14, C033_digit 3 j < 5 := by decide +kernel

private theorem C033_bound_04 : ∀ j : Fin 14, C033_digit 4 j < 5 := by decide +kernel

private theorem C033_bound_05 : ∀ j : Fin 14, C033_digit 5 j < 5 := by decide +kernel

private theorem C033_bound_06 : ∀ j : Fin 14, C033_digit 6 j < 5 := by decide +kernel

private theorem C033_bound_07 : ∀ j : Fin 14, C033_digit 7 j < 5 := by decide +kernel

private theorem C033_bound_08 : ∀ j : Fin 14, C033_digit 8 j < 5 := by decide +kernel

private theorem C033_bound_09 : ∀ j : Fin 14, C033_digit 9 j < 5 := by decide +kernel

private theorem C033_bound_10 : ∀ j : Fin 14, C033_digit 10 j < 5 := by decide +kernel

private theorem C033_bound_11 : ∀ j : Fin 14, C033_digit 11 j < 5 := by decide +kernel

private theorem C033_bound_12 : ∀ j : Fin 14, C033_digit 12 j < 5 := by decide +kernel

private theorem C033_bound_13 : ∀ j : Fin 14, C033_digit 13 j < 5 := by decide +kernel

theorem C033_bound : ∀ i j : Fin 14, C033_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C033_bound_00 j
  · exact C033_bound_01 j
  · exact C033_bound_02 j
  · exact C033_bound_03 j
  · exact C033_bound_04 j
  · exact C033_bound_05 j
  · exact C033_bound_06 j
  · exact C033_bound_07 j
  · exact C033_bound_08 j
  · exact C033_bound_09 j
  · exact C033_bound_10 j
  · exact C033_bound_11 j
  · exact C033_bound_12 j
  · exact C033_bound_13 j

private theorem C033_row_00 : pack 256 (C033_digit 0)=C033_rowCode 0 := by decide +kernel

private theorem C033_row_01 : pack 256 (C033_digit 1)=C033_rowCode 1 := by decide +kernel

private theorem C033_row_02 : pack 256 (C033_digit 2)=C033_rowCode 2 := by decide +kernel

private theorem C033_row_03 : pack 256 (C033_digit 3)=C033_rowCode 3 := by decide +kernel

private theorem C033_row_04 : pack 256 (C033_digit 4)=C033_rowCode 4 := by decide +kernel

private theorem C033_row_05 : pack 256 (C033_digit 5)=C033_rowCode 5 := by decide +kernel

private theorem C033_row_06 : pack 256 (C033_digit 6)=C033_rowCode 6 := by decide +kernel

private theorem C033_row_07 : pack 256 (C033_digit 7)=C033_rowCode 7 := by decide +kernel

private theorem C033_row_08 : pack 256 (C033_digit 8)=C033_rowCode 8 := by decide +kernel

private theorem C033_row_09 : pack 256 (C033_digit 9)=C033_rowCode 9 := by decide +kernel

private theorem C033_row_10 : pack 256 (C033_digit 10)=C033_rowCode 10 := by decide +kernel

private theorem C033_row_11 : pack 256 (C033_digit 11)=C033_rowCode 11 := by decide +kernel

private theorem C033_row_12 : pack 256 (C033_digit 12)=C033_rowCode 12 := by decide +kernel

private theorem C033_row_13 : pack 256 (C033_digit 13)=C033_rowCode 13 := by decide +kernel

theorem C033_row_binding : ∀ i : Fin 14, pack 256 (C033_digit i)=C033_rowCode i := by
  intro i
  fin_cases i
  · exact C033_row_00
  · exact C033_row_01
  · exact C033_row_02
  · exact C033_row_03
  · exact C033_row_04
  · exact C033_row_05
  · exact C033_row_06
  · exact C033_row_07
  · exact C033_row_08
  · exact C033_row_09
  · exact C033_row_10
  · exact C033_row_11
  · exact C033_row_12
  · exact C033_row_13

private theorem C033_column_00 : reversePack 256 (fun j : Fin 14 => C033_digit j 0)=C033_columnCode 0 := by decide +kernel

private theorem C033_column_01 : reversePack 256 (fun j : Fin 14 => C033_digit j 1)=C033_columnCode 1 := by decide +kernel

private theorem C033_column_02 : reversePack 256 (fun j : Fin 14 => C033_digit j 2)=C033_columnCode 2 := by decide +kernel

private theorem C033_column_03 : reversePack 256 (fun j : Fin 14 => C033_digit j 3)=C033_columnCode 3 := by decide +kernel

private theorem C033_column_04 : reversePack 256 (fun j : Fin 14 => C033_digit j 4)=C033_columnCode 4 := by decide +kernel

private theorem C033_column_05 : reversePack 256 (fun j : Fin 14 => C033_digit j 5)=C033_columnCode 5 := by decide +kernel

private theorem C033_column_06 : reversePack 256 (fun j : Fin 14 => C033_digit j 6)=C033_columnCode 6 := by decide +kernel

private theorem C033_column_07 : reversePack 256 (fun j : Fin 14 => C033_digit j 7)=C033_columnCode 7 := by decide +kernel

private theorem C033_column_08 : reversePack 256 (fun j : Fin 14 => C033_digit j 8)=C033_columnCode 8 := by decide +kernel

private theorem C033_column_09 : reversePack 256 (fun j : Fin 14 => C033_digit j 9)=C033_columnCode 9 := by decide +kernel

private theorem C033_column_10 : reversePack 256 (fun j : Fin 14 => C033_digit j 10)=C033_columnCode 10 := by decide +kernel

private theorem C033_column_11 : reversePack 256 (fun j : Fin 14 => C033_digit j 11)=C033_columnCode 11 := by decide +kernel

private theorem C033_column_12 : reversePack 256 (fun j : Fin 14 => C033_digit j 12)=C033_columnCode 12 := by decide +kernel

private theorem C033_column_13 : reversePack 256 (fun j : Fin 14 => C033_digit j 13)=C033_columnCode 13 := by decide +kernel

theorem C033_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C033_digit j i)=C033_columnCode i := by
  intro i
  fin_cases i
  · exact C033_column_00
  · exact C033_column_01
  · exact C033_column_02
  · exact C033_column_03
  · exact C033_column_04
  · exact C033_column_05
  · exact C033_column_06
  · exact C033_column_07
  · exact C033_column_08
  · exact C033_column_09
  · exact C033_column_10
  · exact C033_column_11
  · exact C033_column_12
  · exact C033_column_13

def C033_data : PackedData 14 5 256 where
  raw := C033_digit
  digit_lt := C033_bound
  rowCode := C033_rowCode
  columnCode := C033_columnCode
  row_binding := C033_row_binding
  column_binding := C033_column_binding

end SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedCaches04
