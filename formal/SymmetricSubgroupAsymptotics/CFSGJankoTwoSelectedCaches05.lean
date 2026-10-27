import SymmetricSubgroupAsymptotics.MatrixKroneckerProductReflection
import Mathlib.Tactic.FinCases

/-! Literal14/F5 selected caches; digit bounds and both pack bindings are independently kernel checked. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedCaches05
open MatrixKroneckerProductReflection MatrixKroneckerDotReflection
open MatrixNaturalRowDotReflection SmallNaturalMatrixProductReflection

def C034_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 2503045694530
  | 1 => 551235471435
  | 2 => 1873077667552
  | 3 => 2487092615202
  | 4 => 1342450180236
  | 5 => 1137537529473
  | 6 => 2503182403219
  | 7 => 1877178729474
  | 8 => 854967756498
  | 9 => 1240763544155
  | 10 => 103251718864
  | 11 => 696072308416
  | 12 => 2364782756371
  | 13 => 1237427569369
  | _ => 0

def C034_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 20520094105398601334213968921346
  | 1 => 61005687568039172675997861675264
  | 2 => 60848160897539641431183792996609
  | 3 => 20362567434899070089378526331906
  | 4 => 81446554705645480186390259958788
  | 5 => 81288404234108499658433043235588
  | 6 => 61005997043622996312351595037697
  | 7 => 60847540723261493609640893677825
  | 8 => 81129950331635242002399048761345
  | 9 => 61085533496369770690460197782273
  | 10 => 158456339269704178199135518979
  | 11 => 237998808311378012615433388035
  | 12 => 40723895720796069068577316208644
  | 13 => 40882041351833616554040104255748
  | _ => 0

def C034_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 40565131129128126670167867589636
  | 1 => 60926771313127470088584461025281
  | 2 => 317844731900874003501201621763
  | 3 => 40881736697841455994627822781444
  | 4 => 81209485556585394309811904185090
  | 5 => 20283032214652838080434483232770
  | 6 => 61006307751670324149372615590916
  | 7 => 40564821644118522341210986775299
  | 8 => 40724207623602188284779059938305
  | 9 => 61085224006637510804936396374530
  | 10 => 159386003151056453972720353536
  | 11 => 932081825441963344524280321
  | 12 => 61005686363835863096485010932228
  | 13 => 20521023774113217015954626576898
  | _ => 0

def C034_digit (i j : Fin 14) : ℕ := packedDigit 3 (C034_lowColumnCode j) i.val

private theorem C034_bound_00 : ∀ j : Fin 14, C034_digit 0 j < 5 := by decide +kernel

private theorem C034_bound_01 : ∀ j : Fin 14, C034_digit 1 j < 5 := by decide +kernel

private theorem C034_bound_02 : ∀ j : Fin 14, C034_digit 2 j < 5 := by decide +kernel

private theorem C034_bound_03 : ∀ j : Fin 14, C034_digit 3 j < 5 := by decide +kernel

private theorem C034_bound_04 : ∀ j : Fin 14, C034_digit 4 j < 5 := by decide +kernel

private theorem C034_bound_05 : ∀ j : Fin 14, C034_digit 5 j < 5 := by decide +kernel

private theorem C034_bound_06 : ∀ j : Fin 14, C034_digit 6 j < 5 := by decide +kernel

private theorem C034_bound_07 : ∀ j : Fin 14, C034_digit 7 j < 5 := by decide +kernel

private theorem C034_bound_08 : ∀ j : Fin 14, C034_digit 8 j < 5 := by decide +kernel

private theorem C034_bound_09 : ∀ j : Fin 14, C034_digit 9 j < 5 := by decide +kernel

private theorem C034_bound_10 : ∀ j : Fin 14, C034_digit 10 j < 5 := by decide +kernel

private theorem C034_bound_11 : ∀ j : Fin 14, C034_digit 11 j < 5 := by decide +kernel

private theorem C034_bound_12 : ∀ j : Fin 14, C034_digit 12 j < 5 := by decide +kernel

private theorem C034_bound_13 : ∀ j : Fin 14, C034_digit 13 j < 5 := by decide +kernel

theorem C034_bound : ∀ i j : Fin 14, C034_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C034_bound_00 j
  · exact C034_bound_01 j
  · exact C034_bound_02 j
  · exact C034_bound_03 j
  · exact C034_bound_04 j
  · exact C034_bound_05 j
  · exact C034_bound_06 j
  · exact C034_bound_07 j
  · exact C034_bound_08 j
  · exact C034_bound_09 j
  · exact C034_bound_10 j
  · exact C034_bound_11 j
  · exact C034_bound_12 j
  · exact C034_bound_13 j

private theorem C034_row_00 : pack 256 (C034_digit 0)=C034_rowCode 0 := by decide +kernel

private theorem C034_row_01 : pack 256 (C034_digit 1)=C034_rowCode 1 := by decide +kernel

private theorem C034_row_02 : pack 256 (C034_digit 2)=C034_rowCode 2 := by decide +kernel

private theorem C034_row_03 : pack 256 (C034_digit 3)=C034_rowCode 3 := by decide +kernel

private theorem C034_row_04 : pack 256 (C034_digit 4)=C034_rowCode 4 := by decide +kernel

private theorem C034_row_05 : pack 256 (C034_digit 5)=C034_rowCode 5 := by decide +kernel

private theorem C034_row_06 : pack 256 (C034_digit 6)=C034_rowCode 6 := by decide +kernel

private theorem C034_row_07 : pack 256 (C034_digit 7)=C034_rowCode 7 := by decide +kernel

private theorem C034_row_08 : pack 256 (C034_digit 8)=C034_rowCode 8 := by decide +kernel

private theorem C034_row_09 : pack 256 (C034_digit 9)=C034_rowCode 9 := by decide +kernel

private theorem C034_row_10 : pack 256 (C034_digit 10)=C034_rowCode 10 := by decide +kernel

private theorem C034_row_11 : pack 256 (C034_digit 11)=C034_rowCode 11 := by decide +kernel

private theorem C034_row_12 : pack 256 (C034_digit 12)=C034_rowCode 12 := by decide +kernel

private theorem C034_row_13 : pack 256 (C034_digit 13)=C034_rowCode 13 := by decide +kernel

theorem C034_row_binding : ∀ i : Fin 14, pack 256 (C034_digit i)=C034_rowCode i := by
  intro i
  fin_cases i
  · exact C034_row_00
  · exact C034_row_01
  · exact C034_row_02
  · exact C034_row_03
  · exact C034_row_04
  · exact C034_row_05
  · exact C034_row_06
  · exact C034_row_07
  · exact C034_row_08
  · exact C034_row_09
  · exact C034_row_10
  · exact C034_row_11
  · exact C034_row_12
  · exact C034_row_13

private theorem C034_column_00 : reversePack 256 (fun j : Fin 14 => C034_digit j 0)=C034_columnCode 0 := by decide +kernel

private theorem C034_column_01 : reversePack 256 (fun j : Fin 14 => C034_digit j 1)=C034_columnCode 1 := by decide +kernel

private theorem C034_column_02 : reversePack 256 (fun j : Fin 14 => C034_digit j 2)=C034_columnCode 2 := by decide +kernel

private theorem C034_column_03 : reversePack 256 (fun j : Fin 14 => C034_digit j 3)=C034_columnCode 3 := by decide +kernel

private theorem C034_column_04 : reversePack 256 (fun j : Fin 14 => C034_digit j 4)=C034_columnCode 4 := by decide +kernel

private theorem C034_column_05 : reversePack 256 (fun j : Fin 14 => C034_digit j 5)=C034_columnCode 5 := by decide +kernel

private theorem C034_column_06 : reversePack 256 (fun j : Fin 14 => C034_digit j 6)=C034_columnCode 6 := by decide +kernel

private theorem C034_column_07 : reversePack 256 (fun j : Fin 14 => C034_digit j 7)=C034_columnCode 7 := by decide +kernel

private theorem C034_column_08 : reversePack 256 (fun j : Fin 14 => C034_digit j 8)=C034_columnCode 8 := by decide +kernel

private theorem C034_column_09 : reversePack 256 (fun j : Fin 14 => C034_digit j 9)=C034_columnCode 9 := by decide +kernel

private theorem C034_column_10 : reversePack 256 (fun j : Fin 14 => C034_digit j 10)=C034_columnCode 10 := by decide +kernel

private theorem C034_column_11 : reversePack 256 (fun j : Fin 14 => C034_digit j 11)=C034_columnCode 11 := by decide +kernel

private theorem C034_column_12 : reversePack 256 (fun j : Fin 14 => C034_digit j 12)=C034_columnCode 12 := by decide +kernel

private theorem C034_column_13 : reversePack 256 (fun j : Fin 14 => C034_digit j 13)=C034_columnCode 13 := by decide +kernel

theorem C034_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C034_digit j i)=C034_columnCode i := by
  intro i
  fin_cases i
  · exact C034_column_00
  · exact C034_column_01
  · exact C034_column_02
  · exact C034_column_03
  · exact C034_column_04
  · exact C034_column_05
  · exact C034_column_06
  · exact C034_column_07
  · exact C034_column_08
  · exact C034_column_09
  · exact C034_column_10
  · exact C034_column_11
  · exact C034_column_12
  · exact C034_column_13

def C034_data : PackedData 14 5 256 where
  raw := C034_digit
  digit_lt := C034_bound
  rowCode := C034_rowCode
  columnCode := C034_columnCode
  row_binding := C034_row_binding
  column_binding := C034_column_binding

def C035_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 1392945775268
  | 1 => 1729800844496
  | 2 => 1256551089281
  | 3 => 1194192863308
  | 4 => 704518140611
  | 5 => 2297177130499
  | 6 => 207518466057
  | 7 => 2220653888545
  | 8 => 2285477302371
  | 9 => 285890356996
  | 10 => 1189759525408
  | 11 => 851918733578
  | 12 => 1807430590554
  | 13 => 2199080814155
  | _ => 0

def C035_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 61006304124948061143246502428676
  | 1 => 20520408411981638728459290149380
  | 2 => 20362875725113132817380886577922
  | 3 => 60847230034048074453570770043393
  | 4 => 81289335106989602925109424685828
  | 5 => 81446554696163708771795344557059
  | 6 => 60848471591493873814197304951298
  | 7 => 61006305329096245818908242739456
  | 8 => 61085535895313424903989157167106
  | 9 => 159384789576585276274228985858
  | 10 => 237998817700914297255009321729
  | 11 => 159387202669036029163927109890
  | 12 => 159695492901547191176500740356
  | 13 => 81367634805085010493970076271362
  | _ => 0

def C035_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 81447171262554151632025220678658
  | 1 => 159387212150662761218488467715
  | 2 => 20283030991523097021489703158274
  | 3 => 81209176062167949944702604869890
  | 4 => 60848158489132951901193482928641
  | 5 => 60847232456659046554774280536324
  | 6 => 20361637766184669737098774840064
  | 7 => 20599324690486871102447679569924
  | 8 => 61164450950744544681647142994180
  | 9 => 81130879990886678531792019981312
  | 10 => 316913868483238678113500135682
  | 11 => 40645285328746645292779556766721
  | 12 => 40802813189374475714035116540419
  | 13 => 60926770104220025726670544568324
  | _ => 0

def C035_digit (i j : Fin 14) : ℕ := packedDigit 3 (C035_lowColumnCode j) i.val

private theorem C035_bound_00 : ∀ j : Fin 14, C035_digit 0 j < 5 := by decide +kernel

private theorem C035_bound_01 : ∀ j : Fin 14, C035_digit 1 j < 5 := by decide +kernel

private theorem C035_bound_02 : ∀ j : Fin 14, C035_digit 2 j < 5 := by decide +kernel

private theorem C035_bound_03 : ∀ j : Fin 14, C035_digit 3 j < 5 := by decide +kernel

private theorem C035_bound_04 : ∀ j : Fin 14, C035_digit 4 j < 5 := by decide +kernel

private theorem C035_bound_05 : ∀ j : Fin 14, C035_digit 5 j < 5 := by decide +kernel

private theorem C035_bound_06 : ∀ j : Fin 14, C035_digit 6 j < 5 := by decide +kernel

private theorem C035_bound_07 : ∀ j : Fin 14, C035_digit 7 j < 5 := by decide +kernel

private theorem C035_bound_08 : ∀ j : Fin 14, C035_digit 8 j < 5 := by decide +kernel

private theorem C035_bound_09 : ∀ j : Fin 14, C035_digit 9 j < 5 := by decide +kernel

private theorem C035_bound_10 : ∀ j : Fin 14, C035_digit 10 j < 5 := by decide +kernel

private theorem C035_bound_11 : ∀ j : Fin 14, C035_digit 11 j < 5 := by decide +kernel

private theorem C035_bound_12 : ∀ j : Fin 14, C035_digit 12 j < 5 := by decide +kernel

private theorem C035_bound_13 : ∀ j : Fin 14, C035_digit 13 j < 5 := by decide +kernel

theorem C035_bound : ∀ i j : Fin 14, C035_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C035_bound_00 j
  · exact C035_bound_01 j
  · exact C035_bound_02 j
  · exact C035_bound_03 j
  · exact C035_bound_04 j
  · exact C035_bound_05 j
  · exact C035_bound_06 j
  · exact C035_bound_07 j
  · exact C035_bound_08 j
  · exact C035_bound_09 j
  · exact C035_bound_10 j
  · exact C035_bound_11 j
  · exact C035_bound_12 j
  · exact C035_bound_13 j

private theorem C035_row_00 : pack 256 (C035_digit 0)=C035_rowCode 0 := by decide +kernel

private theorem C035_row_01 : pack 256 (C035_digit 1)=C035_rowCode 1 := by decide +kernel

private theorem C035_row_02 : pack 256 (C035_digit 2)=C035_rowCode 2 := by decide +kernel

private theorem C035_row_03 : pack 256 (C035_digit 3)=C035_rowCode 3 := by decide +kernel

private theorem C035_row_04 : pack 256 (C035_digit 4)=C035_rowCode 4 := by decide +kernel

private theorem C035_row_05 : pack 256 (C035_digit 5)=C035_rowCode 5 := by decide +kernel

private theorem C035_row_06 : pack 256 (C035_digit 6)=C035_rowCode 6 := by decide +kernel

private theorem C035_row_07 : pack 256 (C035_digit 7)=C035_rowCode 7 := by decide +kernel

private theorem C035_row_08 : pack 256 (C035_digit 8)=C035_rowCode 8 := by decide +kernel

private theorem C035_row_09 : pack 256 (C035_digit 9)=C035_rowCode 9 := by decide +kernel

private theorem C035_row_10 : pack 256 (C035_digit 10)=C035_rowCode 10 := by decide +kernel

private theorem C035_row_11 : pack 256 (C035_digit 11)=C035_rowCode 11 := by decide +kernel

private theorem C035_row_12 : pack 256 (C035_digit 12)=C035_rowCode 12 := by decide +kernel

private theorem C035_row_13 : pack 256 (C035_digit 13)=C035_rowCode 13 := by decide +kernel

theorem C035_row_binding : ∀ i : Fin 14, pack 256 (C035_digit i)=C035_rowCode i := by
  intro i
  fin_cases i
  · exact C035_row_00
  · exact C035_row_01
  · exact C035_row_02
  · exact C035_row_03
  · exact C035_row_04
  · exact C035_row_05
  · exact C035_row_06
  · exact C035_row_07
  · exact C035_row_08
  · exact C035_row_09
  · exact C035_row_10
  · exact C035_row_11
  · exact C035_row_12
  · exact C035_row_13

private theorem C035_column_00 : reversePack 256 (fun j : Fin 14 => C035_digit j 0)=C035_columnCode 0 := by decide +kernel

private theorem C035_column_01 : reversePack 256 (fun j : Fin 14 => C035_digit j 1)=C035_columnCode 1 := by decide +kernel

private theorem C035_column_02 : reversePack 256 (fun j : Fin 14 => C035_digit j 2)=C035_columnCode 2 := by decide +kernel

private theorem C035_column_03 : reversePack 256 (fun j : Fin 14 => C035_digit j 3)=C035_columnCode 3 := by decide +kernel

private theorem C035_column_04 : reversePack 256 (fun j : Fin 14 => C035_digit j 4)=C035_columnCode 4 := by decide +kernel

private theorem C035_column_05 : reversePack 256 (fun j : Fin 14 => C035_digit j 5)=C035_columnCode 5 := by decide +kernel

private theorem C035_column_06 : reversePack 256 (fun j : Fin 14 => C035_digit j 6)=C035_columnCode 6 := by decide +kernel

private theorem C035_column_07 : reversePack 256 (fun j : Fin 14 => C035_digit j 7)=C035_columnCode 7 := by decide +kernel

private theorem C035_column_08 : reversePack 256 (fun j : Fin 14 => C035_digit j 8)=C035_columnCode 8 := by decide +kernel

private theorem C035_column_09 : reversePack 256 (fun j : Fin 14 => C035_digit j 9)=C035_columnCode 9 := by decide +kernel

private theorem C035_column_10 : reversePack 256 (fun j : Fin 14 => C035_digit j 10)=C035_columnCode 10 := by decide +kernel

private theorem C035_column_11 : reversePack 256 (fun j : Fin 14 => C035_digit j 11)=C035_columnCode 11 := by decide +kernel

private theorem C035_column_12 : reversePack 256 (fun j : Fin 14 => C035_digit j 12)=C035_columnCode 12 := by decide +kernel

private theorem C035_column_13 : reversePack 256 (fun j : Fin 14 => C035_digit j 13)=C035_columnCode 13 := by decide +kernel

theorem C035_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C035_digit j i)=C035_columnCode i := by
  intro i
  fin_cases i
  · exact C035_column_00
  · exact C035_column_01
  · exact C035_column_02
  · exact C035_column_03
  · exact C035_column_04
  · exact C035_column_05
  · exact C035_column_06
  · exact C035_column_07
  · exact C035_column_08
  · exact C035_column_09
  · exact C035_column_10
  · exact C035_column_11
  · exact C035_column_12
  · exact C035_column_13

def C035_data : PackedData 14 5 256 where
  raw := C035_digit
  digit_lt := C035_bound
  rowCode := C035_rowCode
  columnCode := C035_columnCode
  row_binding := C035_row_binding
  column_binding := C035_column_binding

def C043_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 148636545283
  | 1 => 639046912065
  | 2 => 1205147599880
  | 3 => 1266250228820
  | 4 => 1925807442146
  | 5 => 1941780666532
  | 6 => 1258864132884
  | 7 => 1126897173202
  | 8 => 1937232729280
  | 9 => 2289360442394
  | 10 => 782951892770
  | 11 => 2358243864832
  | 12 => 1205298370700
  | 13 => 2373007197905
  | _ => 0

def C043_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 20599324681005245214813753180419
  | 1 => 40644052219688127775166970265600
  | 2 => 61006927911781661318935513923844
  | 3 => 61164145097271226263474438013952
  | 4 => 81209799872594791111424380764163
  | 5 => 238616569405345483682970993667
  | 6 => 623810519291063192430641667
  | 7 => 40803127519458665338570478387459
  | 8 => 40644669966688494262069265170947
  | 9 => 317532833743621960200985182467
  | 10 => 40724514700260300609257373565698
  | 11 => 81447173670924237027932295660033
  | 12 => 40644669971410860746042717044994
  | 13 => 81289333907545266211029359132928
  | _ => 0

def C043_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 60848466765216953353465214599680
  | 1 => 20282723924438701602693934350593
  | 2 => 79230580402869957031199244546
  | 3 => 81288406651978370303416508547586
  | 4 => 40882665148148769157904563438595
  | 5 => 81447174875164439252288537756675
  | 6 => 81289333907563640614934575972866
  | 7 => 40724205215250622816439622631426
  | 8 => 930877659098214333857989635
  | 9 => 40802506117420212756301436027140
  | 10 => 40882973443122237945709716505345
  | 11 => 1237954261869741450673127940
  | 12 => 81209490387621574742669126795522
  | 13 => 20441798029376588474855628997124
  | _ => 0

def C043_digit (i j : Fin 14) : ℕ := packedDigit 3 (C043_lowColumnCode j) i.val

private theorem C043_bound_00 : ∀ j : Fin 14, C043_digit 0 j < 5 := by decide +kernel

private theorem C043_bound_01 : ∀ j : Fin 14, C043_digit 1 j < 5 := by decide +kernel

private theorem C043_bound_02 : ∀ j : Fin 14, C043_digit 2 j < 5 := by decide +kernel

private theorem C043_bound_03 : ∀ j : Fin 14, C043_digit 3 j < 5 := by decide +kernel

private theorem C043_bound_04 : ∀ j : Fin 14, C043_digit 4 j < 5 := by decide +kernel

private theorem C043_bound_05 : ∀ j : Fin 14, C043_digit 5 j < 5 := by decide +kernel

private theorem C043_bound_06 : ∀ j : Fin 14, C043_digit 6 j < 5 := by decide +kernel

private theorem C043_bound_07 : ∀ j : Fin 14, C043_digit 7 j < 5 := by decide +kernel

private theorem C043_bound_08 : ∀ j : Fin 14, C043_digit 8 j < 5 := by decide +kernel

private theorem C043_bound_09 : ∀ j : Fin 14, C043_digit 9 j < 5 := by decide +kernel

private theorem C043_bound_10 : ∀ j : Fin 14, C043_digit 10 j < 5 := by decide +kernel

private theorem C043_bound_11 : ∀ j : Fin 14, C043_digit 11 j < 5 := by decide +kernel

private theorem C043_bound_12 : ∀ j : Fin 14, C043_digit 12 j < 5 := by decide +kernel

private theorem C043_bound_13 : ∀ j : Fin 14, C043_digit 13 j < 5 := by decide +kernel

theorem C043_bound : ∀ i j : Fin 14, C043_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C043_bound_00 j
  · exact C043_bound_01 j
  · exact C043_bound_02 j
  · exact C043_bound_03 j
  · exact C043_bound_04 j
  · exact C043_bound_05 j
  · exact C043_bound_06 j
  · exact C043_bound_07 j
  · exact C043_bound_08 j
  · exact C043_bound_09 j
  · exact C043_bound_10 j
  · exact C043_bound_11 j
  · exact C043_bound_12 j
  · exact C043_bound_13 j

private theorem C043_row_00 : pack 256 (C043_digit 0)=C043_rowCode 0 := by decide +kernel

private theorem C043_row_01 : pack 256 (C043_digit 1)=C043_rowCode 1 := by decide +kernel

private theorem C043_row_02 : pack 256 (C043_digit 2)=C043_rowCode 2 := by decide +kernel

private theorem C043_row_03 : pack 256 (C043_digit 3)=C043_rowCode 3 := by decide +kernel

private theorem C043_row_04 : pack 256 (C043_digit 4)=C043_rowCode 4 := by decide +kernel

private theorem C043_row_05 : pack 256 (C043_digit 5)=C043_rowCode 5 := by decide +kernel

private theorem C043_row_06 : pack 256 (C043_digit 6)=C043_rowCode 6 := by decide +kernel

private theorem C043_row_07 : pack 256 (C043_digit 7)=C043_rowCode 7 := by decide +kernel

private theorem C043_row_08 : pack 256 (C043_digit 8)=C043_rowCode 8 := by decide +kernel

private theorem C043_row_09 : pack 256 (C043_digit 9)=C043_rowCode 9 := by decide +kernel

private theorem C043_row_10 : pack 256 (C043_digit 10)=C043_rowCode 10 := by decide +kernel

private theorem C043_row_11 : pack 256 (C043_digit 11)=C043_rowCode 11 := by decide +kernel

private theorem C043_row_12 : pack 256 (C043_digit 12)=C043_rowCode 12 := by decide +kernel

private theorem C043_row_13 : pack 256 (C043_digit 13)=C043_rowCode 13 := by decide +kernel

theorem C043_row_binding : ∀ i : Fin 14, pack 256 (C043_digit i)=C043_rowCode i := by
  intro i
  fin_cases i
  · exact C043_row_00
  · exact C043_row_01
  · exact C043_row_02
  · exact C043_row_03
  · exact C043_row_04
  · exact C043_row_05
  · exact C043_row_06
  · exact C043_row_07
  · exact C043_row_08
  · exact C043_row_09
  · exact C043_row_10
  · exact C043_row_11
  · exact C043_row_12
  · exact C043_row_13

private theorem C043_column_00 : reversePack 256 (fun j : Fin 14 => C043_digit j 0)=C043_columnCode 0 := by decide +kernel

private theorem C043_column_01 : reversePack 256 (fun j : Fin 14 => C043_digit j 1)=C043_columnCode 1 := by decide +kernel

private theorem C043_column_02 : reversePack 256 (fun j : Fin 14 => C043_digit j 2)=C043_columnCode 2 := by decide +kernel

private theorem C043_column_03 : reversePack 256 (fun j : Fin 14 => C043_digit j 3)=C043_columnCode 3 := by decide +kernel

private theorem C043_column_04 : reversePack 256 (fun j : Fin 14 => C043_digit j 4)=C043_columnCode 4 := by decide +kernel

private theorem C043_column_05 : reversePack 256 (fun j : Fin 14 => C043_digit j 5)=C043_columnCode 5 := by decide +kernel

private theorem C043_column_06 : reversePack 256 (fun j : Fin 14 => C043_digit j 6)=C043_columnCode 6 := by decide +kernel

private theorem C043_column_07 : reversePack 256 (fun j : Fin 14 => C043_digit j 7)=C043_columnCode 7 := by decide +kernel

private theorem C043_column_08 : reversePack 256 (fun j : Fin 14 => C043_digit j 8)=C043_columnCode 8 := by decide +kernel

private theorem C043_column_09 : reversePack 256 (fun j : Fin 14 => C043_digit j 9)=C043_columnCode 9 := by decide +kernel

private theorem C043_column_10 : reversePack 256 (fun j : Fin 14 => C043_digit j 10)=C043_columnCode 10 := by decide +kernel

private theorem C043_column_11 : reversePack 256 (fun j : Fin 14 => C043_digit j 11)=C043_columnCode 11 := by decide +kernel

private theorem C043_column_12 : reversePack 256 (fun j : Fin 14 => C043_digit j 12)=C043_columnCode 12 := by decide +kernel

private theorem C043_column_13 : reversePack 256 (fun j : Fin 14 => C043_digit j 13)=C043_columnCode 13 := by decide +kernel

theorem C043_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C043_digit j i)=C043_columnCode i := by
  intro i
  fin_cases i
  · exact C043_column_00
  · exact C043_column_01
  · exact C043_column_02
  · exact C043_column_03
  · exact C043_column_04
  · exact C043_column_05
  · exact C043_column_06
  · exact C043_column_07
  · exact C043_column_08
  · exact C043_column_09
  · exact C043_column_10
  · exact C043_column_11
  · exact C043_column_12
  · exact C043_column_13

def C043_data : PackedData 14 5 256 where
  raw := C043_digit
  digit_lt := C043_bound
  rowCode := C043_rowCode
  columnCode := C043_columnCode
  row_binding := C043_row_binding
  column_binding := C043_column_binding

def C045_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 107836683777
  | 1 => 1745003488961
  | 2 => 3542229715
  | 3 => 1262792479450
  | 4 => 1804094186249
  | 5 => 67108864
  | 6 => 1112940095202
  | 7 => 2272188973833
  | 8 => 1882406134035
  | 9 => 2217599833740
  | 10 => 1798589236899
  | 11 => 1309344548064
  | 12 => 224586933344
  | 13 => 1657876523154
  | _ => 0

def C045_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 40564822853025678476030056268033
  | 1 => 40882974637862295191575630839808
  | 2 => 40644978252217517466805011153664
  | 3 => 81288717350599484255633282237187
  | 4 => 40724518312833982126224964715011
  | 5 => 79231789365511283680108347394
  | 6 => 20520404785148623479572852114436
  | 7 => 20520096518509283220237081182724
  | 8 => 20441799233580113103475479609859
  | 9 => 80156627006981266110958141699
  | 10 => 80160249062289799906655928580
  | 11 => 20440867147106092193207549952772
  | 12 => 238615360479308567068945678593
  | 13 => 60847851426697207762905460638464
  | _ => 0

def C045_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 20282413244633411564178675859712
  | 1 => 20283341694903615064309680505091
  | 2 => 61006614809457343823680471302144
  | 3 => 40803433363524000733510242599426
  | 4 => 20362876924594292372679178715651
  | 5 => 4398046511104
  | 6 => 40882663948685913921432720572418
  | 7 => 20362876934020577746621361553668
  | 8 => 61006923085541417608411196097283
  | 9 => 81209489178640414616534263136260
  | 10 => 61164764076754048944882701107715
  | 11 => 317843541827698607222788457218
  | 12 => 317224562381914653924629021440
  | 13 => 40723899347499595977643555618819
  | _ => 0

def C045_digit (i j : Fin 14) : ℕ := packedDigit 3 (C045_lowColumnCode j) i.val

private theorem C045_bound_00 : ∀ j : Fin 14, C045_digit 0 j < 5 := by decide +kernel

private theorem C045_bound_01 : ∀ j : Fin 14, C045_digit 1 j < 5 := by decide +kernel

private theorem C045_bound_02 : ∀ j : Fin 14, C045_digit 2 j < 5 := by decide +kernel

private theorem C045_bound_03 : ∀ j : Fin 14, C045_digit 3 j < 5 := by decide +kernel

private theorem C045_bound_04 : ∀ j : Fin 14, C045_digit 4 j < 5 := by decide +kernel

private theorem C045_bound_05 : ∀ j : Fin 14, C045_digit 5 j < 5 := by decide +kernel

private theorem C045_bound_06 : ∀ j : Fin 14, C045_digit 6 j < 5 := by decide +kernel

private theorem C045_bound_07 : ∀ j : Fin 14, C045_digit 7 j < 5 := by decide +kernel

private theorem C045_bound_08 : ∀ j : Fin 14, C045_digit 8 j < 5 := by decide +kernel

private theorem C045_bound_09 : ∀ j : Fin 14, C045_digit 9 j < 5 := by decide +kernel

private theorem C045_bound_10 : ∀ j : Fin 14, C045_digit 10 j < 5 := by decide +kernel

private theorem C045_bound_11 : ∀ j : Fin 14, C045_digit 11 j < 5 := by decide +kernel

private theorem C045_bound_12 : ∀ j : Fin 14, C045_digit 12 j < 5 := by decide +kernel

private theorem C045_bound_13 : ∀ j : Fin 14, C045_digit 13 j < 5 := by decide +kernel

theorem C045_bound : ∀ i j : Fin 14, C045_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C045_bound_00 j
  · exact C045_bound_01 j
  · exact C045_bound_02 j
  · exact C045_bound_03 j
  · exact C045_bound_04 j
  · exact C045_bound_05 j
  · exact C045_bound_06 j
  · exact C045_bound_07 j
  · exact C045_bound_08 j
  · exact C045_bound_09 j
  · exact C045_bound_10 j
  · exact C045_bound_11 j
  · exact C045_bound_12 j
  · exact C045_bound_13 j

private theorem C045_row_00 : pack 256 (C045_digit 0)=C045_rowCode 0 := by decide +kernel

private theorem C045_row_01 : pack 256 (C045_digit 1)=C045_rowCode 1 := by decide +kernel

private theorem C045_row_02 : pack 256 (C045_digit 2)=C045_rowCode 2 := by decide +kernel

private theorem C045_row_03 : pack 256 (C045_digit 3)=C045_rowCode 3 := by decide +kernel

private theorem C045_row_04 : pack 256 (C045_digit 4)=C045_rowCode 4 := by decide +kernel

private theorem C045_row_05 : pack 256 (C045_digit 5)=C045_rowCode 5 := by decide +kernel

private theorem C045_row_06 : pack 256 (C045_digit 6)=C045_rowCode 6 := by decide +kernel

private theorem C045_row_07 : pack 256 (C045_digit 7)=C045_rowCode 7 := by decide +kernel

private theorem C045_row_08 : pack 256 (C045_digit 8)=C045_rowCode 8 := by decide +kernel

private theorem C045_row_09 : pack 256 (C045_digit 9)=C045_rowCode 9 := by decide +kernel

private theorem C045_row_10 : pack 256 (C045_digit 10)=C045_rowCode 10 := by decide +kernel

private theorem C045_row_11 : pack 256 (C045_digit 11)=C045_rowCode 11 := by decide +kernel

private theorem C045_row_12 : pack 256 (C045_digit 12)=C045_rowCode 12 := by decide +kernel

private theorem C045_row_13 : pack 256 (C045_digit 13)=C045_rowCode 13 := by decide +kernel

theorem C045_row_binding : ∀ i : Fin 14, pack 256 (C045_digit i)=C045_rowCode i := by
  intro i
  fin_cases i
  · exact C045_row_00
  · exact C045_row_01
  · exact C045_row_02
  · exact C045_row_03
  · exact C045_row_04
  · exact C045_row_05
  · exact C045_row_06
  · exact C045_row_07
  · exact C045_row_08
  · exact C045_row_09
  · exact C045_row_10
  · exact C045_row_11
  · exact C045_row_12
  · exact C045_row_13

private theorem C045_column_00 : reversePack 256 (fun j : Fin 14 => C045_digit j 0)=C045_columnCode 0 := by decide +kernel

private theorem C045_column_01 : reversePack 256 (fun j : Fin 14 => C045_digit j 1)=C045_columnCode 1 := by decide +kernel

private theorem C045_column_02 : reversePack 256 (fun j : Fin 14 => C045_digit j 2)=C045_columnCode 2 := by decide +kernel

private theorem C045_column_03 : reversePack 256 (fun j : Fin 14 => C045_digit j 3)=C045_columnCode 3 := by decide +kernel

private theorem C045_column_04 : reversePack 256 (fun j : Fin 14 => C045_digit j 4)=C045_columnCode 4 := by decide +kernel

private theorem C045_column_05 : reversePack 256 (fun j : Fin 14 => C045_digit j 5)=C045_columnCode 5 := by decide +kernel

private theorem C045_column_06 : reversePack 256 (fun j : Fin 14 => C045_digit j 6)=C045_columnCode 6 := by decide +kernel

private theorem C045_column_07 : reversePack 256 (fun j : Fin 14 => C045_digit j 7)=C045_columnCode 7 := by decide +kernel

private theorem C045_column_08 : reversePack 256 (fun j : Fin 14 => C045_digit j 8)=C045_columnCode 8 := by decide +kernel

private theorem C045_column_09 : reversePack 256 (fun j : Fin 14 => C045_digit j 9)=C045_columnCode 9 := by decide +kernel

private theorem C045_column_10 : reversePack 256 (fun j : Fin 14 => C045_digit j 10)=C045_columnCode 10 := by decide +kernel

private theorem C045_column_11 : reversePack 256 (fun j : Fin 14 => C045_digit j 11)=C045_columnCode 11 := by decide +kernel

private theorem C045_column_12 : reversePack 256 (fun j : Fin 14 => C045_digit j 12)=C045_columnCode 12 := by decide +kernel

private theorem C045_column_13 : reversePack 256 (fun j : Fin 14 => C045_digit j 13)=C045_columnCode 13 := by decide +kernel

theorem C045_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C045_digit j i)=C045_columnCode i := by
  intro i
  fin_cases i
  · exact C045_column_00
  · exact C045_column_01
  · exact C045_column_02
  · exact C045_column_03
  · exact C045_column_04
  · exact C045_column_05
  · exact C045_column_06
  · exact C045_column_07
  · exact C045_column_08
  · exact C045_column_09
  · exact C045_column_10
  · exact C045_column_11
  · exact C045_column_12
  · exact C045_column_13

def C045_data : PackedData 14 5 256 where
  raw := C045_digit
  digit_lt := C045_bound
  rowCode := C045_rowCode
  columnCode := C045_columnCode
  row_binding := C045_row_binding
  column_binding := C045_column_binding

def C047_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 1169599250969
  | 1 => 2405653661315
  | 2 => 1873051222674
  | 3 => 2227268368516
  | 4 => 12371953416
  | 5 => 97176518849
  | 6 => 106355638428
  | 7 => 167000817874
  | 8 => 1787113878284
  | 9 => 1928765441219
  | 10 => 1754652063298
  | 11 => 1721527048272
  | 12 => 1135138672868
  | 13 => 567137896066
  | _ => 0

def C047_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 40881734289453069094618363200257
  | 1 => 317531620095291744202636001283
  | 2 => 40802814403022877984324623401472
  | 3 => 60848470387234935205830129156865
  | 4 => 79541274357174115047030391812
  | 5 => 61086154874814911063029943829248
  | 6 => 61005687553872145288290055159811
  | 7 => 316916291038509695080471986436
  | 8 => 81368252580272002766631273104385
  | 9 => 20362257954611758499059250430722
  | 10 => 80159054285050552955634188289
  | 11 => 40881736693063893958770278137856
  | 12 => 310712862144777086463836929
  | 13 => 20441798024709561659058169250818
  | _ => 0

def C047_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 20520095319009966282625777664258
  | 1 => 60847851426696919255452345172740
  | 2 => 40723895711332889360963272311555
  | 3 => 81130262234570634513742068645892
  | 4 => 80469729368119068227172106240
  | 5 => 20283338058681350913427729744128
  | 6 => 81367941891132514987917120372992
  | 7 => 40724204006324658525871475458560
  | 8 => 81210105740308635387267601400323
  | 9 => 60848159683873008872185818776579
  | 10 => 40565132333313205678397662167299
  | 11 => 158770650537781941244170076419
  | 12 => 81447479524471055040850958745602
  | 13 => 40565441804155998791325060300801
  | _ => 0

def C047_digit (i j : Fin 14) : ℕ := packedDigit 3 (C047_lowColumnCode j) i.val

private theorem C047_bound_00 : ∀ j : Fin 14, C047_digit 0 j < 5 := by decide +kernel

private theorem C047_bound_01 : ∀ j : Fin 14, C047_digit 1 j < 5 := by decide +kernel

private theorem C047_bound_02 : ∀ j : Fin 14, C047_digit 2 j < 5 := by decide +kernel

private theorem C047_bound_03 : ∀ j : Fin 14, C047_digit 3 j < 5 := by decide +kernel

private theorem C047_bound_04 : ∀ j : Fin 14, C047_digit 4 j < 5 := by decide +kernel

private theorem C047_bound_05 : ∀ j : Fin 14, C047_digit 5 j < 5 := by decide +kernel

private theorem C047_bound_06 : ∀ j : Fin 14, C047_digit 6 j < 5 := by decide +kernel

private theorem C047_bound_07 : ∀ j : Fin 14, C047_digit 7 j < 5 := by decide +kernel

private theorem C047_bound_08 : ∀ j : Fin 14, C047_digit 8 j < 5 := by decide +kernel

private theorem C047_bound_09 : ∀ j : Fin 14, C047_digit 9 j < 5 := by decide +kernel

private theorem C047_bound_10 : ∀ j : Fin 14, C047_digit 10 j < 5 := by decide +kernel

private theorem C047_bound_11 : ∀ j : Fin 14, C047_digit 11 j < 5 := by decide +kernel

private theorem C047_bound_12 : ∀ j : Fin 14, C047_digit 12 j < 5 := by decide +kernel

private theorem C047_bound_13 : ∀ j : Fin 14, C047_digit 13 j < 5 := by decide +kernel

theorem C047_bound : ∀ i j : Fin 14, C047_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C047_bound_00 j
  · exact C047_bound_01 j
  · exact C047_bound_02 j
  · exact C047_bound_03 j
  · exact C047_bound_04 j
  · exact C047_bound_05 j
  · exact C047_bound_06 j
  · exact C047_bound_07 j
  · exact C047_bound_08 j
  · exact C047_bound_09 j
  · exact C047_bound_10 j
  · exact C047_bound_11 j
  · exact C047_bound_12 j
  · exact C047_bound_13 j

private theorem C047_row_00 : pack 256 (C047_digit 0)=C047_rowCode 0 := by decide +kernel

private theorem C047_row_01 : pack 256 (C047_digit 1)=C047_rowCode 1 := by decide +kernel

private theorem C047_row_02 : pack 256 (C047_digit 2)=C047_rowCode 2 := by decide +kernel

private theorem C047_row_03 : pack 256 (C047_digit 3)=C047_rowCode 3 := by decide +kernel

private theorem C047_row_04 : pack 256 (C047_digit 4)=C047_rowCode 4 := by decide +kernel

private theorem C047_row_05 : pack 256 (C047_digit 5)=C047_rowCode 5 := by decide +kernel

private theorem C047_row_06 : pack 256 (C047_digit 6)=C047_rowCode 6 := by decide +kernel

private theorem C047_row_07 : pack 256 (C047_digit 7)=C047_rowCode 7 := by decide +kernel

private theorem C047_row_08 : pack 256 (C047_digit 8)=C047_rowCode 8 := by decide +kernel

private theorem C047_row_09 : pack 256 (C047_digit 9)=C047_rowCode 9 := by decide +kernel

private theorem C047_row_10 : pack 256 (C047_digit 10)=C047_rowCode 10 := by decide +kernel

private theorem C047_row_11 : pack 256 (C047_digit 11)=C047_rowCode 11 := by decide +kernel

private theorem C047_row_12 : pack 256 (C047_digit 12)=C047_rowCode 12 := by decide +kernel

private theorem C047_row_13 : pack 256 (C047_digit 13)=C047_rowCode 13 := by decide +kernel

theorem C047_row_binding : ∀ i : Fin 14, pack 256 (C047_digit i)=C047_rowCode i := by
  intro i
  fin_cases i
  · exact C047_row_00
  · exact C047_row_01
  · exact C047_row_02
  · exact C047_row_03
  · exact C047_row_04
  · exact C047_row_05
  · exact C047_row_06
  · exact C047_row_07
  · exact C047_row_08
  · exact C047_row_09
  · exact C047_row_10
  · exact C047_row_11
  · exact C047_row_12
  · exact C047_row_13

private theorem C047_column_00 : reversePack 256 (fun j : Fin 14 => C047_digit j 0)=C047_columnCode 0 := by decide +kernel

private theorem C047_column_01 : reversePack 256 (fun j : Fin 14 => C047_digit j 1)=C047_columnCode 1 := by decide +kernel

private theorem C047_column_02 : reversePack 256 (fun j : Fin 14 => C047_digit j 2)=C047_columnCode 2 := by decide +kernel

private theorem C047_column_03 : reversePack 256 (fun j : Fin 14 => C047_digit j 3)=C047_columnCode 3 := by decide +kernel

private theorem C047_column_04 : reversePack 256 (fun j : Fin 14 => C047_digit j 4)=C047_columnCode 4 := by decide +kernel

private theorem C047_column_05 : reversePack 256 (fun j : Fin 14 => C047_digit j 5)=C047_columnCode 5 := by decide +kernel

private theorem C047_column_06 : reversePack 256 (fun j : Fin 14 => C047_digit j 6)=C047_columnCode 6 := by decide +kernel

private theorem C047_column_07 : reversePack 256 (fun j : Fin 14 => C047_digit j 7)=C047_columnCode 7 := by decide +kernel

private theorem C047_column_08 : reversePack 256 (fun j : Fin 14 => C047_digit j 8)=C047_columnCode 8 := by decide +kernel

private theorem C047_column_09 : reversePack 256 (fun j : Fin 14 => C047_digit j 9)=C047_columnCode 9 := by decide +kernel

private theorem C047_column_10 : reversePack 256 (fun j : Fin 14 => C047_digit j 10)=C047_columnCode 10 := by decide +kernel

private theorem C047_column_11 : reversePack 256 (fun j : Fin 14 => C047_digit j 11)=C047_columnCode 11 := by decide +kernel

private theorem C047_column_12 : reversePack 256 (fun j : Fin 14 => C047_digit j 12)=C047_columnCode 12 := by decide +kernel

private theorem C047_column_13 : reversePack 256 (fun j : Fin 14 => C047_digit j 13)=C047_columnCode 13 := by decide +kernel

theorem C047_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C047_digit j i)=C047_columnCode i := by
  intro i
  fin_cases i
  · exact C047_column_00
  · exact C047_column_01
  · exact C047_column_02
  · exact C047_column_03
  · exact C047_column_04
  · exact C047_column_05
  · exact C047_column_06
  · exact C047_column_07
  · exact C047_column_08
  · exact C047_column_09
  · exact C047_column_10
  · exact C047_column_11
  · exact C047_column_12
  · exact C047_column_13

def C047_data : PackedData 14 5 256 where
  raw := C047_digit
  digit_lt := C047_bound
  rowCode := C047_rowCode
  columnCode := C047_columnCode
  row_binding := C047_row_binding
  column_binding := C047_column_binding

def C050_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 1754786285139
  | 1 => 554460559371
  | 2 => 850573694747
  | 3 => 309294531234
  | 4 => 1327681799315
  | 5 => 1676300629251
  | 6 => 407487244
  | 7 => 657283233380
  | 8 => 1332551451787
  | 9 => 19655411281
  | 10 => 2236882093323
  | 11 => 1196203319904
  | 12 => 1671219525825
  | 13 => 236366373449
  | _ => 0

def C050_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 20361641397721389680106605314819
  | 1 => 20283648762080243640524110758146
  | 2 => 20520408416666896399230986092545
  | 3 => 20599634170774397741869576684547
  | 4 => 40803122683755459784271720416004
  | 5 => 20600560207970741913530302267651
  | 6 => 40882046192240598016711542768386
  | 7 => 81367946726798827899592850342659
  | 8 => 317841119290586383229328162817
  | 9 => 20520096518490908534861182599938
  | 10 => 81447173670924308521493997814786
  | 11 => 61006618436216643872395477843972
  | 12 => 60847538296020244906738597494785
  | 13 => 238308293302679710483362152707
  | _ => 0

def C050_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 61005998266715771260405941534979
  | 1 => 60926461823358317277854637752321
  | 2 => 61086154870055434077000496776193
  | 3 => 40882352036305933408352805848064
  | 4 => 61006306523873268610515597394690
  | 5 => 60848469183068592301239980720131
  | 6 => 81210105745031001870137246613504
  | 7 => 81446864190691905942602054369537
  | 8 => 60927078361395898326201219089154
  | 9 => 20441179059412502753779476725760
  | 10 => 60927697331360489575253245427716
  | 11 => 317223353511290875948763906306
  | 12 => 20283342908625588421785978798083
  | 13 => 20361948469564900672144039674624
  | _ => 0

def C050_digit (i j : Fin 14) : ℕ := packedDigit 3 (C050_lowColumnCode j) i.val

private theorem C050_bound_00 : ∀ j : Fin 14, C050_digit 0 j < 5 := by decide +kernel

private theorem C050_bound_01 : ∀ j : Fin 14, C050_digit 1 j < 5 := by decide +kernel

private theorem C050_bound_02 : ∀ j : Fin 14, C050_digit 2 j < 5 := by decide +kernel

private theorem C050_bound_03 : ∀ j : Fin 14, C050_digit 3 j < 5 := by decide +kernel

private theorem C050_bound_04 : ∀ j : Fin 14, C050_digit 4 j < 5 := by decide +kernel

private theorem C050_bound_05 : ∀ j : Fin 14, C050_digit 5 j < 5 := by decide +kernel

private theorem C050_bound_06 : ∀ j : Fin 14, C050_digit 6 j < 5 := by decide +kernel

private theorem C050_bound_07 : ∀ j : Fin 14, C050_digit 7 j < 5 := by decide +kernel

private theorem C050_bound_08 : ∀ j : Fin 14, C050_digit 8 j < 5 := by decide +kernel

private theorem C050_bound_09 : ∀ j : Fin 14, C050_digit 9 j < 5 := by decide +kernel

private theorem C050_bound_10 : ∀ j : Fin 14, C050_digit 10 j < 5 := by decide +kernel

private theorem C050_bound_11 : ∀ j : Fin 14, C050_digit 11 j < 5 := by decide +kernel

private theorem C050_bound_12 : ∀ j : Fin 14, C050_digit 12 j < 5 := by decide +kernel

private theorem C050_bound_13 : ∀ j : Fin 14, C050_digit 13 j < 5 := by decide +kernel

theorem C050_bound : ∀ i j : Fin 14, C050_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C050_bound_00 j
  · exact C050_bound_01 j
  · exact C050_bound_02 j
  · exact C050_bound_03 j
  · exact C050_bound_04 j
  · exact C050_bound_05 j
  · exact C050_bound_06 j
  · exact C050_bound_07 j
  · exact C050_bound_08 j
  · exact C050_bound_09 j
  · exact C050_bound_10 j
  · exact C050_bound_11 j
  · exact C050_bound_12 j
  · exact C050_bound_13 j

private theorem C050_row_00 : pack 256 (C050_digit 0)=C050_rowCode 0 := by decide +kernel

private theorem C050_row_01 : pack 256 (C050_digit 1)=C050_rowCode 1 := by decide +kernel

private theorem C050_row_02 : pack 256 (C050_digit 2)=C050_rowCode 2 := by decide +kernel

private theorem C050_row_03 : pack 256 (C050_digit 3)=C050_rowCode 3 := by decide +kernel

private theorem C050_row_04 : pack 256 (C050_digit 4)=C050_rowCode 4 := by decide +kernel

private theorem C050_row_05 : pack 256 (C050_digit 5)=C050_rowCode 5 := by decide +kernel

private theorem C050_row_06 : pack 256 (C050_digit 6)=C050_rowCode 6 := by decide +kernel

private theorem C050_row_07 : pack 256 (C050_digit 7)=C050_rowCode 7 := by decide +kernel

private theorem C050_row_08 : pack 256 (C050_digit 8)=C050_rowCode 8 := by decide +kernel

private theorem C050_row_09 : pack 256 (C050_digit 9)=C050_rowCode 9 := by decide +kernel

private theorem C050_row_10 : pack 256 (C050_digit 10)=C050_rowCode 10 := by decide +kernel

private theorem C050_row_11 : pack 256 (C050_digit 11)=C050_rowCode 11 := by decide +kernel

private theorem C050_row_12 : pack 256 (C050_digit 12)=C050_rowCode 12 := by decide +kernel

private theorem C050_row_13 : pack 256 (C050_digit 13)=C050_rowCode 13 := by decide +kernel

theorem C050_row_binding : ∀ i : Fin 14, pack 256 (C050_digit i)=C050_rowCode i := by
  intro i
  fin_cases i
  · exact C050_row_00
  · exact C050_row_01
  · exact C050_row_02
  · exact C050_row_03
  · exact C050_row_04
  · exact C050_row_05
  · exact C050_row_06
  · exact C050_row_07
  · exact C050_row_08
  · exact C050_row_09
  · exact C050_row_10
  · exact C050_row_11
  · exact C050_row_12
  · exact C050_row_13

private theorem C050_column_00 : reversePack 256 (fun j : Fin 14 => C050_digit j 0)=C050_columnCode 0 := by decide +kernel

private theorem C050_column_01 : reversePack 256 (fun j : Fin 14 => C050_digit j 1)=C050_columnCode 1 := by decide +kernel

private theorem C050_column_02 : reversePack 256 (fun j : Fin 14 => C050_digit j 2)=C050_columnCode 2 := by decide +kernel

private theorem C050_column_03 : reversePack 256 (fun j : Fin 14 => C050_digit j 3)=C050_columnCode 3 := by decide +kernel

private theorem C050_column_04 : reversePack 256 (fun j : Fin 14 => C050_digit j 4)=C050_columnCode 4 := by decide +kernel

private theorem C050_column_05 : reversePack 256 (fun j : Fin 14 => C050_digit j 5)=C050_columnCode 5 := by decide +kernel

private theorem C050_column_06 : reversePack 256 (fun j : Fin 14 => C050_digit j 6)=C050_columnCode 6 := by decide +kernel

private theorem C050_column_07 : reversePack 256 (fun j : Fin 14 => C050_digit j 7)=C050_columnCode 7 := by decide +kernel

private theorem C050_column_08 : reversePack 256 (fun j : Fin 14 => C050_digit j 8)=C050_columnCode 8 := by decide +kernel

private theorem C050_column_09 : reversePack 256 (fun j : Fin 14 => C050_digit j 9)=C050_columnCode 9 := by decide +kernel

private theorem C050_column_10 : reversePack 256 (fun j : Fin 14 => C050_digit j 10)=C050_columnCode 10 := by decide +kernel

private theorem C050_column_11 : reversePack 256 (fun j : Fin 14 => C050_digit j 11)=C050_columnCode 11 := by decide +kernel

private theorem C050_column_12 : reversePack 256 (fun j : Fin 14 => C050_digit j 12)=C050_columnCode 12 := by decide +kernel

private theorem C050_column_13 : reversePack 256 (fun j : Fin 14 => C050_digit j 13)=C050_columnCode 13 := by decide +kernel

theorem C050_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C050_digit j i)=C050_columnCode i := by
  intro i
  fin_cases i
  · exact C050_column_00
  · exact C050_column_01
  · exact C050_column_02
  · exact C050_column_03
  · exact C050_column_04
  · exact C050_column_05
  · exact C050_column_06
  · exact C050_column_07
  · exact C050_column_08
  · exact C050_column_09
  · exact C050_column_10
  · exact C050_column_11
  · exact C050_column_12
  · exact C050_column_13

def C050_data : PackedData 14 5 256 where
  raw := C050_digit
  digit_lt := C050_bound
  rowCode := C050_rowCode
  columnCode := C050_columnCode
  row_binding := C050_row_binding
  column_binding := C050_column_binding

end SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedCaches05
