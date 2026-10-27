import SymmetricSubgroupAsymptotics.MatrixKroneckerProductReflection
import Mathlib.Tactic.FinCases

/-! Literal14/F5 selected caches; digit bounds and both pack bindings are independently kernel checked. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedCaches02
open MatrixKroneckerProductReflection MatrixKroneckerDotReflection
open MatrixNaturalRowDotReflection SmallNaturalMatrixProductReflection

def C015_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 1791295557905
  | 1 => 285003819097
  | 2 => 2225405961954
  | 3 => 206597275787
  | 4 => 1128979302596
  | 5 => 1135152992864
  | 6 => 1788065399812
  | 7 => 141101727828
  | 8 => 1661486088204
  | 9 => 13422827169
  | 10 => 577673447586
  | 11 => 724111229473
  | 12 => 851905480396
  | 13 => 2235539404900
  | _ => 0

def C015_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 81446862972321642435948027445505
  | 1 => 81210109371771566667312576856834
  | 2 => 20520096518490907690431991185668
  | 3 => 81367637237029674524830641357824
  | 4 => 60847233651454444316522421813761
  | 5 => 317224552974074611188059079170
  | 6 => 40644358082679893796296232928002
  | 7 => 81447479519730240688016287073284
  | 8 => 79228162514408738671856714497
  | 9 => 238612961517279948531030033154
  | 10 => 40644668776633909723953042030852
  | 11 => 81368564473707032164086346612992
  | 12 => 317531620076844718649704973314
  | 13 => 81209177271111928071934120820739
  | _ => 0

def C015_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 20442103873478889692622453998083
  | 1 => 20520408421389406996193473528832
  | 2 => 40882663948612199288604876537860
  | 3 => 60927075962378528629926288950016
  | 4 => 81130571705376462641683285344258
  | 5 => 317223348715137699363047079938
  | 6 => 81129640851366233601707763302915
  | 7 => 81288404224700660743804010103296
  | 8 => 81208866596065896875233223180291
  | 9 => 20599944855228484021609444737024
  | 10 => 40882355682009750824142898397185
  | 11 => 20599323462653067035056198124033
  | 12 => 81209798659001729073377444037633
  | 13 => 81446865399544083539445556707332
  | _ => 0

def C015_digit (i j : Fin 14) : ℕ := packedDigit 3 (C015_lowColumnCode j) i.val

private theorem C015_bound_00 : ∀ j : Fin 14, C015_digit 0 j < 5 := by decide +kernel

private theorem C015_bound_01 : ∀ j : Fin 14, C015_digit 1 j < 5 := by decide +kernel

private theorem C015_bound_02 : ∀ j : Fin 14, C015_digit 2 j < 5 := by decide +kernel

private theorem C015_bound_03 : ∀ j : Fin 14, C015_digit 3 j < 5 := by decide +kernel

private theorem C015_bound_04 : ∀ j : Fin 14, C015_digit 4 j < 5 := by decide +kernel

private theorem C015_bound_05 : ∀ j : Fin 14, C015_digit 5 j < 5 := by decide +kernel

private theorem C015_bound_06 : ∀ j : Fin 14, C015_digit 6 j < 5 := by decide +kernel

private theorem C015_bound_07 : ∀ j : Fin 14, C015_digit 7 j < 5 := by decide +kernel

private theorem C015_bound_08 : ∀ j : Fin 14, C015_digit 8 j < 5 := by decide +kernel

private theorem C015_bound_09 : ∀ j : Fin 14, C015_digit 9 j < 5 := by decide +kernel

private theorem C015_bound_10 : ∀ j : Fin 14, C015_digit 10 j < 5 := by decide +kernel

private theorem C015_bound_11 : ∀ j : Fin 14, C015_digit 11 j < 5 := by decide +kernel

private theorem C015_bound_12 : ∀ j : Fin 14, C015_digit 12 j < 5 := by decide +kernel

private theorem C015_bound_13 : ∀ j : Fin 14, C015_digit 13 j < 5 := by decide +kernel

theorem C015_bound : ∀ i j : Fin 14, C015_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C015_bound_00 j
  · exact C015_bound_01 j
  · exact C015_bound_02 j
  · exact C015_bound_03 j
  · exact C015_bound_04 j
  · exact C015_bound_05 j
  · exact C015_bound_06 j
  · exact C015_bound_07 j
  · exact C015_bound_08 j
  · exact C015_bound_09 j
  · exact C015_bound_10 j
  · exact C015_bound_11 j
  · exact C015_bound_12 j
  · exact C015_bound_13 j

private theorem C015_row_00 : pack 256 (C015_digit 0)=C015_rowCode 0 := by decide +kernel

private theorem C015_row_01 : pack 256 (C015_digit 1)=C015_rowCode 1 := by decide +kernel

private theorem C015_row_02 : pack 256 (C015_digit 2)=C015_rowCode 2 := by decide +kernel

private theorem C015_row_03 : pack 256 (C015_digit 3)=C015_rowCode 3 := by decide +kernel

private theorem C015_row_04 : pack 256 (C015_digit 4)=C015_rowCode 4 := by decide +kernel

private theorem C015_row_05 : pack 256 (C015_digit 5)=C015_rowCode 5 := by decide +kernel

private theorem C015_row_06 : pack 256 (C015_digit 6)=C015_rowCode 6 := by decide +kernel

private theorem C015_row_07 : pack 256 (C015_digit 7)=C015_rowCode 7 := by decide +kernel

private theorem C015_row_08 : pack 256 (C015_digit 8)=C015_rowCode 8 := by decide +kernel

private theorem C015_row_09 : pack 256 (C015_digit 9)=C015_rowCode 9 := by decide +kernel

private theorem C015_row_10 : pack 256 (C015_digit 10)=C015_rowCode 10 := by decide +kernel

private theorem C015_row_11 : pack 256 (C015_digit 11)=C015_rowCode 11 := by decide +kernel

private theorem C015_row_12 : pack 256 (C015_digit 12)=C015_rowCode 12 := by decide +kernel

private theorem C015_row_13 : pack 256 (C015_digit 13)=C015_rowCode 13 := by decide +kernel

theorem C015_row_binding : ∀ i : Fin 14, pack 256 (C015_digit i)=C015_rowCode i := by
  intro i
  fin_cases i
  · exact C015_row_00
  · exact C015_row_01
  · exact C015_row_02
  · exact C015_row_03
  · exact C015_row_04
  · exact C015_row_05
  · exact C015_row_06
  · exact C015_row_07
  · exact C015_row_08
  · exact C015_row_09
  · exact C015_row_10
  · exact C015_row_11
  · exact C015_row_12
  · exact C015_row_13

private theorem C015_column_00 : reversePack 256 (fun j : Fin 14 => C015_digit j 0)=C015_columnCode 0 := by decide +kernel

private theorem C015_column_01 : reversePack 256 (fun j : Fin 14 => C015_digit j 1)=C015_columnCode 1 := by decide +kernel

private theorem C015_column_02 : reversePack 256 (fun j : Fin 14 => C015_digit j 2)=C015_columnCode 2 := by decide +kernel

private theorem C015_column_03 : reversePack 256 (fun j : Fin 14 => C015_digit j 3)=C015_columnCode 3 := by decide +kernel

private theorem C015_column_04 : reversePack 256 (fun j : Fin 14 => C015_digit j 4)=C015_columnCode 4 := by decide +kernel

private theorem C015_column_05 : reversePack 256 (fun j : Fin 14 => C015_digit j 5)=C015_columnCode 5 := by decide +kernel

private theorem C015_column_06 : reversePack 256 (fun j : Fin 14 => C015_digit j 6)=C015_columnCode 6 := by decide +kernel

private theorem C015_column_07 : reversePack 256 (fun j : Fin 14 => C015_digit j 7)=C015_columnCode 7 := by decide +kernel

private theorem C015_column_08 : reversePack 256 (fun j : Fin 14 => C015_digit j 8)=C015_columnCode 8 := by decide +kernel

private theorem C015_column_09 : reversePack 256 (fun j : Fin 14 => C015_digit j 9)=C015_columnCode 9 := by decide +kernel

private theorem C015_column_10 : reversePack 256 (fun j : Fin 14 => C015_digit j 10)=C015_columnCode 10 := by decide +kernel

private theorem C015_column_11 : reversePack 256 (fun j : Fin 14 => C015_digit j 11)=C015_columnCode 11 := by decide +kernel

private theorem C015_column_12 : reversePack 256 (fun j : Fin 14 => C015_digit j 12)=C015_columnCode 12 := by decide +kernel

private theorem C015_column_13 : reversePack 256 (fun j : Fin 14 => C015_digit j 13)=C015_columnCode 13 := by decide +kernel

theorem C015_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C015_digit j i)=C015_columnCode i := by
  intro i
  fin_cases i
  · exact C015_column_00
  · exact C015_column_01
  · exact C015_column_02
  · exact C015_column_03
  · exact C015_column_04
  · exact C015_column_05
  · exact C015_column_06
  · exact C015_column_07
  · exact C015_column_08
  · exact C015_column_09
  · exact C015_column_10
  · exact C015_column_11
  · exact C015_column_12
  · exact C015_column_13

def C015_data : PackedData 14 5 256 where
  raw := C015_digit
  digit_lt := C015_bound
  rowCode := C015_rowCode
  columnCode := C015_columnCode
  row_binding := C015_row_binding
  column_binding := C015_column_binding

def C016_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 1127735935203
  | 1 => 2410072781843
  | 2 => 2340894291730
  | 3 => 233447765644
  | 4 => 98792912011
  | 5 => 2218558589024
  | 6 => 137975963852
  | 7 => 88607631634
  | 8 => 1813701563156
  | 9 => 164421441289
  | 10 => 1670880797699
  | 11 => 28513181778
  | 12 => 218173608530
  | 13 => 106703500938
  | _ => 0

def C016_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 40723898133925269757371982414595
  | 1 => 20441484903459246161354264019460
  | 2 => 40644356873790968514239407587331
  | 3 => 60926459405506749266159131099648
  | 4 => 60927078366081515433925416256260
  | 5 => 81288407851477976036540055289857
  | 6 => 20441175423171863071975761183235
  | 7 => 80468529850138088963978626050
  | 8 => 317841105105040191646177690370
  | 9 => 60927696127175483188658346984450
  | 10 => 61085537108961682777624184882178
  | 11 => 81209797464224633096077171490819
  | 12 => 20520094100676162511162929447680
  | 13 => 3626832799080506699547650
  | _ => 0

def C016_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 61165069934949662070914108555266
  | 1 => 61005687568002423869299891372804
  | 2 => 40724517113315929650114401927684
  | 3 => 81209489188159223350799280308992
  | 4 => 60927078375507730160934044500224
  | 5 => 317226970825570292602071285764
  | 6 => 81209795041668930010640031941120
  | 7 => 40724518317556276834083667050752
  | 8 => 81289333893378166197262840168963
  | 9 => 20362879337705190146715204911616
  | 10 => 60847231238306724262014837981187
  | 11 => 40723585026804943764773008506880
  | 12 => 40723586231026914854861998719744
  | 13 => 40644669980855665202023767474432
  | _ => 0

def C016_digit (i j : Fin 14) : ℕ := packedDigit 3 (C016_lowColumnCode j) i.val

private theorem C016_bound_00 : ∀ j : Fin 14, C016_digit 0 j < 5 := by decide +kernel

private theorem C016_bound_01 : ∀ j : Fin 14, C016_digit 1 j < 5 := by decide +kernel

private theorem C016_bound_02 : ∀ j : Fin 14, C016_digit 2 j < 5 := by decide +kernel

private theorem C016_bound_03 : ∀ j : Fin 14, C016_digit 3 j < 5 := by decide +kernel

private theorem C016_bound_04 : ∀ j : Fin 14, C016_digit 4 j < 5 := by decide +kernel

private theorem C016_bound_05 : ∀ j : Fin 14, C016_digit 5 j < 5 := by decide +kernel

private theorem C016_bound_06 : ∀ j : Fin 14, C016_digit 6 j < 5 := by decide +kernel

private theorem C016_bound_07 : ∀ j : Fin 14, C016_digit 7 j < 5 := by decide +kernel

private theorem C016_bound_08 : ∀ j : Fin 14, C016_digit 8 j < 5 := by decide +kernel

private theorem C016_bound_09 : ∀ j : Fin 14, C016_digit 9 j < 5 := by decide +kernel

private theorem C016_bound_10 : ∀ j : Fin 14, C016_digit 10 j < 5 := by decide +kernel

private theorem C016_bound_11 : ∀ j : Fin 14, C016_digit 11 j < 5 := by decide +kernel

private theorem C016_bound_12 : ∀ j : Fin 14, C016_digit 12 j < 5 := by decide +kernel

private theorem C016_bound_13 : ∀ j : Fin 14, C016_digit 13 j < 5 := by decide +kernel

theorem C016_bound : ∀ i j : Fin 14, C016_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C016_bound_00 j
  · exact C016_bound_01 j
  · exact C016_bound_02 j
  · exact C016_bound_03 j
  · exact C016_bound_04 j
  · exact C016_bound_05 j
  · exact C016_bound_06 j
  · exact C016_bound_07 j
  · exact C016_bound_08 j
  · exact C016_bound_09 j
  · exact C016_bound_10 j
  · exact C016_bound_11 j
  · exact C016_bound_12 j
  · exact C016_bound_13 j

private theorem C016_row_00 : pack 256 (C016_digit 0)=C016_rowCode 0 := by decide +kernel

private theorem C016_row_01 : pack 256 (C016_digit 1)=C016_rowCode 1 := by decide +kernel

private theorem C016_row_02 : pack 256 (C016_digit 2)=C016_rowCode 2 := by decide +kernel

private theorem C016_row_03 : pack 256 (C016_digit 3)=C016_rowCode 3 := by decide +kernel

private theorem C016_row_04 : pack 256 (C016_digit 4)=C016_rowCode 4 := by decide +kernel

private theorem C016_row_05 : pack 256 (C016_digit 5)=C016_rowCode 5 := by decide +kernel

private theorem C016_row_06 : pack 256 (C016_digit 6)=C016_rowCode 6 := by decide +kernel

private theorem C016_row_07 : pack 256 (C016_digit 7)=C016_rowCode 7 := by decide +kernel

private theorem C016_row_08 : pack 256 (C016_digit 8)=C016_rowCode 8 := by decide +kernel

private theorem C016_row_09 : pack 256 (C016_digit 9)=C016_rowCode 9 := by decide +kernel

private theorem C016_row_10 : pack 256 (C016_digit 10)=C016_rowCode 10 := by decide +kernel

private theorem C016_row_11 : pack 256 (C016_digit 11)=C016_rowCode 11 := by decide +kernel

private theorem C016_row_12 : pack 256 (C016_digit 12)=C016_rowCode 12 := by decide +kernel

private theorem C016_row_13 : pack 256 (C016_digit 13)=C016_rowCode 13 := by decide +kernel

theorem C016_row_binding : ∀ i : Fin 14, pack 256 (C016_digit i)=C016_rowCode i := by
  intro i
  fin_cases i
  · exact C016_row_00
  · exact C016_row_01
  · exact C016_row_02
  · exact C016_row_03
  · exact C016_row_04
  · exact C016_row_05
  · exact C016_row_06
  · exact C016_row_07
  · exact C016_row_08
  · exact C016_row_09
  · exact C016_row_10
  · exact C016_row_11
  · exact C016_row_12
  · exact C016_row_13

private theorem C016_column_00 : reversePack 256 (fun j : Fin 14 => C016_digit j 0)=C016_columnCode 0 := by decide +kernel

private theorem C016_column_01 : reversePack 256 (fun j : Fin 14 => C016_digit j 1)=C016_columnCode 1 := by decide +kernel

private theorem C016_column_02 : reversePack 256 (fun j : Fin 14 => C016_digit j 2)=C016_columnCode 2 := by decide +kernel

private theorem C016_column_03 : reversePack 256 (fun j : Fin 14 => C016_digit j 3)=C016_columnCode 3 := by decide +kernel

private theorem C016_column_04 : reversePack 256 (fun j : Fin 14 => C016_digit j 4)=C016_columnCode 4 := by decide +kernel

private theorem C016_column_05 : reversePack 256 (fun j : Fin 14 => C016_digit j 5)=C016_columnCode 5 := by decide +kernel

private theorem C016_column_06 : reversePack 256 (fun j : Fin 14 => C016_digit j 6)=C016_columnCode 6 := by decide +kernel

private theorem C016_column_07 : reversePack 256 (fun j : Fin 14 => C016_digit j 7)=C016_columnCode 7 := by decide +kernel

private theorem C016_column_08 : reversePack 256 (fun j : Fin 14 => C016_digit j 8)=C016_columnCode 8 := by decide +kernel

private theorem C016_column_09 : reversePack 256 (fun j : Fin 14 => C016_digit j 9)=C016_columnCode 9 := by decide +kernel

private theorem C016_column_10 : reversePack 256 (fun j : Fin 14 => C016_digit j 10)=C016_columnCode 10 := by decide +kernel

private theorem C016_column_11 : reversePack 256 (fun j : Fin 14 => C016_digit j 11)=C016_columnCode 11 := by decide +kernel

private theorem C016_column_12 : reversePack 256 (fun j : Fin 14 => C016_digit j 12)=C016_columnCode 12 := by decide +kernel

private theorem C016_column_13 : reversePack 256 (fun j : Fin 14 => C016_digit j 13)=C016_columnCode 13 := by decide +kernel

theorem C016_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C016_digit j i)=C016_columnCode i := by
  intro i
  fin_cases i
  · exact C016_column_00
  · exact C016_column_01
  · exact C016_column_02
  · exact C016_column_03
  · exact C016_column_04
  · exact C016_column_05
  · exact C016_column_06
  · exact C016_column_07
  · exact C016_column_08
  · exact C016_column_09
  · exact C016_column_10
  · exact C016_column_11
  · exact C016_column_12
  · exact C016_column_13

def C016_data : PackedData 14 5 256 where
  raw := C016_digit
  digit_lt := C016_bound
  rowCode := C016_rowCode
  columnCode := C016_columnCode
  row_binding := C016_row_binding
  column_binding := C016_column_binding

def C017_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 2441085601292
  | 1 => 1925544289292
  | 2 => 2364849826018
  | 3 => 2207948744928
  | 4 => 2293917885065
  | 5 => 39250593371
  | 6 => 1666454455825
  | 7 => 1378200650332
  | 8 => 1825420429404
  | 9 => 1812798181571
  | 10 => 1112684136483
  | 11 => 1856017309762
  | 12 => 577992168145
  | 13 => 2293714465540
  | _ => 0

def C017_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 81209489188159222507465255027716
  | 1 => 158461160787364104959879807233
  | 2 => 81367632401344914305023196987392
  | 3 => 20361642601943073101674197549571
  | 4 => 60927075948285071758745854411268
  | 5 => 40644358073235017278318786446340
  | 6 => 40644048597669929180464328867842
  | 7 => 620183741688670352417227520
  | 8 => 81368252580327414215315766379268
  | 9 => 20442106296016144909193995026947
  | 10 => 158461160805810287178785358081
  | 11 => 61084914521664510891516236070916
  | 12 => 20283338068163049143420581970947
  | 13 => 81209797464224633938307390374660
  | _ => 0

def C017_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 81208870222861801904642516583172
  | 1 => 81208869004491106052407098868739
  | 2 => 40882665157556464521403592540676
  | 3 => 317845950234532814242975907844
  | 4 => 20362257954593167916870066700548
  | 5 => 61085226410303604404462071054336
  | 6 => 20440869555494768448376326455299
  | 7 => 81367633596122153556393773237250
  | 8 => 81367637241789079176167645512195
  | 9 => 60848157270744023793223245955587
  | 10 => 61164146296733866164983521411074
  | 11 => 40565128701776342469041895506691
  | 12 => 20441795597376368036814239498241
  | 13 => 81130877577775923747039851249924
  | _ => 0

def C017_digit (i j : Fin 14) : ℕ := packedDigit 3 (C017_lowColumnCode j) i.val

private theorem C017_bound_00 : ∀ j : Fin 14, C017_digit 0 j < 5 := by decide +kernel

private theorem C017_bound_01 : ∀ j : Fin 14, C017_digit 1 j < 5 := by decide +kernel

private theorem C017_bound_02 : ∀ j : Fin 14, C017_digit 2 j < 5 := by decide +kernel

private theorem C017_bound_03 : ∀ j : Fin 14, C017_digit 3 j < 5 := by decide +kernel

private theorem C017_bound_04 : ∀ j : Fin 14, C017_digit 4 j < 5 := by decide +kernel

private theorem C017_bound_05 : ∀ j : Fin 14, C017_digit 5 j < 5 := by decide +kernel

private theorem C017_bound_06 : ∀ j : Fin 14, C017_digit 6 j < 5 := by decide +kernel

private theorem C017_bound_07 : ∀ j : Fin 14, C017_digit 7 j < 5 := by decide +kernel

private theorem C017_bound_08 : ∀ j : Fin 14, C017_digit 8 j < 5 := by decide +kernel

private theorem C017_bound_09 : ∀ j : Fin 14, C017_digit 9 j < 5 := by decide +kernel

private theorem C017_bound_10 : ∀ j : Fin 14, C017_digit 10 j < 5 := by decide +kernel

private theorem C017_bound_11 : ∀ j : Fin 14, C017_digit 11 j < 5 := by decide +kernel

private theorem C017_bound_12 : ∀ j : Fin 14, C017_digit 12 j < 5 := by decide +kernel

private theorem C017_bound_13 : ∀ j : Fin 14, C017_digit 13 j < 5 := by decide +kernel

theorem C017_bound : ∀ i j : Fin 14, C017_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C017_bound_00 j
  · exact C017_bound_01 j
  · exact C017_bound_02 j
  · exact C017_bound_03 j
  · exact C017_bound_04 j
  · exact C017_bound_05 j
  · exact C017_bound_06 j
  · exact C017_bound_07 j
  · exact C017_bound_08 j
  · exact C017_bound_09 j
  · exact C017_bound_10 j
  · exact C017_bound_11 j
  · exact C017_bound_12 j
  · exact C017_bound_13 j

private theorem C017_row_00 : pack 256 (C017_digit 0)=C017_rowCode 0 := by decide +kernel

private theorem C017_row_01 : pack 256 (C017_digit 1)=C017_rowCode 1 := by decide +kernel

private theorem C017_row_02 : pack 256 (C017_digit 2)=C017_rowCode 2 := by decide +kernel

private theorem C017_row_03 : pack 256 (C017_digit 3)=C017_rowCode 3 := by decide +kernel

private theorem C017_row_04 : pack 256 (C017_digit 4)=C017_rowCode 4 := by decide +kernel

private theorem C017_row_05 : pack 256 (C017_digit 5)=C017_rowCode 5 := by decide +kernel

private theorem C017_row_06 : pack 256 (C017_digit 6)=C017_rowCode 6 := by decide +kernel

private theorem C017_row_07 : pack 256 (C017_digit 7)=C017_rowCode 7 := by decide +kernel

private theorem C017_row_08 : pack 256 (C017_digit 8)=C017_rowCode 8 := by decide +kernel

private theorem C017_row_09 : pack 256 (C017_digit 9)=C017_rowCode 9 := by decide +kernel

private theorem C017_row_10 : pack 256 (C017_digit 10)=C017_rowCode 10 := by decide +kernel

private theorem C017_row_11 : pack 256 (C017_digit 11)=C017_rowCode 11 := by decide +kernel

private theorem C017_row_12 : pack 256 (C017_digit 12)=C017_rowCode 12 := by decide +kernel

private theorem C017_row_13 : pack 256 (C017_digit 13)=C017_rowCode 13 := by decide +kernel

theorem C017_row_binding : ∀ i : Fin 14, pack 256 (C017_digit i)=C017_rowCode i := by
  intro i
  fin_cases i
  · exact C017_row_00
  · exact C017_row_01
  · exact C017_row_02
  · exact C017_row_03
  · exact C017_row_04
  · exact C017_row_05
  · exact C017_row_06
  · exact C017_row_07
  · exact C017_row_08
  · exact C017_row_09
  · exact C017_row_10
  · exact C017_row_11
  · exact C017_row_12
  · exact C017_row_13

private theorem C017_column_00 : reversePack 256 (fun j : Fin 14 => C017_digit j 0)=C017_columnCode 0 := by decide +kernel

private theorem C017_column_01 : reversePack 256 (fun j : Fin 14 => C017_digit j 1)=C017_columnCode 1 := by decide +kernel

private theorem C017_column_02 : reversePack 256 (fun j : Fin 14 => C017_digit j 2)=C017_columnCode 2 := by decide +kernel

private theorem C017_column_03 : reversePack 256 (fun j : Fin 14 => C017_digit j 3)=C017_columnCode 3 := by decide +kernel

private theorem C017_column_04 : reversePack 256 (fun j : Fin 14 => C017_digit j 4)=C017_columnCode 4 := by decide +kernel

private theorem C017_column_05 : reversePack 256 (fun j : Fin 14 => C017_digit j 5)=C017_columnCode 5 := by decide +kernel

private theorem C017_column_06 : reversePack 256 (fun j : Fin 14 => C017_digit j 6)=C017_columnCode 6 := by decide +kernel

private theorem C017_column_07 : reversePack 256 (fun j : Fin 14 => C017_digit j 7)=C017_columnCode 7 := by decide +kernel

private theorem C017_column_08 : reversePack 256 (fun j : Fin 14 => C017_digit j 8)=C017_columnCode 8 := by decide +kernel

private theorem C017_column_09 : reversePack 256 (fun j : Fin 14 => C017_digit j 9)=C017_columnCode 9 := by decide +kernel

private theorem C017_column_10 : reversePack 256 (fun j : Fin 14 => C017_digit j 10)=C017_columnCode 10 := by decide +kernel

private theorem C017_column_11 : reversePack 256 (fun j : Fin 14 => C017_digit j 11)=C017_columnCode 11 := by decide +kernel

private theorem C017_column_12 : reversePack 256 (fun j : Fin 14 => C017_digit j 12)=C017_columnCode 12 := by decide +kernel

private theorem C017_column_13 : reversePack 256 (fun j : Fin 14 => C017_digit j 13)=C017_columnCode 13 := by decide +kernel

theorem C017_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C017_digit j i)=C017_columnCode i := by
  intro i
  fin_cases i
  · exact C017_column_00
  · exact C017_column_01
  · exact C017_column_02
  · exact C017_column_03
  · exact C017_column_04
  · exact C017_column_05
  · exact C017_column_06
  · exact C017_column_07
  · exact C017_column_08
  · exact C017_column_09
  · exact C017_column_10
  · exact C017_column_11
  · exact C017_column_12
  · exact C017_column_13

def C017_data : PackedData 14 5 256 where
  raw := C017_digit
  digit_lt := C017_bound
  rowCode := C017_rowCode
  columnCode := C017_columnCode
  row_binding := C017_row_binding
  column_binding := C017_column_binding

def C018_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 1343843254946
  | 1 => 775378765348
  | 2 => 1378707707931
  | 3 => 292079599905
  | 4 => 2442923218706
  | 5 => 233173029650
  | 6 => 313568278562
  | 7 => 30624849995
  | 8 => 25778258944
  | 9 => 18524743316
  | 10 => 1935156319442
  | 11 => 1377143985363
  | 12 => 577992168145
  | 13 => 2293714465540
  | _ => 0

def C018_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 81209797468891731967265351074818
  | 1 => 159077722344616746023802569732
  | 2 => 81368254993401202615411957301250
  | 3 => 20362259168241210744705252590337
  | 4 => 60926767676849794495589300371460
  | 5 => 40644980670032262367889041129985
  | 6 => 40644979461069261034736312124163
  | 7 => 311907657830488865373356290
  | 8 => 81368560842188832711591862534147
  | 9 => 20442106296016144905886836457732
  | 10 => 159077717622466434840987435523
  | 11 => 61084914516923914399209748431364
  | 12 => 20283652379394235391950243234563
  | 13 => 81209489173918047567424702775554
  | _ => 0

def C018_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 40882352055213989917635425600258
  | 1 => 81446554691478307832459543315201
  | 2 => 61084918138997237047828076823554
  | 3 => 20600560193785123379575324279808
  | 4 => 40724517103945056563788412879620
  | 5 => 40724514686093416491204611343104
  | 6 => 40881736707230776389068380177408
  | 7 => 60926766467997617742079840157696
  | 8 => 2417888533843305675554816
  | 9 => 81288717345914082755559435665408
  | 10 => 40724206410009342982451288409091
  | 11 => 61006616013642566385256489812994
  | 12 => 20441795597376368036814239498241
  | 13 => 81130877577775923747039851249924
  | _ => 0

def C018_digit (i j : Fin 14) : ℕ := packedDigit 3 (C018_lowColumnCode j) i.val

private theorem C018_bound_00 : ∀ j : Fin 14, C018_digit 0 j < 5 := by decide +kernel

private theorem C018_bound_01 : ∀ j : Fin 14, C018_digit 1 j < 5 := by decide +kernel

private theorem C018_bound_02 : ∀ j : Fin 14, C018_digit 2 j < 5 := by decide +kernel

private theorem C018_bound_03 : ∀ j : Fin 14, C018_digit 3 j < 5 := by decide +kernel

private theorem C018_bound_04 : ∀ j : Fin 14, C018_digit 4 j < 5 := by decide +kernel

private theorem C018_bound_05 : ∀ j : Fin 14, C018_digit 5 j < 5 := by decide +kernel

private theorem C018_bound_06 : ∀ j : Fin 14, C018_digit 6 j < 5 := by decide +kernel

private theorem C018_bound_07 : ∀ j : Fin 14, C018_digit 7 j < 5 := by decide +kernel

private theorem C018_bound_08 : ∀ j : Fin 14, C018_digit 8 j < 5 := by decide +kernel

private theorem C018_bound_09 : ∀ j : Fin 14, C018_digit 9 j < 5 := by decide +kernel

private theorem C018_bound_10 : ∀ j : Fin 14, C018_digit 10 j < 5 := by decide +kernel

private theorem C018_bound_11 : ∀ j : Fin 14, C018_digit 11 j < 5 := by decide +kernel

private theorem C018_bound_12 : ∀ j : Fin 14, C018_digit 12 j < 5 := by decide +kernel

private theorem C018_bound_13 : ∀ j : Fin 14, C018_digit 13 j < 5 := by decide +kernel

theorem C018_bound : ∀ i j : Fin 14, C018_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C018_bound_00 j
  · exact C018_bound_01 j
  · exact C018_bound_02 j
  · exact C018_bound_03 j
  · exact C018_bound_04 j
  · exact C018_bound_05 j
  · exact C018_bound_06 j
  · exact C018_bound_07 j
  · exact C018_bound_08 j
  · exact C018_bound_09 j
  · exact C018_bound_10 j
  · exact C018_bound_11 j
  · exact C018_bound_12 j
  · exact C018_bound_13 j

private theorem C018_row_00 : pack 256 (C018_digit 0)=C018_rowCode 0 := by decide +kernel

private theorem C018_row_01 : pack 256 (C018_digit 1)=C018_rowCode 1 := by decide +kernel

private theorem C018_row_02 : pack 256 (C018_digit 2)=C018_rowCode 2 := by decide +kernel

private theorem C018_row_03 : pack 256 (C018_digit 3)=C018_rowCode 3 := by decide +kernel

private theorem C018_row_04 : pack 256 (C018_digit 4)=C018_rowCode 4 := by decide +kernel

private theorem C018_row_05 : pack 256 (C018_digit 5)=C018_rowCode 5 := by decide +kernel

private theorem C018_row_06 : pack 256 (C018_digit 6)=C018_rowCode 6 := by decide +kernel

private theorem C018_row_07 : pack 256 (C018_digit 7)=C018_rowCode 7 := by decide +kernel

private theorem C018_row_08 : pack 256 (C018_digit 8)=C018_rowCode 8 := by decide +kernel

private theorem C018_row_09 : pack 256 (C018_digit 9)=C018_rowCode 9 := by decide +kernel

private theorem C018_row_10 : pack 256 (C018_digit 10)=C018_rowCode 10 := by decide +kernel

private theorem C018_row_11 : pack 256 (C018_digit 11)=C018_rowCode 11 := by decide +kernel

private theorem C018_row_12 : pack 256 (C018_digit 12)=C018_rowCode 12 := by decide +kernel

private theorem C018_row_13 : pack 256 (C018_digit 13)=C018_rowCode 13 := by decide +kernel

theorem C018_row_binding : ∀ i : Fin 14, pack 256 (C018_digit i)=C018_rowCode i := by
  intro i
  fin_cases i
  · exact C018_row_00
  · exact C018_row_01
  · exact C018_row_02
  · exact C018_row_03
  · exact C018_row_04
  · exact C018_row_05
  · exact C018_row_06
  · exact C018_row_07
  · exact C018_row_08
  · exact C018_row_09
  · exact C018_row_10
  · exact C018_row_11
  · exact C018_row_12
  · exact C018_row_13

private theorem C018_column_00 : reversePack 256 (fun j : Fin 14 => C018_digit j 0)=C018_columnCode 0 := by decide +kernel

private theorem C018_column_01 : reversePack 256 (fun j : Fin 14 => C018_digit j 1)=C018_columnCode 1 := by decide +kernel

private theorem C018_column_02 : reversePack 256 (fun j : Fin 14 => C018_digit j 2)=C018_columnCode 2 := by decide +kernel

private theorem C018_column_03 : reversePack 256 (fun j : Fin 14 => C018_digit j 3)=C018_columnCode 3 := by decide +kernel

private theorem C018_column_04 : reversePack 256 (fun j : Fin 14 => C018_digit j 4)=C018_columnCode 4 := by decide +kernel

private theorem C018_column_05 : reversePack 256 (fun j : Fin 14 => C018_digit j 5)=C018_columnCode 5 := by decide +kernel

private theorem C018_column_06 : reversePack 256 (fun j : Fin 14 => C018_digit j 6)=C018_columnCode 6 := by decide +kernel

private theorem C018_column_07 : reversePack 256 (fun j : Fin 14 => C018_digit j 7)=C018_columnCode 7 := by decide +kernel

private theorem C018_column_08 : reversePack 256 (fun j : Fin 14 => C018_digit j 8)=C018_columnCode 8 := by decide +kernel

private theorem C018_column_09 : reversePack 256 (fun j : Fin 14 => C018_digit j 9)=C018_columnCode 9 := by decide +kernel

private theorem C018_column_10 : reversePack 256 (fun j : Fin 14 => C018_digit j 10)=C018_columnCode 10 := by decide +kernel

private theorem C018_column_11 : reversePack 256 (fun j : Fin 14 => C018_digit j 11)=C018_columnCode 11 := by decide +kernel

private theorem C018_column_12 : reversePack 256 (fun j : Fin 14 => C018_digit j 12)=C018_columnCode 12 := by decide +kernel

private theorem C018_column_13 : reversePack 256 (fun j : Fin 14 => C018_digit j 13)=C018_columnCode 13 := by decide +kernel

theorem C018_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C018_digit j i)=C018_columnCode i := by
  intro i
  fin_cases i
  · exact C018_column_00
  · exact C018_column_01
  · exact C018_column_02
  · exact C018_column_03
  · exact C018_column_04
  · exact C018_column_05
  · exact C018_column_06
  · exact C018_column_07
  · exact C018_column_08
  · exact C018_column_09
  · exact C018_column_10
  · exact C018_column_11
  · exact C018_column_12
  · exact C018_column_13

def C018_data : PackedData 14 5 256 where
  raw := C018_digit
  digit_lt := C018_bound
  rowCode := C018_rowCode
  columnCode := C018_columnCode
  row_binding := C018_row_binding
  column_binding := C018_column_binding

def C019_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 1204251935900
  | 1 => 2512833098899
  | 2 => 2355258982467
  | 3 => 19797672137
  | 4 => 1135081526435
  | 5 => 2502390989412
  | 6 => 708188087396
  | 7 => 1941332076756
  | 8 => 1856703701212
  | 9 => 1926855271524
  | 10 => 2199080280785
  | 11 => 638104704129
  | 12 => 1258567078690
  | 13 => 855106397960
  | _ => 0

def C019_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 158767037927711903345413391108
  | 1 => 20599324690505318412782711865859
  | 2 => 81447173666238763750644170949122
  | 3 => 60927077161859759674375419200002
  | 4 => 40644359282160836896242201002756
  | 5 => 238308312229039408290115617796
  | 6 => 81446552278348963591422459511040
  | 7 => 40802507340531722116950822945792
  | 8 => 622601593255839813477597187
  | 9 => 60927075962396832105427336692228
  | 10 => 81447170044146562292741912462337
  | 11 => 61006304106003327318620069037060
  | 12 => 81288404243590126677468679111681
  | 13 => 20441180263615955042213554291714
  | _ => 0

def C019_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 81367944308984009539054586822914
  | 1 => 61006306538095781474831016657924
  | 2 => 60847538295964833461352605549060
  | 3 => 20362566221213989660419720085504
  | 4 => 61164762853661057538181791219714
  | 5 => 81446861777488846221030874874884
  | 6 => 81446862976988596069351087538689
  | 7 => 81289028039831277534124972311555
  | 8 => 81368251366697603086875350795011
  | 9 => 81446862977043792747135053595651
  | 10 => 20441795602154075596321319813124
  | 11 => 20283030996282212316567761453313
  | 12 => 40882971011103498983068970123778
  | 13 => 80469738776030320834314961921
  | _ => 0

def C019_digit (i j : Fin 14) : ℕ := packedDigit 3 (C019_lowColumnCode j) i.val

private theorem C019_bound_00 : ∀ j : Fin 14, C019_digit 0 j < 5 := by decide +kernel

private theorem C019_bound_01 : ∀ j : Fin 14, C019_digit 1 j < 5 := by decide +kernel

private theorem C019_bound_02 : ∀ j : Fin 14, C019_digit 2 j < 5 := by decide +kernel

private theorem C019_bound_03 : ∀ j : Fin 14, C019_digit 3 j < 5 := by decide +kernel

private theorem C019_bound_04 : ∀ j : Fin 14, C019_digit 4 j < 5 := by decide +kernel

private theorem C019_bound_05 : ∀ j : Fin 14, C019_digit 5 j < 5 := by decide +kernel

private theorem C019_bound_06 : ∀ j : Fin 14, C019_digit 6 j < 5 := by decide +kernel

private theorem C019_bound_07 : ∀ j : Fin 14, C019_digit 7 j < 5 := by decide +kernel

private theorem C019_bound_08 : ∀ j : Fin 14, C019_digit 8 j < 5 := by decide +kernel

private theorem C019_bound_09 : ∀ j : Fin 14, C019_digit 9 j < 5 := by decide +kernel

private theorem C019_bound_10 : ∀ j : Fin 14, C019_digit 10 j < 5 := by decide +kernel

private theorem C019_bound_11 : ∀ j : Fin 14, C019_digit 11 j < 5 := by decide +kernel

private theorem C019_bound_12 : ∀ j : Fin 14, C019_digit 12 j < 5 := by decide +kernel

private theorem C019_bound_13 : ∀ j : Fin 14, C019_digit 13 j < 5 := by decide +kernel

theorem C019_bound : ∀ i j : Fin 14, C019_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C019_bound_00 j
  · exact C019_bound_01 j
  · exact C019_bound_02 j
  · exact C019_bound_03 j
  · exact C019_bound_04 j
  · exact C019_bound_05 j
  · exact C019_bound_06 j
  · exact C019_bound_07 j
  · exact C019_bound_08 j
  · exact C019_bound_09 j
  · exact C019_bound_10 j
  · exact C019_bound_11 j
  · exact C019_bound_12 j
  · exact C019_bound_13 j

private theorem C019_row_00 : pack 256 (C019_digit 0)=C019_rowCode 0 := by decide +kernel

private theorem C019_row_01 : pack 256 (C019_digit 1)=C019_rowCode 1 := by decide +kernel

private theorem C019_row_02 : pack 256 (C019_digit 2)=C019_rowCode 2 := by decide +kernel

private theorem C019_row_03 : pack 256 (C019_digit 3)=C019_rowCode 3 := by decide +kernel

private theorem C019_row_04 : pack 256 (C019_digit 4)=C019_rowCode 4 := by decide +kernel

private theorem C019_row_05 : pack 256 (C019_digit 5)=C019_rowCode 5 := by decide +kernel

private theorem C019_row_06 : pack 256 (C019_digit 6)=C019_rowCode 6 := by decide +kernel

private theorem C019_row_07 : pack 256 (C019_digit 7)=C019_rowCode 7 := by decide +kernel

private theorem C019_row_08 : pack 256 (C019_digit 8)=C019_rowCode 8 := by decide +kernel

private theorem C019_row_09 : pack 256 (C019_digit 9)=C019_rowCode 9 := by decide +kernel

private theorem C019_row_10 : pack 256 (C019_digit 10)=C019_rowCode 10 := by decide +kernel

private theorem C019_row_11 : pack 256 (C019_digit 11)=C019_rowCode 11 := by decide +kernel

private theorem C019_row_12 : pack 256 (C019_digit 12)=C019_rowCode 12 := by decide +kernel

private theorem C019_row_13 : pack 256 (C019_digit 13)=C019_rowCode 13 := by decide +kernel

theorem C019_row_binding : ∀ i : Fin 14, pack 256 (C019_digit i)=C019_rowCode i := by
  intro i
  fin_cases i
  · exact C019_row_00
  · exact C019_row_01
  · exact C019_row_02
  · exact C019_row_03
  · exact C019_row_04
  · exact C019_row_05
  · exact C019_row_06
  · exact C019_row_07
  · exact C019_row_08
  · exact C019_row_09
  · exact C019_row_10
  · exact C019_row_11
  · exact C019_row_12
  · exact C019_row_13

private theorem C019_column_00 : reversePack 256 (fun j : Fin 14 => C019_digit j 0)=C019_columnCode 0 := by decide +kernel

private theorem C019_column_01 : reversePack 256 (fun j : Fin 14 => C019_digit j 1)=C019_columnCode 1 := by decide +kernel

private theorem C019_column_02 : reversePack 256 (fun j : Fin 14 => C019_digit j 2)=C019_columnCode 2 := by decide +kernel

private theorem C019_column_03 : reversePack 256 (fun j : Fin 14 => C019_digit j 3)=C019_columnCode 3 := by decide +kernel

private theorem C019_column_04 : reversePack 256 (fun j : Fin 14 => C019_digit j 4)=C019_columnCode 4 := by decide +kernel

private theorem C019_column_05 : reversePack 256 (fun j : Fin 14 => C019_digit j 5)=C019_columnCode 5 := by decide +kernel

private theorem C019_column_06 : reversePack 256 (fun j : Fin 14 => C019_digit j 6)=C019_columnCode 6 := by decide +kernel

private theorem C019_column_07 : reversePack 256 (fun j : Fin 14 => C019_digit j 7)=C019_columnCode 7 := by decide +kernel

private theorem C019_column_08 : reversePack 256 (fun j : Fin 14 => C019_digit j 8)=C019_columnCode 8 := by decide +kernel

private theorem C019_column_09 : reversePack 256 (fun j : Fin 14 => C019_digit j 9)=C019_columnCode 9 := by decide +kernel

private theorem C019_column_10 : reversePack 256 (fun j : Fin 14 => C019_digit j 10)=C019_columnCode 10 := by decide +kernel

private theorem C019_column_11 : reversePack 256 (fun j : Fin 14 => C019_digit j 11)=C019_columnCode 11 := by decide +kernel

private theorem C019_column_12 : reversePack 256 (fun j : Fin 14 => C019_digit j 12)=C019_columnCode 12 := by decide +kernel

private theorem C019_column_13 : reversePack 256 (fun j : Fin 14 => C019_digit j 13)=C019_columnCode 13 := by decide +kernel

theorem C019_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C019_digit j i)=C019_columnCode i := by
  intro i
  fin_cases i
  · exact C019_column_00
  · exact C019_column_01
  · exact C019_column_02
  · exact C019_column_03
  · exact C019_column_04
  · exact C019_column_05
  · exact C019_column_06
  · exact C019_column_07
  · exact C019_column_08
  · exact C019_column_09
  · exact C019_column_10
  · exact C019_column_11
  · exact C019_column_12
  · exact C019_column_13

def C019_data : PackedData 14 5 256 where
  raw := C019_digit
  digit_lt := C019_bound
  rowCode := C019_rowCode
  columnCode := C019_columnCode
  row_binding := C019_row_binding
  column_binding := C019_column_binding

def C020_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 825918259994
  | 1 => 1937504837777
  | 2 => 759311778914
  | 3 => 77750374993
  | 4 => 560533120067
  | 5 => 284550050460
  | 6 => 2227348440096
  | 7 => 78574340371
  | 8 => 2483900950681
  | 9 => 2209784046113
  | 10 => 2353810653699
  | 11 => 826972881940
  | 12 => 1258567078690
  | 13 => 855106397960
  | _ => 0

def C020_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 159697896586302303485928014082
  | 1 => 20599941242673321872545137558019
  | 2 => 81446551064700920766890086826500
  | 3 => 60927077157211180167800629100545
  | 4 => 40645290155042083711849647571456
  | 5 => 237993977293571702184122516225
  | 6 => 81447483151229995079767922049540
  | 7 => 40803432164042914084633276842500
  | 8 => 930877677472896419744580612
  | 9 => 60926767667441882959299634856705
  | 10 => 81447170044146634067765723595777
  | 11 => 61005687558576065306353337368832
  | 12 => 81289335097599994018796281201668
  | 13 => 20441180268356552936397383729921
  | _ => 0

def C020_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 40803742843829974960331334616065
  | 1 => 20441484908200059669781235696643
  | 2 => 40882043779185112808472447025921
  | 3 => 20441176627356797966125530939648
  | 4 => 60847540723279652402605815037953
  | 5 => 81367943095298931075992539694080
  | 6 => 316915067908985372971548999684
  | 7 => 61006927930652536110768254419200
  | 8 => 20520717906380708414789760648196
  | 9 => 20599323472097800001882115080196
  | 10 => 60847230038770512992934941557252
  | 11 => 81288097176394979296296640185345
  | 12 => 40882971011103498983068970123778
  | 13 => 80469738776030320834314961921
  | _ => 0

def C020_digit (i j : Fin 14) : ℕ := packedDigit 3 (C020_lowColumnCode j) i.val

private theorem C020_bound_00 : ∀ j : Fin 14, C020_digit 0 j < 5 := by decide +kernel

private theorem C020_bound_01 : ∀ j : Fin 14, C020_digit 1 j < 5 := by decide +kernel

private theorem C020_bound_02 : ∀ j : Fin 14, C020_digit 2 j < 5 := by decide +kernel

private theorem C020_bound_03 : ∀ j : Fin 14, C020_digit 3 j < 5 := by decide +kernel

private theorem C020_bound_04 : ∀ j : Fin 14, C020_digit 4 j < 5 := by decide +kernel

private theorem C020_bound_05 : ∀ j : Fin 14, C020_digit 5 j < 5 := by decide +kernel

private theorem C020_bound_06 : ∀ j : Fin 14, C020_digit 6 j < 5 := by decide +kernel

private theorem C020_bound_07 : ∀ j : Fin 14, C020_digit 7 j < 5 := by decide +kernel

private theorem C020_bound_08 : ∀ j : Fin 14, C020_digit 8 j < 5 := by decide +kernel

private theorem C020_bound_09 : ∀ j : Fin 14, C020_digit 9 j < 5 := by decide +kernel

private theorem C020_bound_10 : ∀ j : Fin 14, C020_digit 10 j < 5 := by decide +kernel

private theorem C020_bound_11 : ∀ j : Fin 14, C020_digit 11 j < 5 := by decide +kernel

private theorem C020_bound_12 : ∀ j : Fin 14, C020_digit 12 j < 5 := by decide +kernel

private theorem C020_bound_13 : ∀ j : Fin 14, C020_digit 13 j < 5 := by decide +kernel

theorem C020_bound : ∀ i j : Fin 14, C020_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C020_bound_00 j
  · exact C020_bound_01 j
  · exact C020_bound_02 j
  · exact C020_bound_03 j
  · exact C020_bound_04 j
  · exact C020_bound_05 j
  · exact C020_bound_06 j
  · exact C020_bound_07 j
  · exact C020_bound_08 j
  · exact C020_bound_09 j
  · exact C020_bound_10 j
  · exact C020_bound_11 j
  · exact C020_bound_12 j
  · exact C020_bound_13 j

private theorem C020_row_00 : pack 256 (C020_digit 0)=C020_rowCode 0 := by decide +kernel

private theorem C020_row_01 : pack 256 (C020_digit 1)=C020_rowCode 1 := by decide +kernel

private theorem C020_row_02 : pack 256 (C020_digit 2)=C020_rowCode 2 := by decide +kernel

private theorem C020_row_03 : pack 256 (C020_digit 3)=C020_rowCode 3 := by decide +kernel

private theorem C020_row_04 : pack 256 (C020_digit 4)=C020_rowCode 4 := by decide +kernel

private theorem C020_row_05 : pack 256 (C020_digit 5)=C020_rowCode 5 := by decide +kernel

private theorem C020_row_06 : pack 256 (C020_digit 6)=C020_rowCode 6 := by decide +kernel

private theorem C020_row_07 : pack 256 (C020_digit 7)=C020_rowCode 7 := by decide +kernel

private theorem C020_row_08 : pack 256 (C020_digit 8)=C020_rowCode 8 := by decide +kernel

private theorem C020_row_09 : pack 256 (C020_digit 9)=C020_rowCode 9 := by decide +kernel

private theorem C020_row_10 : pack 256 (C020_digit 10)=C020_rowCode 10 := by decide +kernel

private theorem C020_row_11 : pack 256 (C020_digit 11)=C020_rowCode 11 := by decide +kernel

private theorem C020_row_12 : pack 256 (C020_digit 12)=C020_rowCode 12 := by decide +kernel

private theorem C020_row_13 : pack 256 (C020_digit 13)=C020_rowCode 13 := by decide +kernel

theorem C020_row_binding : ∀ i : Fin 14, pack 256 (C020_digit i)=C020_rowCode i := by
  intro i
  fin_cases i
  · exact C020_row_00
  · exact C020_row_01
  · exact C020_row_02
  · exact C020_row_03
  · exact C020_row_04
  · exact C020_row_05
  · exact C020_row_06
  · exact C020_row_07
  · exact C020_row_08
  · exact C020_row_09
  · exact C020_row_10
  · exact C020_row_11
  · exact C020_row_12
  · exact C020_row_13

private theorem C020_column_00 : reversePack 256 (fun j : Fin 14 => C020_digit j 0)=C020_columnCode 0 := by decide +kernel

private theorem C020_column_01 : reversePack 256 (fun j : Fin 14 => C020_digit j 1)=C020_columnCode 1 := by decide +kernel

private theorem C020_column_02 : reversePack 256 (fun j : Fin 14 => C020_digit j 2)=C020_columnCode 2 := by decide +kernel

private theorem C020_column_03 : reversePack 256 (fun j : Fin 14 => C020_digit j 3)=C020_columnCode 3 := by decide +kernel

private theorem C020_column_04 : reversePack 256 (fun j : Fin 14 => C020_digit j 4)=C020_columnCode 4 := by decide +kernel

private theorem C020_column_05 : reversePack 256 (fun j : Fin 14 => C020_digit j 5)=C020_columnCode 5 := by decide +kernel

private theorem C020_column_06 : reversePack 256 (fun j : Fin 14 => C020_digit j 6)=C020_columnCode 6 := by decide +kernel

private theorem C020_column_07 : reversePack 256 (fun j : Fin 14 => C020_digit j 7)=C020_columnCode 7 := by decide +kernel

private theorem C020_column_08 : reversePack 256 (fun j : Fin 14 => C020_digit j 8)=C020_columnCode 8 := by decide +kernel

private theorem C020_column_09 : reversePack 256 (fun j : Fin 14 => C020_digit j 9)=C020_columnCode 9 := by decide +kernel

private theorem C020_column_10 : reversePack 256 (fun j : Fin 14 => C020_digit j 10)=C020_columnCode 10 := by decide +kernel

private theorem C020_column_11 : reversePack 256 (fun j : Fin 14 => C020_digit j 11)=C020_columnCode 11 := by decide +kernel

private theorem C020_column_12 : reversePack 256 (fun j : Fin 14 => C020_digit j 12)=C020_columnCode 12 := by decide +kernel

private theorem C020_column_13 : reversePack 256 (fun j : Fin 14 => C020_digit j 13)=C020_columnCode 13 := by decide +kernel

theorem C020_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C020_digit j i)=C020_columnCode i := by
  intro i
  fin_cases i
  · exact C020_column_00
  · exact C020_column_01
  · exact C020_column_02
  · exact C020_column_03
  · exact C020_column_04
  · exact C020_column_05
  · exact C020_column_06
  · exact C020_column_07
  · exact C020_column_08
  · exact C020_column_09
  · exact C020_column_10
  · exact C020_column_11
  · exact C020_column_12
  · exact C020_column_13

def C020_data : PackedData 14 5 256 where
  raw := C020_digit
  digit_lt := C020_bound
  rowCode := C020_rowCode
  columnCode := C020_columnCode
  row_binding := C020_row_binding
  column_binding := C020_column_binding

end SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedCaches02
