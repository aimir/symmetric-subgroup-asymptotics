import SymmetricSubgroupAsymptotics.MatrixKroneckerProductReflection
import Mathlib.Tactic.FinCases

/-! Literal14/F5 selected caches; digit bounds and both pack bindings are independently kernel checked. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryCaches05
open MatrixKroneckerProductReflection MatrixKroneckerDotReflection
open MatrixNaturalRowDotReflection SmallNaturalMatrixProductReflection

def C024_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 1806036470040
  | 1 => 241802231940
  | 2 => 2441188214787
  | 3 => 17520207002
  | 4 => 550181602516
  | 5 => 98019315722
  | 6 => 287093821457
  | 7 => 2305514943187
  | 8 => 764546778896
  | 9 => 70079623392
  | 10 => 1272820410450
  | 11 => 2509754385995
  | 12 => 577021200611
  | 13 => 2199074472483
  | _ => 0

def C024_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 61085844171379124005560236835840
  | 1 => 81446862986451703719362436268035
  | 2 => 237995195719536570177337426436
  | 3 => 20600255544496882557868090589188
  | 4 => 318153022115297863872995656704
  | 5 => 60926771313145916551178915676675
  | 6 => 60926766477405528433923117416962
  | 7 => 79228162588267771456926057473
  | 8 => 60926768881090212329764935566336
  | 9 => 238616578794521761844530774272
  | 10 => 79538861172488800666667516162
  | 11 => 238927263304092110795636474882
  | 12 => 1240362668704509217479000834
  | 13 => 81210106935030605617369954123779
  | _ => 0

def C024_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 238927263340841480456444707331
  | 1 => 81130257403552829051042795881216
  | 2 => 60847233646658434129237725414148
  | 3 => 40803125092199186916502308782080
  | 4 => 81289025612553207969125362565121
  | 5 => 40644047374540116630178361442560
  | 6 => 20440865933402565863491896411136
  | 7 => 61006614814179782927089813160196
  | 8 => 159697891919205118931355370241
  | 9 => 317841119327696041968394043648
  | 10 => 40723589862563489270913067909634
  | 11 => 60926770104164540532650288612356
  | 12 => 61165074770652796131672521375745
  | 13 => 61164142669993444645146881687556
  | _ => 0

def C024_digit (i j : Fin 14) : ℕ := packedDigit 3 (C024_lowColumnCode j) i.val

private theorem C024_bound_00 : ∀ j : Fin 14, C024_digit 0 j < 5 := by decide +kernel

private theorem C024_bound_01 : ∀ j : Fin 14, C024_digit 1 j < 5 := by decide +kernel

private theorem C024_bound_02 : ∀ j : Fin 14, C024_digit 2 j < 5 := by decide +kernel

private theorem C024_bound_03 : ∀ j : Fin 14, C024_digit 3 j < 5 := by decide +kernel

private theorem C024_bound_04 : ∀ j : Fin 14, C024_digit 4 j < 5 := by decide +kernel

private theorem C024_bound_05 : ∀ j : Fin 14, C024_digit 5 j < 5 := by decide +kernel

private theorem C024_bound_06 : ∀ j : Fin 14, C024_digit 6 j < 5 := by decide +kernel

private theorem C024_bound_07 : ∀ j : Fin 14, C024_digit 7 j < 5 := by decide +kernel

private theorem C024_bound_08 : ∀ j : Fin 14, C024_digit 8 j < 5 := by decide +kernel

private theorem C024_bound_09 : ∀ j : Fin 14, C024_digit 9 j < 5 := by decide +kernel

private theorem C024_bound_10 : ∀ j : Fin 14, C024_digit 10 j < 5 := by decide +kernel

private theorem C024_bound_11 : ∀ j : Fin 14, C024_digit 11 j < 5 := by decide +kernel

private theorem C024_bound_12 : ∀ j : Fin 14, C024_digit 12 j < 5 := by decide +kernel

private theorem C024_bound_13 : ∀ j : Fin 14, C024_digit 13 j < 5 := by decide +kernel

theorem C024_bound : ∀ i j : Fin 14, C024_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C024_bound_00 j
  · exact C024_bound_01 j
  · exact C024_bound_02 j
  · exact C024_bound_03 j
  · exact C024_bound_04 j
  · exact C024_bound_05 j
  · exact C024_bound_06 j
  · exact C024_bound_07 j
  · exact C024_bound_08 j
  · exact C024_bound_09 j
  · exact C024_bound_10 j
  · exact C024_bound_11 j
  · exact C024_bound_12 j
  · exact C024_bound_13 j

private theorem C024_row_00 : pack 256 (C024_digit 0)=C024_rowCode 0 := by decide +kernel

private theorem C024_row_01 : pack 256 (C024_digit 1)=C024_rowCode 1 := by decide +kernel

private theorem C024_row_02 : pack 256 (C024_digit 2)=C024_rowCode 2 := by decide +kernel

private theorem C024_row_03 : pack 256 (C024_digit 3)=C024_rowCode 3 := by decide +kernel

private theorem C024_row_04 : pack 256 (C024_digit 4)=C024_rowCode 4 := by decide +kernel

private theorem C024_row_05 : pack 256 (C024_digit 5)=C024_rowCode 5 := by decide +kernel

private theorem C024_row_06 : pack 256 (C024_digit 6)=C024_rowCode 6 := by decide +kernel

private theorem C024_row_07 : pack 256 (C024_digit 7)=C024_rowCode 7 := by decide +kernel

private theorem C024_row_08 : pack 256 (C024_digit 8)=C024_rowCode 8 := by decide +kernel

private theorem C024_row_09 : pack 256 (C024_digit 9)=C024_rowCode 9 := by decide +kernel

private theorem C024_row_10 : pack 256 (C024_digit 10)=C024_rowCode 10 := by decide +kernel

private theorem C024_row_11 : pack 256 (C024_digit 11)=C024_rowCode 11 := by decide +kernel

private theorem C024_row_12 : pack 256 (C024_digit 12)=C024_rowCode 12 := by decide +kernel

private theorem C024_row_13 : pack 256 (C024_digit 13)=C024_rowCode 13 := by decide +kernel

theorem C024_row_binding : ∀ i : Fin 14, pack 256 (C024_digit i)=C024_rowCode i := by
  intro i
  fin_cases i
  · exact C024_row_00
  · exact C024_row_01
  · exact C024_row_02
  · exact C024_row_03
  · exact C024_row_04
  · exact C024_row_05
  · exact C024_row_06
  · exact C024_row_07
  · exact C024_row_08
  · exact C024_row_09
  · exact C024_row_10
  · exact C024_row_11
  · exact C024_row_12
  · exact C024_row_13

private theorem C024_column_00 : reversePack 256 (fun j : Fin 14 => C024_digit j 0)=C024_columnCode 0 := by decide +kernel

private theorem C024_column_01 : reversePack 256 (fun j : Fin 14 => C024_digit j 1)=C024_columnCode 1 := by decide +kernel

private theorem C024_column_02 : reversePack 256 (fun j : Fin 14 => C024_digit j 2)=C024_columnCode 2 := by decide +kernel

private theorem C024_column_03 : reversePack 256 (fun j : Fin 14 => C024_digit j 3)=C024_columnCode 3 := by decide +kernel

private theorem C024_column_04 : reversePack 256 (fun j : Fin 14 => C024_digit j 4)=C024_columnCode 4 := by decide +kernel

private theorem C024_column_05 : reversePack 256 (fun j : Fin 14 => C024_digit j 5)=C024_columnCode 5 := by decide +kernel

private theorem C024_column_06 : reversePack 256 (fun j : Fin 14 => C024_digit j 6)=C024_columnCode 6 := by decide +kernel

private theorem C024_column_07 : reversePack 256 (fun j : Fin 14 => C024_digit j 7)=C024_columnCode 7 := by decide +kernel

private theorem C024_column_08 : reversePack 256 (fun j : Fin 14 => C024_digit j 8)=C024_columnCode 8 := by decide +kernel

private theorem C024_column_09 : reversePack 256 (fun j : Fin 14 => C024_digit j 9)=C024_columnCode 9 := by decide +kernel

private theorem C024_column_10 : reversePack 256 (fun j : Fin 14 => C024_digit j 10)=C024_columnCode 10 := by decide +kernel

private theorem C024_column_11 : reversePack 256 (fun j : Fin 14 => C024_digit j 11)=C024_columnCode 11 := by decide +kernel

private theorem C024_column_12 : reversePack 256 (fun j : Fin 14 => C024_digit j 12)=C024_columnCode 12 := by decide +kernel

private theorem C024_column_13 : reversePack 256 (fun j : Fin 14 => C024_digit j 13)=C024_columnCode 13 := by decide +kernel

theorem C024_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C024_digit j i)=C024_columnCode i := by
  intro i
  fin_cases i
  · exact C024_column_00
  · exact C024_column_01
  · exact C024_column_02
  · exact C024_column_03
  · exact C024_column_04
  · exact C024_column_05
  · exact C024_column_06
  · exact C024_column_07
  · exact C024_column_08
  · exact C024_column_09
  · exact C024_column_10
  · exact C024_column_11
  · exact C024_column_12
  · exact C024_column_13

def C024_data : PackedData 14 5 256 where
  raw := C024_digit
  digit_lt := C024_bound
  rowCode := C024_rowCode
  columnCode := C024_columnCode
  row_binding := C024_row_binding
  column_binding := C024_column_binding

def C025_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 2363507218184
  | 1 => 1383187915788
  | 2 => 1334194348244
  | 3 => 140719687752
  | 4 => 310639147139
  | 5 => 164438583059
  | 6 => 2303180802113
  | 7 => 2440136073248
  | 8 => 2370875196504
  | 9 => 829349013650
  | 10 => 89464902875
  | 11 => 1401672221712
  | 12 => 567137896066
  | 13 => 2199074472483
  | _ => 0

def C025_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 61005688772205732041442053063680
  | 1 => 81130261020904144660349589782785
  | 2 => 158459961269167514769242128388
  | 3 => 20520715497992105904965370774019
  | 4 => 1239158409982078043348402689
  | 5 => 61085227633396667582879600214276
  | 6 => 61085842976675816130446102823680
  | 7 => 314320731763285607470662400
  | 8 => 61164765271512912659855412823044
  | 9 => 80159049562755282151256883457
  | 10 => 313130676746403013663522817
  | 11 => 159387197983708275538223366403
  | 12 => 1239167891680871003401159682
  | 13 => 81209485551937031538960540762628
  | _ => 0

def C025_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 80469734127162025322809065988
  | 1 => 81208869004435981994063283946498
  | 2 => 81289023204183410806888746648322
  | 3 => 79542483227581443159573398016
  | 4 => 60847852630882070601647381545984
  | 5 => 61006926712300574105987574858240
  | 6 => 20282723924438629824371521487108
  | 7 => 316912659557419626451391742724
  | 8 => 237996390422916788737041236484
  | 9 => 40723899347555080043590735365121
  | 10 => 61085844176175134196152024563968
  | 11 => 158458761788297036466743346178
  | 12 => 40565441804155998791325060300801
  | 13 => 61164142669993444645146881687556
  | _ => 0

def C025_digit (i j : Fin 14) : ℕ := packedDigit 3 (C025_lowColumnCode j) i.val

private theorem C025_bound_00 : ∀ j : Fin 14, C025_digit 0 j < 5 := by decide +kernel

private theorem C025_bound_01 : ∀ j : Fin 14, C025_digit 1 j < 5 := by decide +kernel

private theorem C025_bound_02 : ∀ j : Fin 14, C025_digit 2 j < 5 := by decide +kernel

private theorem C025_bound_03 : ∀ j : Fin 14, C025_digit 3 j < 5 := by decide +kernel

private theorem C025_bound_04 : ∀ j : Fin 14, C025_digit 4 j < 5 := by decide +kernel

private theorem C025_bound_05 : ∀ j : Fin 14, C025_digit 5 j < 5 := by decide +kernel

private theorem C025_bound_06 : ∀ j : Fin 14, C025_digit 6 j < 5 := by decide +kernel

private theorem C025_bound_07 : ∀ j : Fin 14, C025_digit 7 j < 5 := by decide +kernel

private theorem C025_bound_08 : ∀ j : Fin 14, C025_digit 8 j < 5 := by decide +kernel

private theorem C025_bound_09 : ∀ j : Fin 14, C025_digit 9 j < 5 := by decide +kernel

private theorem C025_bound_10 : ∀ j : Fin 14, C025_digit 10 j < 5 := by decide +kernel

private theorem C025_bound_11 : ∀ j : Fin 14, C025_digit 11 j < 5 := by decide +kernel

private theorem C025_bound_12 : ∀ j : Fin 14, C025_digit 12 j < 5 := by decide +kernel

private theorem C025_bound_13 : ∀ j : Fin 14, C025_digit 13 j < 5 := by decide +kernel

theorem C025_bound : ∀ i j : Fin 14, C025_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C025_bound_00 j
  · exact C025_bound_01 j
  · exact C025_bound_02 j
  · exact C025_bound_03 j
  · exact C025_bound_04 j
  · exact C025_bound_05 j
  · exact C025_bound_06 j
  · exact C025_bound_07 j
  · exact C025_bound_08 j
  · exact C025_bound_09 j
  · exact C025_bound_10 j
  · exact C025_bound_11 j
  · exact C025_bound_12 j
  · exact C025_bound_13 j

private theorem C025_row_00 : pack 256 (C025_digit 0)=C025_rowCode 0 := by decide +kernel

private theorem C025_row_01 : pack 256 (C025_digit 1)=C025_rowCode 1 := by decide +kernel

private theorem C025_row_02 : pack 256 (C025_digit 2)=C025_rowCode 2 := by decide +kernel

private theorem C025_row_03 : pack 256 (C025_digit 3)=C025_rowCode 3 := by decide +kernel

private theorem C025_row_04 : pack 256 (C025_digit 4)=C025_rowCode 4 := by decide +kernel

private theorem C025_row_05 : pack 256 (C025_digit 5)=C025_rowCode 5 := by decide +kernel

private theorem C025_row_06 : pack 256 (C025_digit 6)=C025_rowCode 6 := by decide +kernel

private theorem C025_row_07 : pack 256 (C025_digit 7)=C025_rowCode 7 := by decide +kernel

private theorem C025_row_08 : pack 256 (C025_digit 8)=C025_rowCode 8 := by decide +kernel

private theorem C025_row_09 : pack 256 (C025_digit 9)=C025_rowCode 9 := by decide +kernel

private theorem C025_row_10 : pack 256 (C025_digit 10)=C025_rowCode 10 := by decide +kernel

private theorem C025_row_11 : pack 256 (C025_digit 11)=C025_rowCode 11 := by decide +kernel

private theorem C025_row_12 : pack 256 (C025_digit 12)=C025_rowCode 12 := by decide +kernel

private theorem C025_row_13 : pack 256 (C025_digit 13)=C025_rowCode 13 := by decide +kernel

theorem C025_row_binding : ∀ i : Fin 14, pack 256 (C025_digit i)=C025_rowCode i := by
  intro i
  fin_cases i
  · exact C025_row_00
  · exact C025_row_01
  · exact C025_row_02
  · exact C025_row_03
  · exact C025_row_04
  · exact C025_row_05
  · exact C025_row_06
  · exact C025_row_07
  · exact C025_row_08
  · exact C025_row_09
  · exact C025_row_10
  · exact C025_row_11
  · exact C025_row_12
  · exact C025_row_13

private theorem C025_column_00 : reversePack 256 (fun j : Fin 14 => C025_digit j 0)=C025_columnCode 0 := by decide +kernel

private theorem C025_column_01 : reversePack 256 (fun j : Fin 14 => C025_digit j 1)=C025_columnCode 1 := by decide +kernel

private theorem C025_column_02 : reversePack 256 (fun j : Fin 14 => C025_digit j 2)=C025_columnCode 2 := by decide +kernel

private theorem C025_column_03 : reversePack 256 (fun j : Fin 14 => C025_digit j 3)=C025_columnCode 3 := by decide +kernel

private theorem C025_column_04 : reversePack 256 (fun j : Fin 14 => C025_digit j 4)=C025_columnCode 4 := by decide +kernel

private theorem C025_column_05 : reversePack 256 (fun j : Fin 14 => C025_digit j 5)=C025_columnCode 5 := by decide +kernel

private theorem C025_column_06 : reversePack 256 (fun j : Fin 14 => C025_digit j 6)=C025_columnCode 6 := by decide +kernel

private theorem C025_column_07 : reversePack 256 (fun j : Fin 14 => C025_digit j 7)=C025_columnCode 7 := by decide +kernel

private theorem C025_column_08 : reversePack 256 (fun j : Fin 14 => C025_digit j 8)=C025_columnCode 8 := by decide +kernel

private theorem C025_column_09 : reversePack 256 (fun j : Fin 14 => C025_digit j 9)=C025_columnCode 9 := by decide +kernel

private theorem C025_column_10 : reversePack 256 (fun j : Fin 14 => C025_digit j 10)=C025_columnCode 10 := by decide +kernel

private theorem C025_column_11 : reversePack 256 (fun j : Fin 14 => C025_digit j 11)=C025_columnCode 11 := by decide +kernel

private theorem C025_column_12 : reversePack 256 (fun j : Fin 14 => C025_digit j 12)=C025_columnCode 12 := by decide +kernel

private theorem C025_column_13 : reversePack 256 (fun j : Fin 14 => C025_digit j 13)=C025_columnCode 13 := by decide +kernel

theorem C025_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C025_digit j i)=C025_columnCode i := by
  intro i
  fin_cases i
  · exact C025_column_00
  · exact C025_column_01
  · exact C025_column_02
  · exact C025_column_03
  · exact C025_column_04
  · exact C025_column_05
  · exact C025_column_06
  · exact C025_column_07
  · exact C025_column_08
  · exact C025_column_09
  · exact C025_column_10
  · exact C025_column_11
  · exact C025_column_12
  · exact C025_column_13

def C025_data : PackedData 14 5 256 where
  raw := C025_digit
  digit_lt := C025_bound
  rowCode := C025_rowCode
  columnCode := C025_columnCode
  row_binding := C025_row_binding
  column_binding := C025_column_binding

def C026_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 1737872983755
  | 1 => 2271291652360
  | 2 => 1744182822993
  | 3 => 1403991934737
  | 4 => 1103962945792
  | 5 => 1943750198050
  | 6 => 639069329673
  | 7 => 657568876834
  | 8 => 764546778896
  | 9 => 70079623392
  | 10 => 1172567004369
  | 11 => 2277729506913
  | 12 => 1413254849036
  | 13 => 2199074472483
  | _ => 0

def C026_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 61164452154947853980775921811459
  | 1 => 81210106953938518578791006208257
  | 2 => 313126028455974551374857219
  | 3 => 20362568639102667615619248292867
  | 4 => 158767033131557599756050236164
  | 5 => 61086152466426234249304864915458
  | 6 => 61084918153127586280169430647299
  | 7 => 317535246928019048594619433986
  | 8 => 61165072338652576817314885862145
  | 9 => 79847141978856449930759963140
  | 10 => 317226975492812713846579921666
  | 11 => 317222135085614235041789050882
  | 12 => 317223348770477368629977481473
  | 13 => 81289335097544654066959224341507
  | _ => 0

def C026_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 60927389074202774645003788615939
  | 1 => 80470952424072869389235388676
  | 2 => 20441180268338177969550837088515
  | 3 => 20442107514405145078065411589122
  | 4 => 1242789965292314051641081858
  | 5 => 40882971025288901342042777584643
  | 6 => 20362880546630866212404825555201
  | 7 => 40882974652011019111487594823937
  | 8 => 159697891919205118931355370241
  | 9 => 317841119327696041968394043648
  | 10 => 20441796806302404667542389915906
  | 11 => 20599635370292161988699254489348
  | 12 => 81208867795547056149056572359682
  | 13 => 61164142669993444645146881687556
  | _ => 0

def C026_digit (i j : Fin 14) : ℕ := packedDigit 3 (C026_lowColumnCode j) i.val

private theorem C026_bound_00 : ∀ j : Fin 14, C026_digit 0 j < 5 := by decide +kernel

private theorem C026_bound_01 : ∀ j : Fin 14, C026_digit 1 j < 5 := by decide +kernel

private theorem C026_bound_02 : ∀ j : Fin 14, C026_digit 2 j < 5 := by decide +kernel

private theorem C026_bound_03 : ∀ j : Fin 14, C026_digit 3 j < 5 := by decide +kernel

private theorem C026_bound_04 : ∀ j : Fin 14, C026_digit 4 j < 5 := by decide +kernel

private theorem C026_bound_05 : ∀ j : Fin 14, C026_digit 5 j < 5 := by decide +kernel

private theorem C026_bound_06 : ∀ j : Fin 14, C026_digit 6 j < 5 := by decide +kernel

private theorem C026_bound_07 : ∀ j : Fin 14, C026_digit 7 j < 5 := by decide +kernel

private theorem C026_bound_08 : ∀ j : Fin 14, C026_digit 8 j < 5 := by decide +kernel

private theorem C026_bound_09 : ∀ j : Fin 14, C026_digit 9 j < 5 := by decide +kernel

private theorem C026_bound_10 : ∀ j : Fin 14, C026_digit 10 j < 5 := by decide +kernel

private theorem C026_bound_11 : ∀ j : Fin 14, C026_digit 11 j < 5 := by decide +kernel

private theorem C026_bound_12 : ∀ j : Fin 14, C026_digit 12 j < 5 := by decide +kernel

private theorem C026_bound_13 : ∀ j : Fin 14, C026_digit 13 j < 5 := by decide +kernel

theorem C026_bound : ∀ i j : Fin 14, C026_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C026_bound_00 j
  · exact C026_bound_01 j
  · exact C026_bound_02 j
  · exact C026_bound_03 j
  · exact C026_bound_04 j
  · exact C026_bound_05 j
  · exact C026_bound_06 j
  · exact C026_bound_07 j
  · exact C026_bound_08 j
  · exact C026_bound_09 j
  · exact C026_bound_10 j
  · exact C026_bound_11 j
  · exact C026_bound_12 j
  · exact C026_bound_13 j

private theorem C026_row_00 : pack 256 (C026_digit 0)=C026_rowCode 0 := by decide +kernel

private theorem C026_row_01 : pack 256 (C026_digit 1)=C026_rowCode 1 := by decide +kernel

private theorem C026_row_02 : pack 256 (C026_digit 2)=C026_rowCode 2 := by decide +kernel

private theorem C026_row_03 : pack 256 (C026_digit 3)=C026_rowCode 3 := by decide +kernel

private theorem C026_row_04 : pack 256 (C026_digit 4)=C026_rowCode 4 := by decide +kernel

private theorem C026_row_05 : pack 256 (C026_digit 5)=C026_rowCode 5 := by decide +kernel

private theorem C026_row_06 : pack 256 (C026_digit 6)=C026_rowCode 6 := by decide +kernel

private theorem C026_row_07 : pack 256 (C026_digit 7)=C026_rowCode 7 := by decide +kernel

private theorem C026_row_08 : pack 256 (C026_digit 8)=C026_rowCode 8 := by decide +kernel

private theorem C026_row_09 : pack 256 (C026_digit 9)=C026_rowCode 9 := by decide +kernel

private theorem C026_row_10 : pack 256 (C026_digit 10)=C026_rowCode 10 := by decide +kernel

private theorem C026_row_11 : pack 256 (C026_digit 11)=C026_rowCode 11 := by decide +kernel

private theorem C026_row_12 : pack 256 (C026_digit 12)=C026_rowCode 12 := by decide +kernel

private theorem C026_row_13 : pack 256 (C026_digit 13)=C026_rowCode 13 := by decide +kernel

theorem C026_row_binding : ∀ i : Fin 14, pack 256 (C026_digit i)=C026_rowCode i := by
  intro i
  fin_cases i
  · exact C026_row_00
  · exact C026_row_01
  · exact C026_row_02
  · exact C026_row_03
  · exact C026_row_04
  · exact C026_row_05
  · exact C026_row_06
  · exact C026_row_07
  · exact C026_row_08
  · exact C026_row_09
  · exact C026_row_10
  · exact C026_row_11
  · exact C026_row_12
  · exact C026_row_13

private theorem C026_column_00 : reversePack 256 (fun j : Fin 14 => C026_digit j 0)=C026_columnCode 0 := by decide +kernel

private theorem C026_column_01 : reversePack 256 (fun j : Fin 14 => C026_digit j 1)=C026_columnCode 1 := by decide +kernel

private theorem C026_column_02 : reversePack 256 (fun j : Fin 14 => C026_digit j 2)=C026_columnCode 2 := by decide +kernel

private theorem C026_column_03 : reversePack 256 (fun j : Fin 14 => C026_digit j 3)=C026_columnCode 3 := by decide +kernel

private theorem C026_column_04 : reversePack 256 (fun j : Fin 14 => C026_digit j 4)=C026_columnCode 4 := by decide +kernel

private theorem C026_column_05 : reversePack 256 (fun j : Fin 14 => C026_digit j 5)=C026_columnCode 5 := by decide +kernel

private theorem C026_column_06 : reversePack 256 (fun j : Fin 14 => C026_digit j 6)=C026_columnCode 6 := by decide +kernel

private theorem C026_column_07 : reversePack 256 (fun j : Fin 14 => C026_digit j 7)=C026_columnCode 7 := by decide +kernel

private theorem C026_column_08 : reversePack 256 (fun j : Fin 14 => C026_digit j 8)=C026_columnCode 8 := by decide +kernel

private theorem C026_column_09 : reversePack 256 (fun j : Fin 14 => C026_digit j 9)=C026_columnCode 9 := by decide +kernel

private theorem C026_column_10 : reversePack 256 (fun j : Fin 14 => C026_digit j 10)=C026_columnCode 10 := by decide +kernel

private theorem C026_column_11 : reversePack 256 (fun j : Fin 14 => C026_digit j 11)=C026_columnCode 11 := by decide +kernel

private theorem C026_column_12 : reversePack 256 (fun j : Fin 14 => C026_digit j 12)=C026_columnCode 12 := by decide +kernel

private theorem C026_column_13 : reversePack 256 (fun j : Fin 14 => C026_digit j 13)=C026_columnCode 13 := by decide +kernel

theorem C026_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C026_digit j i)=C026_columnCode i := by
  intro i
  fin_cases i
  · exact C026_column_00
  · exact C026_column_01
  · exact C026_column_02
  · exact C026_column_03
  · exact C026_column_04
  · exact C026_column_05
  · exact C026_column_06
  · exact C026_column_07
  · exact C026_column_08
  · exact C026_column_09
  · exact C026_column_10
  · exact C026_column_11
  · exact C026_column_12
  · exact C026_column_13

def C026_data : PackedData 14 5 256 where
  raw := C026_digit
  digit_lt := C026_bound
  rowCode := C026_rowCode
  columnCode := C026_columnCode
  row_binding := C026_row_binding
  column_binding := C026_column_binding

def C027_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 1333659543619
  | 1 => 81101688842
  | 2 => 1194423227466
  | 3 => 147508008457
  | 4 => 1883645552836
  | 5 => 1197627709515
  | 6 => 1730235139091
  | 7 => 146298255056
  | 8 => 2510964439052
  | 9 => 1892386154242
  | 10 => 2439944351843
  | 11 => 2277729506913
  | 12 => 1936536438792
  | 13 => 1307859584650
  | _ => 0

def C027_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 40565132328609141826625541898755
  | 1 => 20362880541927090023643660484864
  | 2 => 40565129920128663912965493293057
  | 3 => 61165069930282635822473221898244
  | 4 => 313121287569560806900171010
  | 5 => 61006923085486293831559587824387
  | 6 => 316913859001540729586967577091
  | 7 => 81447170034701828481473868529666
  | 8 => 40724204001546880313928953430532
  | 9 => 317535261095190272223104664576
  | 10 => 40802813189337582507362640462594
  | 11 => 79542502190689391332838015235
  | 12 => 61164454587040379633851435122947
  | 13 => 40803746484829584971007344640002
  | _ => 0

def C027_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 60847543141168401013517744014082
  | 1 => 40644047374595456017983149768960
  | 2 => 40644359277401648698054253150466
  | 3 => 20361641397721244717195047535104
  | 4 => 81130571714858016191347691815683
  | 5 => 60926771298923405094234102104322
  | 6 => 61005687553872288839428682612995
  | 7 => 159388421076554151975263994368
  | 8 => 81208871427009843024767633064964
  | 9 => 40566060783601711529255088947971
  | 10 => 61164450960189061473500513174276
  | 11 => 20599635370292161988699254489348
  | 12 => 79232998254725642749973955587
  | 13 => 40644669966670048079833112511234
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

end SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryCaches05
