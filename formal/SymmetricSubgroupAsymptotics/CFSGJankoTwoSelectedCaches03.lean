import SymmetricSubgroupAsymptotics.MatrixKroneckerProductReflection
import Mathlib.Tactic.FinCases

/-! Literal14/F5 selected caches; digit bounds and both pack bindings are independently kernel checked. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedCaches03
open MatrixKroneckerProductReflection MatrixKroneckerDotReflection
open MatrixNaturalRowDotReflection SmallNaturalMatrixProductReflection

def C021_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 42271514
  | 1 => 2212098021459
  | 2 => 2440955430162
  | 3 => 575930442336
  | 4 => 1379006424338
  | 5 => 313935540312
  | 6 => 2295182476578
  | 7 => 1101024035484
  | 8 => 295422132356
  | 9 => 1687408656930
  | 10 => 72494433312
  | 11 => 1256698421328
  | 12 => 1305743771153
  | 13 => 1864207827555
  | _ => 0

def C021_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 60926456982988084344804121641730
  | 1 => 81288718564247814753098034971139
  | 2 => 20282719088698530499368086405380
  | 3 => 20520096513768541769408475956225
  | 4 => 317536474669445559713970258176
  | 5 => 81208868999695168481242644480514
  | 6 => 81210104521919564006335195513857
  | 7 => 61084913312738763893024416203268
  | 8 => 61164452159670221024409365512962
  | 9 => 20283342913292542895211610767616
  | 10 => 622611019613558339279062016
  | 11 => 20283028592597673382533728043264
  | 12 => 61085533477517053851574051471360
  | 13 => 61006304120170427326871816635392
  | _ => 0

def C021_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 40803742843848205529419595382784
  | 1 => 61005999461456188518260331839492
  | 2 => 40724515890222938815159521772292
  | 3 => 317223353474325045446646628353
  | 4 => 40724515899667815613512449786882
  | 5 => 237993986719785864065282475008
  | 6 => 40882972234177827471831641293060
  | 7 => 81367943081150349586838329491458
  | 8 => 81130257384626469627018782835712
  | 9 => 40881733085194203391585853636611
  | 10 => 316915086835056000375267000576
  | 11 => 158765819483371217483685036546
  | 12 => 20440869574365643524991168283394
  | 13 => 61164452155021785636312579113731
  | _ => 0

def C021_digit (i j : Fin 14) : ℕ := packedDigit 3 (C021_lowColumnCode j) i.val

private theorem C021_bound_00 : ∀ j : Fin 14, C021_digit 0 j < 5 := by decide +kernel

private theorem C021_bound_01 : ∀ j : Fin 14, C021_digit 1 j < 5 := by decide +kernel

private theorem C021_bound_02 : ∀ j : Fin 14, C021_digit 2 j < 5 := by decide +kernel

private theorem C021_bound_03 : ∀ j : Fin 14, C021_digit 3 j < 5 := by decide +kernel

private theorem C021_bound_04 : ∀ j : Fin 14, C021_digit 4 j < 5 := by decide +kernel

private theorem C021_bound_05 : ∀ j : Fin 14, C021_digit 5 j < 5 := by decide +kernel

private theorem C021_bound_06 : ∀ j : Fin 14, C021_digit 6 j < 5 := by decide +kernel

private theorem C021_bound_07 : ∀ j : Fin 14, C021_digit 7 j < 5 := by decide +kernel

private theorem C021_bound_08 : ∀ j : Fin 14, C021_digit 8 j < 5 := by decide +kernel

private theorem C021_bound_09 : ∀ j : Fin 14, C021_digit 9 j < 5 := by decide +kernel

private theorem C021_bound_10 : ∀ j : Fin 14, C021_digit 10 j < 5 := by decide +kernel

private theorem C021_bound_11 : ∀ j : Fin 14, C021_digit 11 j < 5 := by decide +kernel

private theorem C021_bound_12 : ∀ j : Fin 14, C021_digit 12 j < 5 := by decide +kernel

private theorem C021_bound_13 : ∀ j : Fin 14, C021_digit 13 j < 5 := by decide +kernel

theorem C021_bound : ∀ i j : Fin 14, C021_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C021_bound_00 j
  · exact C021_bound_01 j
  · exact C021_bound_02 j
  · exact C021_bound_03 j
  · exact C021_bound_04 j
  · exact C021_bound_05 j
  · exact C021_bound_06 j
  · exact C021_bound_07 j
  · exact C021_bound_08 j
  · exact C021_bound_09 j
  · exact C021_bound_10 j
  · exact C021_bound_11 j
  · exact C021_bound_12 j
  · exact C021_bound_13 j

private theorem C021_row_00 : pack 256 (C021_digit 0)=C021_rowCode 0 := by decide +kernel

private theorem C021_row_01 : pack 256 (C021_digit 1)=C021_rowCode 1 := by decide +kernel

private theorem C021_row_02 : pack 256 (C021_digit 2)=C021_rowCode 2 := by decide +kernel

private theorem C021_row_03 : pack 256 (C021_digit 3)=C021_rowCode 3 := by decide +kernel

private theorem C021_row_04 : pack 256 (C021_digit 4)=C021_rowCode 4 := by decide +kernel

private theorem C021_row_05 : pack 256 (C021_digit 5)=C021_rowCode 5 := by decide +kernel

private theorem C021_row_06 : pack 256 (C021_digit 6)=C021_rowCode 6 := by decide +kernel

private theorem C021_row_07 : pack 256 (C021_digit 7)=C021_rowCode 7 := by decide +kernel

private theorem C021_row_08 : pack 256 (C021_digit 8)=C021_rowCode 8 := by decide +kernel

private theorem C021_row_09 : pack 256 (C021_digit 9)=C021_rowCode 9 := by decide +kernel

private theorem C021_row_10 : pack 256 (C021_digit 10)=C021_rowCode 10 := by decide +kernel

private theorem C021_row_11 : pack 256 (C021_digit 11)=C021_rowCode 11 := by decide +kernel

private theorem C021_row_12 : pack 256 (C021_digit 12)=C021_rowCode 12 := by decide +kernel

private theorem C021_row_13 : pack 256 (C021_digit 13)=C021_rowCode 13 := by decide +kernel

theorem C021_row_binding : ∀ i : Fin 14, pack 256 (C021_digit i)=C021_rowCode i := by
  intro i
  fin_cases i
  · exact C021_row_00
  · exact C021_row_01
  · exact C021_row_02
  · exact C021_row_03
  · exact C021_row_04
  · exact C021_row_05
  · exact C021_row_06
  · exact C021_row_07
  · exact C021_row_08
  · exact C021_row_09
  · exact C021_row_10
  · exact C021_row_11
  · exact C021_row_12
  · exact C021_row_13

private theorem C021_column_00 : reversePack 256 (fun j : Fin 14 => C021_digit j 0)=C021_columnCode 0 := by decide +kernel

private theorem C021_column_01 : reversePack 256 (fun j : Fin 14 => C021_digit j 1)=C021_columnCode 1 := by decide +kernel

private theorem C021_column_02 : reversePack 256 (fun j : Fin 14 => C021_digit j 2)=C021_columnCode 2 := by decide +kernel

private theorem C021_column_03 : reversePack 256 (fun j : Fin 14 => C021_digit j 3)=C021_columnCode 3 := by decide +kernel

private theorem C021_column_04 : reversePack 256 (fun j : Fin 14 => C021_digit j 4)=C021_columnCode 4 := by decide +kernel

private theorem C021_column_05 : reversePack 256 (fun j : Fin 14 => C021_digit j 5)=C021_columnCode 5 := by decide +kernel

private theorem C021_column_06 : reversePack 256 (fun j : Fin 14 => C021_digit j 6)=C021_columnCode 6 := by decide +kernel

private theorem C021_column_07 : reversePack 256 (fun j : Fin 14 => C021_digit j 7)=C021_columnCode 7 := by decide +kernel

private theorem C021_column_08 : reversePack 256 (fun j : Fin 14 => C021_digit j 8)=C021_columnCode 8 := by decide +kernel

private theorem C021_column_09 : reversePack 256 (fun j : Fin 14 => C021_digit j 9)=C021_columnCode 9 := by decide +kernel

private theorem C021_column_10 : reversePack 256 (fun j : Fin 14 => C021_digit j 10)=C021_columnCode 10 := by decide +kernel

private theorem C021_column_11 : reversePack 256 (fun j : Fin 14 => C021_digit j 11)=C021_columnCode 11 := by decide +kernel

private theorem C021_column_12 : reversePack 256 (fun j : Fin 14 => C021_digit j 12)=C021_columnCode 12 := by decide +kernel

private theorem C021_column_13 : reversePack 256 (fun j : Fin 14 => C021_digit j 13)=C021_columnCode 13 := by decide +kernel

theorem C021_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C021_digit j i)=C021_columnCode i := by
  intro i
  fin_cases i
  · exact C021_column_00
  · exact C021_column_01
  · exact C021_column_02
  · exact C021_column_03
  · exact C021_column_04
  · exact C021_column_05
  · exact C021_column_06
  · exact C021_column_07
  · exact C021_column_08
  · exact C021_column_09
  · exact C021_column_10
  · exact C021_column_11
  · exact C021_column_12
  · exact C021_column_13

def C021_data : PackedData 14 5 256 where
  raw := C021_digit
  digit_lt := C021_bound
  rowCode := C021_rowCode
  columnCode := C021_columnCode
  row_binding := C021_row_binding
  column_binding := C021_column_binding

def C022_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 2439865477130
  | 1 => 1384094180107
  | 2 => 2477396133588
  | 3 => 2474207740953
  | 4 => 1884690327328
  | 5 => 81674404420
  | 6 => 695919055008
  | 7 => 2431161741858
  | 8 => 233157832737
  | 9 => 1203689784524
  | 10 => 89559016724
  | 11 => 1190262476876
  | 12 => 1936496543457
  | 13 => 1258564977444
  | _ => 0

def C022_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 81210109371771566667312576856834
  | 1 => 81446862972321642435948027445505
  | 2 => 81367637237029674524830641357824
  | 3 => 20520096518490907690431991185668
  | 4 => 317224552974074611188059079170
  | 5 => 60847233651454444316522421813761
  | 6 => 81447479519730240688016287073284
  | 7 => 40644358082679893796296232928002
  | 8 => 311907602562036044660736515
  | 9 => 20600563820543991081635198140418
  | 10 => 81368564473707032164086346612992
  | 11 => 40644668776633909723953042030852
  | 12 => 40882042556073962609901882835971
  | 13 => 40803122674310798028415955108356
  | _ => 0

def C022_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 40644052214984352150450975539972
  | 1 => 60927696131916296135226203112450
  | 2 => 81289026821479315531551956009988
  | 3 => 20520096509119962265032675296260
  | 4 => 318154226318751276016597140227
  | 5 => 81129949108560985858215818363136
  | 6 => 317531624872853499680403816961
  | 7 => 40881733080453462506997113094916
  | 8 => 20599322267949758878467053781760
  | 9 => 81209797450020497168920217911554
  | 10 => 81289335107044655206230405546240
  | 11 => 81209176066853350316694768320770
  | 12 => 20600254354405405096762065093635
  | 13 => 81447790213684473066618850771458
  | _ => 0

def C022_digit (i j : Fin 14) : ℕ := packedDigit 3 (C022_lowColumnCode j) i.val

private theorem C022_bound_00 : ∀ j : Fin 14, C022_digit 0 j < 5 := by decide +kernel

private theorem C022_bound_01 : ∀ j : Fin 14, C022_digit 1 j < 5 := by decide +kernel

private theorem C022_bound_02 : ∀ j : Fin 14, C022_digit 2 j < 5 := by decide +kernel

private theorem C022_bound_03 : ∀ j : Fin 14, C022_digit 3 j < 5 := by decide +kernel

private theorem C022_bound_04 : ∀ j : Fin 14, C022_digit 4 j < 5 := by decide +kernel

private theorem C022_bound_05 : ∀ j : Fin 14, C022_digit 5 j < 5 := by decide +kernel

private theorem C022_bound_06 : ∀ j : Fin 14, C022_digit 6 j < 5 := by decide +kernel

private theorem C022_bound_07 : ∀ j : Fin 14, C022_digit 7 j < 5 := by decide +kernel

private theorem C022_bound_08 : ∀ j : Fin 14, C022_digit 8 j < 5 := by decide +kernel

private theorem C022_bound_09 : ∀ j : Fin 14, C022_digit 9 j < 5 := by decide +kernel

private theorem C022_bound_10 : ∀ j : Fin 14, C022_digit 10 j < 5 := by decide +kernel

private theorem C022_bound_11 : ∀ j : Fin 14, C022_digit 11 j < 5 := by decide +kernel

private theorem C022_bound_12 : ∀ j : Fin 14, C022_digit 12 j < 5 := by decide +kernel

private theorem C022_bound_13 : ∀ j : Fin 14, C022_digit 13 j < 5 := by decide +kernel

theorem C022_bound : ∀ i j : Fin 14, C022_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C022_bound_00 j
  · exact C022_bound_01 j
  · exact C022_bound_02 j
  · exact C022_bound_03 j
  · exact C022_bound_04 j
  · exact C022_bound_05 j
  · exact C022_bound_06 j
  · exact C022_bound_07 j
  · exact C022_bound_08 j
  · exact C022_bound_09 j
  · exact C022_bound_10 j
  · exact C022_bound_11 j
  · exact C022_bound_12 j
  · exact C022_bound_13 j

private theorem C022_row_00 : pack 256 (C022_digit 0)=C022_rowCode 0 := by decide +kernel

private theorem C022_row_01 : pack 256 (C022_digit 1)=C022_rowCode 1 := by decide +kernel

private theorem C022_row_02 : pack 256 (C022_digit 2)=C022_rowCode 2 := by decide +kernel

private theorem C022_row_03 : pack 256 (C022_digit 3)=C022_rowCode 3 := by decide +kernel

private theorem C022_row_04 : pack 256 (C022_digit 4)=C022_rowCode 4 := by decide +kernel

private theorem C022_row_05 : pack 256 (C022_digit 5)=C022_rowCode 5 := by decide +kernel

private theorem C022_row_06 : pack 256 (C022_digit 6)=C022_rowCode 6 := by decide +kernel

private theorem C022_row_07 : pack 256 (C022_digit 7)=C022_rowCode 7 := by decide +kernel

private theorem C022_row_08 : pack 256 (C022_digit 8)=C022_rowCode 8 := by decide +kernel

private theorem C022_row_09 : pack 256 (C022_digit 9)=C022_rowCode 9 := by decide +kernel

private theorem C022_row_10 : pack 256 (C022_digit 10)=C022_rowCode 10 := by decide +kernel

private theorem C022_row_11 : pack 256 (C022_digit 11)=C022_rowCode 11 := by decide +kernel

private theorem C022_row_12 : pack 256 (C022_digit 12)=C022_rowCode 12 := by decide +kernel

private theorem C022_row_13 : pack 256 (C022_digit 13)=C022_rowCode 13 := by decide +kernel

theorem C022_row_binding : ∀ i : Fin 14, pack 256 (C022_digit i)=C022_rowCode i := by
  intro i
  fin_cases i
  · exact C022_row_00
  · exact C022_row_01
  · exact C022_row_02
  · exact C022_row_03
  · exact C022_row_04
  · exact C022_row_05
  · exact C022_row_06
  · exact C022_row_07
  · exact C022_row_08
  · exact C022_row_09
  · exact C022_row_10
  · exact C022_row_11
  · exact C022_row_12
  · exact C022_row_13

private theorem C022_column_00 : reversePack 256 (fun j : Fin 14 => C022_digit j 0)=C022_columnCode 0 := by decide +kernel

private theorem C022_column_01 : reversePack 256 (fun j : Fin 14 => C022_digit j 1)=C022_columnCode 1 := by decide +kernel

private theorem C022_column_02 : reversePack 256 (fun j : Fin 14 => C022_digit j 2)=C022_columnCode 2 := by decide +kernel

private theorem C022_column_03 : reversePack 256 (fun j : Fin 14 => C022_digit j 3)=C022_columnCode 3 := by decide +kernel

private theorem C022_column_04 : reversePack 256 (fun j : Fin 14 => C022_digit j 4)=C022_columnCode 4 := by decide +kernel

private theorem C022_column_05 : reversePack 256 (fun j : Fin 14 => C022_digit j 5)=C022_columnCode 5 := by decide +kernel

private theorem C022_column_06 : reversePack 256 (fun j : Fin 14 => C022_digit j 6)=C022_columnCode 6 := by decide +kernel

private theorem C022_column_07 : reversePack 256 (fun j : Fin 14 => C022_digit j 7)=C022_columnCode 7 := by decide +kernel

private theorem C022_column_08 : reversePack 256 (fun j : Fin 14 => C022_digit j 8)=C022_columnCode 8 := by decide +kernel

private theorem C022_column_09 : reversePack 256 (fun j : Fin 14 => C022_digit j 9)=C022_columnCode 9 := by decide +kernel

private theorem C022_column_10 : reversePack 256 (fun j : Fin 14 => C022_digit j 10)=C022_columnCode 10 := by decide +kernel

private theorem C022_column_11 : reversePack 256 (fun j : Fin 14 => C022_digit j 11)=C022_columnCode 11 := by decide +kernel

private theorem C022_column_12 : reversePack 256 (fun j : Fin 14 => C022_digit j 12)=C022_columnCode 12 := by decide +kernel

private theorem C022_column_13 : reversePack 256 (fun j : Fin 14 => C022_digit j 13)=C022_columnCode 13 := by decide +kernel

theorem C022_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C022_digit j i)=C022_columnCode i := by
  intro i
  fin_cases i
  · exact C022_column_00
  · exact C022_column_01
  · exact C022_column_02
  · exact C022_column_03
  · exact C022_column_04
  · exact C022_column_05
  · exact C022_column_06
  · exact C022_column_07
  · exact C022_column_08
  · exact C022_column_09
  · exact C022_column_10
  · exact C022_column_11
  · exact C022_column_12
  · exact C022_column_13

def C022_data : PackedData 14 5 256 where
  raw := C022_digit
  digit_lt := C022_bound
  rowCode := C022_rowCode
  columnCode := C022_columnCode
  row_binding := C022_row_binding
  column_binding := C022_column_binding

def C023_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 1196352901778
  | 1 => 97180469410
  | 2 => 1169712002186
  | 3 => 176553268804
  | 4 => 1136229363971
  | 5 => 824777164897
  | 6 => 1662627348744
  | 7 => 1126897173202
  | 8 => 1308153872404
  | 9 => 2278686008546
  | 10 => 1238586722532
  | 11 => 35876550308
  | 12 => 1936496543457
  | 13 => 1258564977444
  | _ => 0

def C023_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 81210109362382173930508815303170
  | 1 => 81447793859332806705641877996546
  | 2 => 81367945513113892991002275348994
  | 3 => 20521027391372010958182181635073
  | 4 => 317841114531542586106740671489
  | 5 => 60847541932187312658012990144513
  | 6 => 81447171248387125368014036337156
  | 7 => 40644980669995225327503516238593
  | 8 => 620197908716338457180372996
  | 9 => 20600255549201019314966303540225
  | 10 => 81367633605566815305656847892994
  | 11 => 40645285314579473502906928333571
  | 12 => 40881734279989744147015881785601
  | 13 => 40802506131624277470280591474690
  | _ => 0

def C023_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 40723895716018433571045073158402
  | 1 => 40882355681972930238031627223296
  | 2 => 40644668771874505918123383718146
  | 3 => 81129951531153294761092773577216
  | 4 => 60848466765161613403809984544770
  | 5 => 20599636593329957552145456694273
  | 6 => 80466102553838515605546795011
  | 7 => 40724205215250622816439622631426
  | 8 => 81288094739635426548164876829442
  | 9 => 40882662739723200541566278107396
  | 10 => 81447484355451894956717835813378
  | 11 => 81447173675646531734695731003392
  | 12 => 20600254354405405096762065093635
  | 13 => 81447790213684473066618850771458
  | _ => 0

def C023_digit (i j : Fin 14) : ℕ := packedDigit 3 (C023_lowColumnCode j) i.val

private theorem C023_bound_00 : ∀ j : Fin 14, C023_digit 0 j < 5 := by decide +kernel

private theorem C023_bound_01 : ∀ j : Fin 14, C023_digit 1 j < 5 := by decide +kernel

private theorem C023_bound_02 : ∀ j : Fin 14, C023_digit 2 j < 5 := by decide +kernel

private theorem C023_bound_03 : ∀ j : Fin 14, C023_digit 3 j < 5 := by decide +kernel

private theorem C023_bound_04 : ∀ j : Fin 14, C023_digit 4 j < 5 := by decide +kernel

private theorem C023_bound_05 : ∀ j : Fin 14, C023_digit 5 j < 5 := by decide +kernel

private theorem C023_bound_06 : ∀ j : Fin 14, C023_digit 6 j < 5 := by decide +kernel

private theorem C023_bound_07 : ∀ j : Fin 14, C023_digit 7 j < 5 := by decide +kernel

private theorem C023_bound_08 : ∀ j : Fin 14, C023_digit 8 j < 5 := by decide +kernel

private theorem C023_bound_09 : ∀ j : Fin 14, C023_digit 9 j < 5 := by decide +kernel

private theorem C023_bound_10 : ∀ j : Fin 14, C023_digit 10 j < 5 := by decide +kernel

private theorem C023_bound_11 : ∀ j : Fin 14, C023_digit 11 j < 5 := by decide +kernel

private theorem C023_bound_12 : ∀ j : Fin 14, C023_digit 12 j < 5 := by decide +kernel

private theorem C023_bound_13 : ∀ j : Fin 14, C023_digit 13 j < 5 := by decide +kernel

theorem C023_bound : ∀ i j : Fin 14, C023_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C023_bound_00 j
  · exact C023_bound_01 j
  · exact C023_bound_02 j
  · exact C023_bound_03 j
  · exact C023_bound_04 j
  · exact C023_bound_05 j
  · exact C023_bound_06 j
  · exact C023_bound_07 j
  · exact C023_bound_08 j
  · exact C023_bound_09 j
  · exact C023_bound_10 j
  · exact C023_bound_11 j
  · exact C023_bound_12 j
  · exact C023_bound_13 j

private theorem C023_row_00 : pack 256 (C023_digit 0)=C023_rowCode 0 := by decide +kernel

private theorem C023_row_01 : pack 256 (C023_digit 1)=C023_rowCode 1 := by decide +kernel

private theorem C023_row_02 : pack 256 (C023_digit 2)=C023_rowCode 2 := by decide +kernel

private theorem C023_row_03 : pack 256 (C023_digit 3)=C023_rowCode 3 := by decide +kernel

private theorem C023_row_04 : pack 256 (C023_digit 4)=C023_rowCode 4 := by decide +kernel

private theorem C023_row_05 : pack 256 (C023_digit 5)=C023_rowCode 5 := by decide +kernel

private theorem C023_row_06 : pack 256 (C023_digit 6)=C023_rowCode 6 := by decide +kernel

private theorem C023_row_07 : pack 256 (C023_digit 7)=C023_rowCode 7 := by decide +kernel

private theorem C023_row_08 : pack 256 (C023_digit 8)=C023_rowCode 8 := by decide +kernel

private theorem C023_row_09 : pack 256 (C023_digit 9)=C023_rowCode 9 := by decide +kernel

private theorem C023_row_10 : pack 256 (C023_digit 10)=C023_rowCode 10 := by decide +kernel

private theorem C023_row_11 : pack 256 (C023_digit 11)=C023_rowCode 11 := by decide +kernel

private theorem C023_row_12 : pack 256 (C023_digit 12)=C023_rowCode 12 := by decide +kernel

private theorem C023_row_13 : pack 256 (C023_digit 13)=C023_rowCode 13 := by decide +kernel

theorem C023_row_binding : ∀ i : Fin 14, pack 256 (C023_digit i)=C023_rowCode i := by
  intro i
  fin_cases i
  · exact C023_row_00
  · exact C023_row_01
  · exact C023_row_02
  · exact C023_row_03
  · exact C023_row_04
  · exact C023_row_05
  · exact C023_row_06
  · exact C023_row_07
  · exact C023_row_08
  · exact C023_row_09
  · exact C023_row_10
  · exact C023_row_11
  · exact C023_row_12
  · exact C023_row_13

private theorem C023_column_00 : reversePack 256 (fun j : Fin 14 => C023_digit j 0)=C023_columnCode 0 := by decide +kernel

private theorem C023_column_01 : reversePack 256 (fun j : Fin 14 => C023_digit j 1)=C023_columnCode 1 := by decide +kernel

private theorem C023_column_02 : reversePack 256 (fun j : Fin 14 => C023_digit j 2)=C023_columnCode 2 := by decide +kernel

private theorem C023_column_03 : reversePack 256 (fun j : Fin 14 => C023_digit j 3)=C023_columnCode 3 := by decide +kernel

private theorem C023_column_04 : reversePack 256 (fun j : Fin 14 => C023_digit j 4)=C023_columnCode 4 := by decide +kernel

private theorem C023_column_05 : reversePack 256 (fun j : Fin 14 => C023_digit j 5)=C023_columnCode 5 := by decide +kernel

private theorem C023_column_06 : reversePack 256 (fun j : Fin 14 => C023_digit j 6)=C023_columnCode 6 := by decide +kernel

private theorem C023_column_07 : reversePack 256 (fun j : Fin 14 => C023_digit j 7)=C023_columnCode 7 := by decide +kernel

private theorem C023_column_08 : reversePack 256 (fun j : Fin 14 => C023_digit j 8)=C023_columnCode 8 := by decide +kernel

private theorem C023_column_09 : reversePack 256 (fun j : Fin 14 => C023_digit j 9)=C023_columnCode 9 := by decide +kernel

private theorem C023_column_10 : reversePack 256 (fun j : Fin 14 => C023_digit j 10)=C023_columnCode 10 := by decide +kernel

private theorem C023_column_11 : reversePack 256 (fun j : Fin 14 => C023_digit j 11)=C023_columnCode 11 := by decide +kernel

private theorem C023_column_12 : reversePack 256 (fun j : Fin 14 => C023_digit j 12)=C023_columnCode 12 := by decide +kernel

private theorem C023_column_13 : reversePack 256 (fun j : Fin 14 => C023_digit j 13)=C023_columnCode 13 := by decide +kernel

theorem C023_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C023_digit j i)=C023_columnCode i := by
  intro i
  fin_cases i
  · exact C023_column_00
  · exact C023_column_01
  · exact C023_column_02
  · exact C023_column_03
  · exact C023_column_04
  · exact C023_column_05
  · exact C023_column_06
  · exact C023_column_07
  · exact C023_column_08
  · exact C023_column_09
  · exact C023_column_10
  · exact C023_column_11
  · exact C023_column_12
  · exact C023_column_13

def C023_data : PackedData 14 5 256 where
  raw := C023_digit
  digit_lt := C023_bound
  rowCode := C023_rowCode
  columnCode := C023_columnCode
  row_binding := C023_row_binding
  column_binding := C023_column_binding

def C024_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 1806340032088
  | 1 => 2286586267914
  | 2 => 286714513089
  | 3 => 722781349027
  | 4 => 1882859611426
  | 5 => 627067602980
  | 6 => 769355957000
  | 7 => 1262723056860
  | 8 => 1803920622083
  | 9 => 2225195975874
  | 10 => 1101038657728
  | 11 => 776775663826
  | 12 => 2277983236292
  | 13 => 1378203256065
  | _ => 0

def C024_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 20599941233228731897202134286848
  | 1 => 618970019859148809833545987
  | 2 => 81368254998123714334971505345537
  | 3 => 40564819216766664958777225315331
  | 4 => 81367325320075190274805553430528
  | 5 => 20520095300120355108963980673795
  | 6 => 81130877568349638647984232137216
  | 7 => 40803432149875670236054147039490
  | 8 => 61006617217827356595757837779714
  | 9 => 81447483160637762499782918538242
  | 10 => 60927386637424560385174865641730
  | 11 => 79847146738116419856902455810
  | 12 => 81209795032187448517461578875138
  | 13 => 40882043779166809334070927950851
  | _ => 0

def C024_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 237997599385413999115609702915
  | 1 => 40645290145615653656479557353732
  | 2 => 20283341704348132419113037399040
  | 3 => 61164762858328083789929819406849
  | 4 => 40882972224751612463335168213763
  | 5 => 81446555919256555775227475329281
  | 6 => 80467330369123776944085730049
  | 7 => 81368253793938635045249503920642
  | 8 => 60847230038770512992930646589955
  | 9 => 40565750080184516169965949353988
  | 10 => 928464492715805924648812546
  | 11 => 40724203987361622636400316908289
  | 12 => 81130566883858586258466393882884
  | 13 => 20283649980450796505674660447234
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
  | 0 => 158947936394
  | 1 => 1943607452377
  | 2 => 1170452121888
  | 3 => 1791153423939
  | 4 => 26901094624
  | 5 => 2483036766817
  | 6 => 2211120166041
  | 7 => 2226140512779
  | 8 => 224437810176
  | 9 => 645797070532
  | 10 => 1333779112978
  | 11 => 586313958976
  | 12 => 2277983236292
  | 13 => 1378203256065
  | _ => 0

def C025_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 20599324690450049390415009808642
  | 1 => 2417851712135692544115457
  | 2 => 81367632401326396066309664408322
  | 3 => 40565750094388509670758934642948
  | 4 => 81367325338945920950359329604096
  | 5 => 20520717906399083101278005624834
  | 6 => 81130261011440965512399966700034
  | 7 => 40802507340586989731935085068288
  | 8 => 61006617236698375783162709278722
  | 9 => 81446552287756802791937383858432
  | 10 => 60927078366081443657797781815812
  | 11 => 80469743535217953881808962050
  | 12 => 81208870208676111596758927213570
  | 13 => 40882043764944514616139553309440
  | _ => 0

def C025_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 40644671175577563939676780364288
  | 1 => 20521023764594624167494927123459
  | 2 => 318155425873409014283622154498
  | 3 => 60847541941632045623756609028611
  | 4 => 317841114605258348120074551296
  | 5 => 20599632966607694825303870342148
  | 6 => 20520715493232988921028845568004
  | 7 => 60926458182413830761472894107652
  | 8 => 2432055777408202215392000
  | 9 => 81130570515339965124819558793473
  | 10 => 40723277959702245714883976037122
  | 11 => 313111824317795590312558593
  | 12 => 81130566883858586258466393882884
  | 13 => 20283649980450796505674660447234
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
  | 0 => 227939985562
  | 1 => 569141932036
  | 2 => 655307720353
  | 3 => 2485100492881
  | 4 => 1411191156771
  | 5 => 2415978098840
  | 6 => 1894523410569
  | 7 => 863482558732
  | 8 => 1305670103201
  | 9 => 2336617935619
  | 10 => 2406834279003
  | 11 => 861160441936
  | 12 => 294208443425
  | 13 => 563085678153
  | _ => 0

def C026_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 20361641407129228309974994715650
  | 1 => 20599944850579688627026002182147
  | 2 => 20282720316513959598796296028162
  | 3 => 61006924289671300781078686662660
  | 4 => 20361638989314410514568595112706
  | 5 => 60927386637443294796670461804800
  | 6 => 20599941233173391943161725583362
  | 7 => 81209180907279067881923638658050
  | 8 => 40565131114887384644126169563906
  | 9 => 60847233651380729115255706353666
  | 10 => 81288714918580962034226422743556
  | 11 => 20442103868719773836802005402114
  | 12 => 318154226374163850613881896963
  | 13 => 20282723943291202553584346530048
  | _ => 0

def C026_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 40803127510013932655414282945280
  | 1 => 81129638428792229017670125748225
  | 2 => 20599944869469083063851908595969
  | 3 => 20441180263560543595728134538244
  | 4 => 61164141475179385370615021306882
  | 5 => 238303471729608338319530328836
  | 6 => 20362261576648188785442951529219
  | 7 => 81210109367104685656656876667905
  | 8 => 20599941237913916657141521842946
  | 9 => 60848467974087360394596599202308
  | 10 => 61085223997174259599379766706948
  | 11 => 158770645797113108756238173185
  | 12 => 20599324676301468742374293373952
  | 13 => 20361950882730994851293738106881
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

end SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedCaches03
