import SymmetricSubgroupAsymptotics.MatrixKroneckerProductReflection
import Mathlib.Tactic.FinCases

/-! Literal14/F5 selected caches; digit bounds and both pack bindings are independently kernel checked. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryCaches06
open MatrixKroneckerProductReflection MatrixKroneckerDotReflection
open MatrixNaturalRowDotReflection SmallNaturalMatrixProductReflection

def C028_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 619989992595
  | 1 => 273781836
  | 2 => 1745252590690
  | 3 => 1307205435995
  | 4 => 1756778542336
  | 5 => 1943750198050
  | 6 => 1882472879268
  | 7 => 1745151476900
  | 8 => 2487055369985
  | 9 => 568316741316
  | 10 => 1172567004369
  | 11 => 2277729506913
  | 12 => 2511956717595
  | 13 => 1857876166939
  | _ => 0

def C028_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 61085224011341647278347707876355
  | 1 => 61086153656389018254829789905154
  | 2 => 81129951540634992992202300391682
  | 3 => 81130569301710369320329740943874
  | 4 => 237995200441975396514010366208
  | 5 => 20521333249641483401776431497985
  | 6 => 61005689990631624571452880192514
  | 7 => 159078931270435518422775300610
  | 8 => 40882662739686451727154563579906
  | 9 => 40803122674347547403565714833923
  | 10 => 40802818020355459464710276055041
  | 11 => 317222144530275424679147798528
  | 12 => 61164452155021569464630027288577
  | 13 => 61165381823699363711432159068161
  | _ => 0

def C028_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 61006306523873413290848304496897
  | 1 => 81209178484760402116135092224000
  | 2 => 40882043769703629624257928167683
  | 3 => 61085223992433518431125666530050
  | 4 => 1240372095061942957018185987
  | 5 => 40882971025288901342042777584643
  | 6 => 81447172457275834478379669848835
  | 7 => 81447172471498274158114517483779
  | 8 => 20283651189394990240526445380612
  | 9 => 81130570515340252790042438795265
  | 10 => 20441796806302404667542389915906
  | 11 => 20599635370292161988699254489348
  | 12 => 61084913312720388648001461289988
  | 13 => 61086156074259031042477453738755
  | _ => 0

def C028_digit (i j : Fin 14) : ℕ := packedDigit 3 (C028_lowColumnCode j) i.val

private theorem C028_bound_00 : ∀ j : Fin 14, C028_digit 0 j < 5 := by decide +kernel

private theorem C028_bound_01 : ∀ j : Fin 14, C028_digit 1 j < 5 := by decide +kernel

private theorem C028_bound_02 : ∀ j : Fin 14, C028_digit 2 j < 5 := by decide +kernel

private theorem C028_bound_03 : ∀ j : Fin 14, C028_digit 3 j < 5 := by decide +kernel

private theorem C028_bound_04 : ∀ j : Fin 14, C028_digit 4 j < 5 := by decide +kernel

private theorem C028_bound_05 : ∀ j : Fin 14, C028_digit 5 j < 5 := by decide +kernel

private theorem C028_bound_06 : ∀ j : Fin 14, C028_digit 6 j < 5 := by decide +kernel

private theorem C028_bound_07 : ∀ j : Fin 14, C028_digit 7 j < 5 := by decide +kernel

private theorem C028_bound_08 : ∀ j : Fin 14, C028_digit 8 j < 5 := by decide +kernel

private theorem C028_bound_09 : ∀ j : Fin 14, C028_digit 9 j < 5 := by decide +kernel

private theorem C028_bound_10 : ∀ j : Fin 14, C028_digit 10 j < 5 := by decide +kernel

private theorem C028_bound_11 : ∀ j : Fin 14, C028_digit 11 j < 5 := by decide +kernel

private theorem C028_bound_12 : ∀ j : Fin 14, C028_digit 12 j < 5 := by decide +kernel

private theorem C028_bound_13 : ∀ j : Fin 14, C028_digit 13 j < 5 := by decide +kernel

theorem C028_bound : ∀ i j : Fin 14, C028_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C028_bound_00 j
  · exact C028_bound_01 j
  · exact C028_bound_02 j
  · exact C028_bound_03 j
  · exact C028_bound_04 j
  · exact C028_bound_05 j
  · exact C028_bound_06 j
  · exact C028_bound_07 j
  · exact C028_bound_08 j
  · exact C028_bound_09 j
  · exact C028_bound_10 j
  · exact C028_bound_11 j
  · exact C028_bound_12 j
  · exact C028_bound_13 j

private theorem C028_row_00 : pack 256 (C028_digit 0)=C028_rowCode 0 := by decide +kernel

private theorem C028_row_01 : pack 256 (C028_digit 1)=C028_rowCode 1 := by decide +kernel

private theorem C028_row_02 : pack 256 (C028_digit 2)=C028_rowCode 2 := by decide +kernel

private theorem C028_row_03 : pack 256 (C028_digit 3)=C028_rowCode 3 := by decide +kernel

private theorem C028_row_04 : pack 256 (C028_digit 4)=C028_rowCode 4 := by decide +kernel

private theorem C028_row_05 : pack 256 (C028_digit 5)=C028_rowCode 5 := by decide +kernel

private theorem C028_row_06 : pack 256 (C028_digit 6)=C028_rowCode 6 := by decide +kernel

private theorem C028_row_07 : pack 256 (C028_digit 7)=C028_rowCode 7 := by decide +kernel

private theorem C028_row_08 : pack 256 (C028_digit 8)=C028_rowCode 8 := by decide +kernel

private theorem C028_row_09 : pack 256 (C028_digit 9)=C028_rowCode 9 := by decide +kernel

private theorem C028_row_10 : pack 256 (C028_digit 10)=C028_rowCode 10 := by decide +kernel

private theorem C028_row_11 : pack 256 (C028_digit 11)=C028_rowCode 11 := by decide +kernel

private theorem C028_row_12 : pack 256 (C028_digit 12)=C028_rowCode 12 := by decide +kernel

private theorem C028_row_13 : pack 256 (C028_digit 13)=C028_rowCode 13 := by decide +kernel

theorem C028_row_binding : ∀ i : Fin 14, pack 256 (C028_digit i)=C028_rowCode i := by
  intro i
  fin_cases i
  · exact C028_row_00
  · exact C028_row_01
  · exact C028_row_02
  · exact C028_row_03
  · exact C028_row_04
  · exact C028_row_05
  · exact C028_row_06
  · exact C028_row_07
  · exact C028_row_08
  · exact C028_row_09
  · exact C028_row_10
  · exact C028_row_11
  · exact C028_row_12
  · exact C028_row_13

private theorem C028_column_00 : reversePack 256 (fun j : Fin 14 => C028_digit j 0)=C028_columnCode 0 := by decide +kernel

private theorem C028_column_01 : reversePack 256 (fun j : Fin 14 => C028_digit j 1)=C028_columnCode 1 := by decide +kernel

private theorem C028_column_02 : reversePack 256 (fun j : Fin 14 => C028_digit j 2)=C028_columnCode 2 := by decide +kernel

private theorem C028_column_03 : reversePack 256 (fun j : Fin 14 => C028_digit j 3)=C028_columnCode 3 := by decide +kernel

private theorem C028_column_04 : reversePack 256 (fun j : Fin 14 => C028_digit j 4)=C028_columnCode 4 := by decide +kernel

private theorem C028_column_05 : reversePack 256 (fun j : Fin 14 => C028_digit j 5)=C028_columnCode 5 := by decide +kernel

private theorem C028_column_06 : reversePack 256 (fun j : Fin 14 => C028_digit j 6)=C028_columnCode 6 := by decide +kernel

private theorem C028_column_07 : reversePack 256 (fun j : Fin 14 => C028_digit j 7)=C028_columnCode 7 := by decide +kernel

private theorem C028_column_08 : reversePack 256 (fun j : Fin 14 => C028_digit j 8)=C028_columnCode 8 := by decide +kernel

private theorem C028_column_09 : reversePack 256 (fun j : Fin 14 => C028_digit j 9)=C028_columnCode 9 := by decide +kernel

private theorem C028_column_10 : reversePack 256 (fun j : Fin 14 => C028_digit j 10)=C028_columnCode 10 := by decide +kernel

private theorem C028_column_11 : reversePack 256 (fun j : Fin 14 => C028_digit j 11)=C028_columnCode 11 := by decide +kernel

private theorem C028_column_12 : reversePack 256 (fun j : Fin 14 => C028_digit j 12)=C028_columnCode 12 := by decide +kernel

private theorem C028_column_13 : reversePack 256 (fun j : Fin 14 => C028_digit j 13)=C028_columnCode 13 := by decide +kernel

theorem C028_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C028_digit j i)=C028_columnCode i := by
  intro i
  fin_cases i
  · exact C028_column_00
  · exact C028_column_01
  · exact C028_column_02
  · exact C028_column_03
  · exact C028_column_04
  · exact C028_column_05
  · exact C028_column_06
  · exact C028_column_07
  · exact C028_column_08
  · exact C028_column_09
  · exact C028_column_10
  · exact C028_column_11
  · exact C028_column_12
  · exact C028_column_13

def C028_data : PackedData 14 5 256 where
  raw := C028_digit
  digit_lt := C028_bound
  rowCode := C028_rowCode
  columnCode := C028_columnCode
  row_binding := C028_row_binding
  column_binding := C028_column_binding

def C029_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 1662344048868
  | 1 => 1755757035540
  | 2 => 700239877772
  | 3 => 619855626305
  | 4 => 569284858002
  | 5 => 1197627709515
  | 6 => 2504119695138
  | 7 => 210722762848
  | 8 => 628544129316
  | 9 => 1135223023371
  | 10 => 2439944351843
  | 11 => 2277729506913
  | 12 => 635932057601
  | 13 => 2233822413834
  | _ => 0

def C029_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 40644360495845772365605164549124
  | 1 => 20283652384190677079287492837892
  | 2 => 310712898967052073381789699
  | 3 => 40565747676573692156827427602432
  | 4 => 158769446334545824488383120387
  | 5 => 40724513477167597719909495276546
  | 6 => 81129639642440630725005384286467
  | 7 => 20599941242636283422585689211395
  | 8 => 40565747662332805164592867115779
  | 9 => 61006307742280859078980150558977
  | 10 => 309489750923931595279958788
  | 11 => 81288409079256223697845862073345
  | 12 => 79541274320208570405051564288
  | 13 => 81210109362326690710090388931331
  | _ => 0

def C029_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 81447479533897413038635650973699
  | 1 => 81288094758598535902596383899907
  | 2 => 81209489178659078094136771936769
  | 3 => 20282719107624817299541016445185
  | 4 => 40723894507129290990306226995201
  | 5 => 60926771298923405094234102104322
  | 6 => 40882973438418173245101801931780
  | 7 => 317222149307981293137445257984
  | 8 => 81447793859369628131810114339073
  | 9 => 60927698549749488899695386558466
  | 10 => 61164450960189061473500513174276
  | 11 => 20599635370292161988699254489348
  | 12 => 20282409613133298003742457725185
  | 13 => 40644049787706426416956851879940
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
  | 0 => 1334984615427
  | 1 => 1275104624897
  | 2 => 777949694017
  | 3 => 1737619251275
  | 4 => 1401527765249
  | 5 => 8858435584
  | 6 => 164702341396
  | 7 => 1719672094987
  | 8 => 2512833778249
  | 9 => 2220549025880
  | 10 => 1825665717280
  | 11 => 1307205543649
  | 12 => 2356870677128
  | 13 => 2233822413834
  | _ => 0

def C030_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 40565128692331826235723302895875
  | 1 => 20362880556094117413559046504448
  | 2 => 159384784799095293629872276480
  | 3 => 40644978242717156319943366803459
  | 4 => 620193131297853725361831938
  | 5 => 40644975834310466231392610287873
  | 6 => 81446862977044008074392742527490
  | 7 => 20521333240233571580726105800962
  | 8 => 40565750094351832072823418978819
  | 9 => 60848159683873297101462425568258
  | 10 => 237998827219218063212817941251
  | 11 => 81288099584857009617064280851459
  | 12 => 159387197983491536507638055427
  | 13 => 81447173680424309660752327803394
  | _ => 0

def C030_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 60847232447195794506987482579714
  | 1 => 20283647543709546947175166247426
  | 2 => 20282723943328168096035858678529
  | 3 => 60926766467979386608929179042051
  | 4 => 20283652379412970364196735878146
  | 5 => 36893488156009103360
  | 6 => 81289337534341099176247561486848
  | 7 => 60927694932453656232626231443715
  | 8 => 20361948464842678304466765349892
  | 9 => 237993986756751413092389355524
  | 10 => 316915072631207461372903555587
  | 11 => 20600254345015797038180925965058
  | 12 => 79848341478462461235010077188
  | 13 => 40644049787706426416956851879940
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
  | 0 => 1391857120392
  | 1 => 1385297911899
  | 2 => 34528630468
  | 3 => 2302555530257
  | 4 => 293290903297
  | 5 => 1117095297536
  | 6 => 146637375011
  | 7 => 1737736897252
  | 8 => 2208842459428
  | 9 => 2303787648779
  | 10 => 13026501131
  | 11 => 27385731283
  | 12 => 2356870677128
  | 13 => 2233822413834
  | _ => 0

def C031_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 40565751303351439226697368732416
  | 1 => 20362257949907839881747995034369
  | 2 => 159384799021461790965975154946
  | 3 => 40645286533023669508427292540930
  | 4 => 311921788109350229166326275
  | 5 => 40644667562967132769378608742660
  | 6 => 81447793859314504076756244497409
  | 7 => 20520716702195630528070382780673
  | 8 => 40564819226211326706945083179521
  | 9 => 60848467978828246244283018969346
  | 10 => 237998812996850158501781045760
  | 11 => 81289024422498551095234465628418
  | 12 => 158456329750967778617921111044
  | 13 => 81446551083627208128917804155394
  | _ => 0

def C031_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 79849564626505022070233105410
  | 1 => 61085222792971093853558590735362
  | 2 => 81130570501173152778479238119424
  | 3 => 20440868356013464785590818177284
  | 4 => 20283651170468415775113404875776
  | 5 => 1208981448077239340105730
  | 6 => 61164145106697512766614961979904
  | 7 => 81447480747527223884514379038979
  | 8 => 81447793849888001960489303212036
  | 9 => 60927698559231115076513755824388
  | 10 => 60926458191858564008682916478976
  | 11 => 61006618431475831205112081219584
  | 12 => 79848341478462461235010077188
  | 13 => 40644049787706426416956851879940
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

end SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryCaches06
