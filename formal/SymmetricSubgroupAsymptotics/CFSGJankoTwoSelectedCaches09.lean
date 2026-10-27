import SymmetricSubgroupAsymptotics.MatrixKroneckerProductReflection
import Mathlib.Tactic.FinCases

/-! Literal14/F5 selected caches; digit bounds and both pack bindings are independently kernel checked. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedCaches09
open MatrixKroneckerProductReflection MatrixKroneckerDotReflection
open MatrixNaturalRowDotReflection SmallNaturalMatrixProductReflection

def C083_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 1376962815137
  | 1 => 310789940432
  | 2 => 1110838673681
  | 3 => 648811529859
  | 4 => 705503723659
  | 5 => 2373512693259
  | 6 => 1178216177812
  | 7 => 549791565323
  | 8 => 1202660672604
  | 9 => 240594339921
  | 10 => 704379193472
  | 11 => 1884424311488
  | 12 => 1653604451618
  | 13 => 2422418441419
  | _ => 0

def C083_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 61005685140779910708186815987713
  | 1 => 20599322263208873593929644245508
  | 2 => 61165072338633985676582385353474
  | 3 => 40723589871971544922373713035778
  | 4 => 309503899287839497326166530
  | 5 => 238307103284916886590325916674
  | 6 => 20283648762098402435700923367680
  | 7 => 61165072352801156904608900121603
  | 8 => 61005685154946937814428151907329
  | 9 => 567348033749763
  | 10 => 317841105086521669258712318210
  | 11 => 40565750099147697306014108943360
  | 12 => 60848159698021661012671529485316
  | 13 => 81368252566141724471498754883586
  | _ => 0

def C083_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 20599943651061636993141295809538
  | 1 => 159387207428225069590633513984
  | 2 => 20442103868756450309941420425218
  | 3 => 60847851426715582167905894334721
  | 4 => 60927075943507581782677075919361
  | 5 => 60926460600302075529986094400004
  | 6 => 81288713719099730426823027261698
  | 7 => 60926460600302074969217950547969
  | 8 => 81367634805066419916178939183362
  | 9 => 20441180268356697055979211326208
  | 10 => 623805778334001419268522497
  | 11 => 929668714832695653545739011
  | 12 => 40882972215306664168122052771843
  | 13 => 60927387846350451779217324638980
  | _ => 0

def C083_digit (i j : Fin 14) : ℕ := packedDigit 3 (C083_lowColumnCode j) i.val

private theorem C083_bound_00 : ∀ j : Fin 14, C083_digit 0 j < 5 := by decide +kernel

private theorem C083_bound_01 : ∀ j : Fin 14, C083_digit 1 j < 5 := by decide +kernel

private theorem C083_bound_02 : ∀ j : Fin 14, C083_digit 2 j < 5 := by decide +kernel

private theorem C083_bound_03 : ∀ j : Fin 14, C083_digit 3 j < 5 := by decide +kernel

private theorem C083_bound_04 : ∀ j : Fin 14, C083_digit 4 j < 5 := by decide +kernel

private theorem C083_bound_05 : ∀ j : Fin 14, C083_digit 5 j < 5 := by decide +kernel

private theorem C083_bound_06 : ∀ j : Fin 14, C083_digit 6 j < 5 := by decide +kernel

private theorem C083_bound_07 : ∀ j : Fin 14, C083_digit 7 j < 5 := by decide +kernel

private theorem C083_bound_08 : ∀ j : Fin 14, C083_digit 8 j < 5 := by decide +kernel

private theorem C083_bound_09 : ∀ j : Fin 14, C083_digit 9 j < 5 := by decide +kernel

private theorem C083_bound_10 : ∀ j : Fin 14, C083_digit 10 j < 5 := by decide +kernel

private theorem C083_bound_11 : ∀ j : Fin 14, C083_digit 11 j < 5 := by decide +kernel

private theorem C083_bound_12 : ∀ j : Fin 14, C083_digit 12 j < 5 := by decide +kernel

private theorem C083_bound_13 : ∀ j : Fin 14, C083_digit 13 j < 5 := by decide +kernel

theorem C083_bound : ∀ i j : Fin 14, C083_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C083_bound_00 j
  · exact C083_bound_01 j
  · exact C083_bound_02 j
  · exact C083_bound_03 j
  · exact C083_bound_04 j
  · exact C083_bound_05 j
  · exact C083_bound_06 j
  · exact C083_bound_07 j
  · exact C083_bound_08 j
  · exact C083_bound_09 j
  · exact C083_bound_10 j
  · exact C083_bound_11 j
  · exact C083_bound_12 j
  · exact C083_bound_13 j

private theorem C083_row_00 : pack 256 (C083_digit 0)=C083_rowCode 0 := by decide +kernel

private theorem C083_row_01 : pack 256 (C083_digit 1)=C083_rowCode 1 := by decide +kernel

private theorem C083_row_02 : pack 256 (C083_digit 2)=C083_rowCode 2 := by decide +kernel

private theorem C083_row_03 : pack 256 (C083_digit 3)=C083_rowCode 3 := by decide +kernel

private theorem C083_row_04 : pack 256 (C083_digit 4)=C083_rowCode 4 := by decide +kernel

private theorem C083_row_05 : pack 256 (C083_digit 5)=C083_rowCode 5 := by decide +kernel

private theorem C083_row_06 : pack 256 (C083_digit 6)=C083_rowCode 6 := by decide +kernel

private theorem C083_row_07 : pack 256 (C083_digit 7)=C083_rowCode 7 := by decide +kernel

private theorem C083_row_08 : pack 256 (C083_digit 8)=C083_rowCode 8 := by decide +kernel

private theorem C083_row_09 : pack 256 (C083_digit 9)=C083_rowCode 9 := by decide +kernel

private theorem C083_row_10 : pack 256 (C083_digit 10)=C083_rowCode 10 := by decide +kernel

private theorem C083_row_11 : pack 256 (C083_digit 11)=C083_rowCode 11 := by decide +kernel

private theorem C083_row_12 : pack 256 (C083_digit 12)=C083_rowCode 12 := by decide +kernel

private theorem C083_row_13 : pack 256 (C083_digit 13)=C083_rowCode 13 := by decide +kernel

theorem C083_row_binding : ∀ i : Fin 14, pack 256 (C083_digit i)=C083_rowCode i := by
  intro i
  fin_cases i
  · exact C083_row_00
  · exact C083_row_01
  · exact C083_row_02
  · exact C083_row_03
  · exact C083_row_04
  · exact C083_row_05
  · exact C083_row_06
  · exact C083_row_07
  · exact C083_row_08
  · exact C083_row_09
  · exact C083_row_10
  · exact C083_row_11
  · exact C083_row_12
  · exact C083_row_13

private theorem C083_column_00 : reversePack 256 (fun j : Fin 14 => C083_digit j 0)=C083_columnCode 0 := by decide +kernel

private theorem C083_column_01 : reversePack 256 (fun j : Fin 14 => C083_digit j 1)=C083_columnCode 1 := by decide +kernel

private theorem C083_column_02 : reversePack 256 (fun j : Fin 14 => C083_digit j 2)=C083_columnCode 2 := by decide +kernel

private theorem C083_column_03 : reversePack 256 (fun j : Fin 14 => C083_digit j 3)=C083_columnCode 3 := by decide +kernel

private theorem C083_column_04 : reversePack 256 (fun j : Fin 14 => C083_digit j 4)=C083_columnCode 4 := by decide +kernel

private theorem C083_column_05 : reversePack 256 (fun j : Fin 14 => C083_digit j 5)=C083_columnCode 5 := by decide +kernel

private theorem C083_column_06 : reversePack 256 (fun j : Fin 14 => C083_digit j 6)=C083_columnCode 6 := by decide +kernel

private theorem C083_column_07 : reversePack 256 (fun j : Fin 14 => C083_digit j 7)=C083_columnCode 7 := by decide +kernel

private theorem C083_column_08 : reversePack 256 (fun j : Fin 14 => C083_digit j 8)=C083_columnCode 8 := by decide +kernel

private theorem C083_column_09 : reversePack 256 (fun j : Fin 14 => C083_digit j 9)=C083_columnCode 9 := by decide +kernel

private theorem C083_column_10 : reversePack 256 (fun j : Fin 14 => C083_digit j 10)=C083_columnCode 10 := by decide +kernel

private theorem C083_column_11 : reversePack 256 (fun j : Fin 14 => C083_digit j 11)=C083_columnCode 11 := by decide +kernel

private theorem C083_column_12 : reversePack 256 (fun j : Fin 14 => C083_digit j 12)=C083_columnCode 12 := by decide +kernel

private theorem C083_column_13 : reversePack 256 (fun j : Fin 14 => C083_digit j 13)=C083_columnCode 13 := by decide +kernel

theorem C083_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C083_digit j i)=C083_columnCode i := by
  intro i
  fin_cases i
  · exact C083_column_00
  · exact C083_column_01
  · exact C083_column_02
  · exact C083_column_03
  · exact C083_column_04
  · exact C083_column_05
  · exact C083_column_06
  · exact C083_column_07
  · exact C083_column_08
  · exact C083_column_09
  · exact C083_column_10
  · exact C083_column_11
  · exact C083_column_12
  · exact C083_column_13

def C083_data : PackedData 14 5 256 where
  raw := C083_digit
  digit_lt := C083_bound
  rowCode := C083_rowCode
  columnCode := C083_columnCode
  row_binding := C083_row_binding
  column_binding := C083_column_binding

def C084_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 1954770134276
  | 1 => 853966735555
  | 2 => 700641818403
  | 3 => 2435286958306
  | 4 => 286999561760
  | 5 => 1202660672604
  | 6 => 2373512693259
  | 7 => 704379193472
  | 8 => 1178216177812
  | 9 => 549791565323
  | 10 => 240594339921
  | 11 => 2422418441419
  | 12 => 1884424311488
  | 13 => 1653604451618
  | _ => 0

def C084_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 40565748885499511771456635863812
  | 1 => 81129950322227402525923902488576
  | 2 => 81368252566141795962840043225860
  | 3 => 40644671189707914859764120749058
  | 4 => 79232998254436284274841945090
  | 5 => 61005689985854134874673007232002
  | 6 => 317224552955483472641763835904
  | 7 => 81368256197623175389965613007619
  | 8 => 40565752507536156543984464888833
  | 9 => 36894614055916143108
  | 10 => 81367322902167922015606252241668
  | 11 => 238308293284306150998864364291
  | 12 => 238616569368307315202811102212
  | 13 => 61086151243296422821607384350979
  | _ => 0

def C084_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 81130878781979233604750652146691
  | 1 => 60848162120651007522169663194113
  | 2 => 61165383042051253654225082712577
  | 3 => 40882660312463794171581787472644
  | 4 => 316916295779323486068979860480
  | 5 => 81367634805066419916178939183362
  | 6 => 60926460600302075529986094400004
  | 7 => 623805778334001419268522497
  | 8 => 81288713719099730426823027261698
  | 9 => 60926460600302074969217950547969
  | 10 => 20441180268356697055979211326208
  | 11 => 60927387846350451779217324638980
  | 12 => 929668714832695653545739011
  | 13 => 40882972215306664168122052771843
  | _ => 0

def C084_digit (i j : Fin 14) : ℕ := packedDigit 3 (C084_lowColumnCode j) i.val

private theorem C084_bound_00 : ∀ j : Fin 14, C084_digit 0 j < 5 := by decide +kernel

private theorem C084_bound_01 : ∀ j : Fin 14, C084_digit 1 j < 5 := by decide +kernel

private theorem C084_bound_02 : ∀ j : Fin 14, C084_digit 2 j < 5 := by decide +kernel

private theorem C084_bound_03 : ∀ j : Fin 14, C084_digit 3 j < 5 := by decide +kernel

private theorem C084_bound_04 : ∀ j : Fin 14, C084_digit 4 j < 5 := by decide +kernel

private theorem C084_bound_05 : ∀ j : Fin 14, C084_digit 5 j < 5 := by decide +kernel

private theorem C084_bound_06 : ∀ j : Fin 14, C084_digit 6 j < 5 := by decide +kernel

private theorem C084_bound_07 : ∀ j : Fin 14, C084_digit 7 j < 5 := by decide +kernel

private theorem C084_bound_08 : ∀ j : Fin 14, C084_digit 8 j < 5 := by decide +kernel

private theorem C084_bound_09 : ∀ j : Fin 14, C084_digit 9 j < 5 := by decide +kernel

private theorem C084_bound_10 : ∀ j : Fin 14, C084_digit 10 j < 5 := by decide +kernel

private theorem C084_bound_11 : ∀ j : Fin 14, C084_digit 11 j < 5 := by decide +kernel

private theorem C084_bound_12 : ∀ j : Fin 14, C084_digit 12 j < 5 := by decide +kernel

private theorem C084_bound_13 : ∀ j : Fin 14, C084_digit 13 j < 5 := by decide +kernel

theorem C084_bound : ∀ i j : Fin 14, C084_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C084_bound_00 j
  · exact C084_bound_01 j
  · exact C084_bound_02 j
  · exact C084_bound_03 j
  · exact C084_bound_04 j
  · exact C084_bound_05 j
  · exact C084_bound_06 j
  · exact C084_bound_07 j
  · exact C084_bound_08 j
  · exact C084_bound_09 j
  · exact C084_bound_10 j
  · exact C084_bound_11 j
  · exact C084_bound_12 j
  · exact C084_bound_13 j

private theorem C084_row_00 : pack 256 (C084_digit 0)=C084_rowCode 0 := by decide +kernel

private theorem C084_row_01 : pack 256 (C084_digit 1)=C084_rowCode 1 := by decide +kernel

private theorem C084_row_02 : pack 256 (C084_digit 2)=C084_rowCode 2 := by decide +kernel

private theorem C084_row_03 : pack 256 (C084_digit 3)=C084_rowCode 3 := by decide +kernel

private theorem C084_row_04 : pack 256 (C084_digit 4)=C084_rowCode 4 := by decide +kernel

private theorem C084_row_05 : pack 256 (C084_digit 5)=C084_rowCode 5 := by decide +kernel

private theorem C084_row_06 : pack 256 (C084_digit 6)=C084_rowCode 6 := by decide +kernel

private theorem C084_row_07 : pack 256 (C084_digit 7)=C084_rowCode 7 := by decide +kernel

private theorem C084_row_08 : pack 256 (C084_digit 8)=C084_rowCode 8 := by decide +kernel

private theorem C084_row_09 : pack 256 (C084_digit 9)=C084_rowCode 9 := by decide +kernel

private theorem C084_row_10 : pack 256 (C084_digit 10)=C084_rowCode 10 := by decide +kernel

private theorem C084_row_11 : pack 256 (C084_digit 11)=C084_rowCode 11 := by decide +kernel

private theorem C084_row_12 : pack 256 (C084_digit 12)=C084_rowCode 12 := by decide +kernel

private theorem C084_row_13 : pack 256 (C084_digit 13)=C084_rowCode 13 := by decide +kernel

theorem C084_row_binding : ∀ i : Fin 14, pack 256 (C084_digit i)=C084_rowCode i := by
  intro i
  fin_cases i
  · exact C084_row_00
  · exact C084_row_01
  · exact C084_row_02
  · exact C084_row_03
  · exact C084_row_04
  · exact C084_row_05
  · exact C084_row_06
  · exact C084_row_07
  · exact C084_row_08
  · exact C084_row_09
  · exact C084_row_10
  · exact C084_row_11
  · exact C084_row_12
  · exact C084_row_13

private theorem C084_column_00 : reversePack 256 (fun j : Fin 14 => C084_digit j 0)=C084_columnCode 0 := by decide +kernel

private theorem C084_column_01 : reversePack 256 (fun j : Fin 14 => C084_digit j 1)=C084_columnCode 1 := by decide +kernel

private theorem C084_column_02 : reversePack 256 (fun j : Fin 14 => C084_digit j 2)=C084_columnCode 2 := by decide +kernel

private theorem C084_column_03 : reversePack 256 (fun j : Fin 14 => C084_digit j 3)=C084_columnCode 3 := by decide +kernel

private theorem C084_column_04 : reversePack 256 (fun j : Fin 14 => C084_digit j 4)=C084_columnCode 4 := by decide +kernel

private theorem C084_column_05 : reversePack 256 (fun j : Fin 14 => C084_digit j 5)=C084_columnCode 5 := by decide +kernel

private theorem C084_column_06 : reversePack 256 (fun j : Fin 14 => C084_digit j 6)=C084_columnCode 6 := by decide +kernel

private theorem C084_column_07 : reversePack 256 (fun j : Fin 14 => C084_digit j 7)=C084_columnCode 7 := by decide +kernel

private theorem C084_column_08 : reversePack 256 (fun j : Fin 14 => C084_digit j 8)=C084_columnCode 8 := by decide +kernel

private theorem C084_column_09 : reversePack 256 (fun j : Fin 14 => C084_digit j 9)=C084_columnCode 9 := by decide +kernel

private theorem C084_column_10 : reversePack 256 (fun j : Fin 14 => C084_digit j 10)=C084_columnCode 10 := by decide +kernel

private theorem C084_column_11 : reversePack 256 (fun j : Fin 14 => C084_digit j 11)=C084_columnCode 11 := by decide +kernel

private theorem C084_column_12 : reversePack 256 (fun j : Fin 14 => C084_digit j 12)=C084_columnCode 12 := by decide +kernel

private theorem C084_column_13 : reversePack 256 (fun j : Fin 14 => C084_digit j 13)=C084_columnCode 13 := by decide +kernel

theorem C084_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C084_digit j i)=C084_columnCode i := by
  intro i
  fin_cases i
  · exact C084_column_00
  · exact C084_column_01
  · exact C084_column_02
  · exact C084_column_03
  · exact C084_column_04
  · exact C084_column_05
  · exact C084_column_06
  · exact C084_column_07
  · exact C084_column_08
  · exact C084_column_09
  · exact C084_column_10
  · exact C084_column_11
  · exact C084_column_12
  · exact C084_column_13

def C084_data : PackedData 14 5 256 where
  raw := C084_digit
  digit_lt := C084_bound
  rowCode := C084_rowCode
  columnCode := C084_columnCode
  row_binding := C084_row_binding
  column_binding := C084_column_binding

def C085_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 696900518411
  | 1 => 1324998493728
  | 2 => 1410972296290
  | 3 => 2499705382626
  | 4 => 1240180236544
  | 5 => 206446272660
  | 6 => 81607406656
  | 7 => 209925775435
  | 8 => 3259073233
  | 9 => 2510832842824
  | 10 => 70866964480
  | 11 => 2210873094940
  | 12 => 1884424311488
  | 13 => 1653604451618
  | _ => 0

def C085_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 40566057147361289149423305228291
  | 1 => 81130566874395477761805372359681
  | 2 => 81368560846966539145220578148352
  | 3 => 40644356873735339769059065594625
  | 4 => 80157840636792397858481504256
  | 5 => 61006923080800677283486826037508
  | 6 => 317841119253837853595403289600
  | 7 => 81367941881651032365561616269316
  | 8 => 40565438182082243510148561895426
  | 9 => 14167387681184110608384
  | 10 => 81368253784530868469689485492737
  | 11 => 237993991442080570802964791809
  | 12 => 237685715358295016452670096130
  | 13 => 61086151257426555596384522863105
  | _ => 0

def C085_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 60926458182468883328458257662465
  | 1 => 316916276853251168711594869506
  | 2 => 40882043769685039612706739717122
  | 3 => 40882663948649163706230223602692
  | 4 => 1237949502466215987856278018
  | 5 => 81288713719099730424623987163904
  | 6 => 311917102563453488005710080
  | 7 => 60926766467960940707089982948096
  | 8 => 20441795592690823546339843899392
  | 9 => 79542497413127070706110301188
  | 10 => 4722366482869678768384
  | 11 => 81368562065355682866308625530884
  | 12 => 929668714832695653545739011
  | 13 => 40882972215306664168122052771843
  | _ => 0

def C085_digit (i j : Fin 14) : ℕ := packedDigit 3 (C085_lowColumnCode j) i.val

private theorem C085_bound_00 : ∀ j : Fin 14, C085_digit 0 j < 5 := by decide +kernel

private theorem C085_bound_01 : ∀ j : Fin 14, C085_digit 1 j < 5 := by decide +kernel

private theorem C085_bound_02 : ∀ j : Fin 14, C085_digit 2 j < 5 := by decide +kernel

private theorem C085_bound_03 : ∀ j : Fin 14, C085_digit 3 j < 5 := by decide +kernel

private theorem C085_bound_04 : ∀ j : Fin 14, C085_digit 4 j < 5 := by decide +kernel

private theorem C085_bound_05 : ∀ j : Fin 14, C085_digit 5 j < 5 := by decide +kernel

private theorem C085_bound_06 : ∀ j : Fin 14, C085_digit 6 j < 5 := by decide +kernel

private theorem C085_bound_07 : ∀ j : Fin 14, C085_digit 7 j < 5 := by decide +kernel

private theorem C085_bound_08 : ∀ j : Fin 14, C085_digit 8 j < 5 := by decide +kernel

private theorem C085_bound_09 : ∀ j : Fin 14, C085_digit 9 j < 5 := by decide +kernel

private theorem C085_bound_10 : ∀ j : Fin 14, C085_digit 10 j < 5 := by decide +kernel

private theorem C085_bound_11 : ∀ j : Fin 14, C085_digit 11 j < 5 := by decide +kernel

private theorem C085_bound_12 : ∀ j : Fin 14, C085_digit 12 j < 5 := by decide +kernel

private theorem C085_bound_13 : ∀ j : Fin 14, C085_digit 13 j < 5 := by decide +kernel

theorem C085_bound : ∀ i j : Fin 14, C085_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C085_bound_00 j
  · exact C085_bound_01 j
  · exact C085_bound_02 j
  · exact C085_bound_03 j
  · exact C085_bound_04 j
  · exact C085_bound_05 j
  · exact C085_bound_06 j
  · exact C085_bound_07 j
  · exact C085_bound_08 j
  · exact C085_bound_09 j
  · exact C085_bound_10 j
  · exact C085_bound_11 j
  · exact C085_bound_12 j
  · exact C085_bound_13 j

private theorem C085_row_00 : pack 256 (C085_digit 0)=C085_rowCode 0 := by decide +kernel

private theorem C085_row_01 : pack 256 (C085_digit 1)=C085_rowCode 1 := by decide +kernel

private theorem C085_row_02 : pack 256 (C085_digit 2)=C085_rowCode 2 := by decide +kernel

private theorem C085_row_03 : pack 256 (C085_digit 3)=C085_rowCode 3 := by decide +kernel

private theorem C085_row_04 : pack 256 (C085_digit 4)=C085_rowCode 4 := by decide +kernel

private theorem C085_row_05 : pack 256 (C085_digit 5)=C085_rowCode 5 := by decide +kernel

private theorem C085_row_06 : pack 256 (C085_digit 6)=C085_rowCode 6 := by decide +kernel

private theorem C085_row_07 : pack 256 (C085_digit 7)=C085_rowCode 7 := by decide +kernel

private theorem C085_row_08 : pack 256 (C085_digit 8)=C085_rowCode 8 := by decide +kernel

private theorem C085_row_09 : pack 256 (C085_digit 9)=C085_rowCode 9 := by decide +kernel

private theorem C085_row_10 : pack 256 (C085_digit 10)=C085_rowCode 10 := by decide +kernel

private theorem C085_row_11 : pack 256 (C085_digit 11)=C085_rowCode 11 := by decide +kernel

private theorem C085_row_12 : pack 256 (C085_digit 12)=C085_rowCode 12 := by decide +kernel

private theorem C085_row_13 : pack 256 (C085_digit 13)=C085_rowCode 13 := by decide +kernel

theorem C085_row_binding : ∀ i : Fin 14, pack 256 (C085_digit i)=C085_rowCode i := by
  intro i
  fin_cases i
  · exact C085_row_00
  · exact C085_row_01
  · exact C085_row_02
  · exact C085_row_03
  · exact C085_row_04
  · exact C085_row_05
  · exact C085_row_06
  · exact C085_row_07
  · exact C085_row_08
  · exact C085_row_09
  · exact C085_row_10
  · exact C085_row_11
  · exact C085_row_12
  · exact C085_row_13

private theorem C085_column_00 : reversePack 256 (fun j : Fin 14 => C085_digit j 0)=C085_columnCode 0 := by decide +kernel

private theorem C085_column_01 : reversePack 256 (fun j : Fin 14 => C085_digit j 1)=C085_columnCode 1 := by decide +kernel

private theorem C085_column_02 : reversePack 256 (fun j : Fin 14 => C085_digit j 2)=C085_columnCode 2 := by decide +kernel

private theorem C085_column_03 : reversePack 256 (fun j : Fin 14 => C085_digit j 3)=C085_columnCode 3 := by decide +kernel

private theorem C085_column_04 : reversePack 256 (fun j : Fin 14 => C085_digit j 4)=C085_columnCode 4 := by decide +kernel

private theorem C085_column_05 : reversePack 256 (fun j : Fin 14 => C085_digit j 5)=C085_columnCode 5 := by decide +kernel

private theorem C085_column_06 : reversePack 256 (fun j : Fin 14 => C085_digit j 6)=C085_columnCode 6 := by decide +kernel

private theorem C085_column_07 : reversePack 256 (fun j : Fin 14 => C085_digit j 7)=C085_columnCode 7 := by decide +kernel

private theorem C085_column_08 : reversePack 256 (fun j : Fin 14 => C085_digit j 8)=C085_columnCode 8 := by decide +kernel

private theorem C085_column_09 : reversePack 256 (fun j : Fin 14 => C085_digit j 9)=C085_columnCode 9 := by decide +kernel

private theorem C085_column_10 : reversePack 256 (fun j : Fin 14 => C085_digit j 10)=C085_columnCode 10 := by decide +kernel

private theorem C085_column_11 : reversePack 256 (fun j : Fin 14 => C085_digit j 11)=C085_columnCode 11 := by decide +kernel

private theorem C085_column_12 : reversePack 256 (fun j : Fin 14 => C085_digit j 12)=C085_columnCode 12 := by decide +kernel

private theorem C085_column_13 : reversePack 256 (fun j : Fin 14 => C085_digit j 13)=C085_columnCode 13 := by decide +kernel

theorem C085_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C085_digit j i)=C085_columnCode i := by
  intro i
  fin_cases i
  · exact C085_column_00
  · exact C085_column_01
  · exact C085_column_02
  · exact C085_column_03
  · exact C085_column_04
  · exact C085_column_05
  · exact C085_column_06
  · exact C085_column_07
  · exact C085_column_08
  · exact C085_column_09
  · exact C085_column_10
  · exact C085_column_11
  · exact C085_column_12
  · exact C085_column_13

def C085_data : PackedData 14 5 256 where
  raw := C085_digit
  digit_lt := C085_bound
  rowCode := C085_rowCode
  columnCode := C085_columnCode
  row_binding := C085_row_binding
  column_binding := C085_column_binding

def C086_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 300667646723
  | 1 => 1856523618403
  | 2 => 2510482416132
  | 3 => 1857575596096
  | 4 => 1264904341282
  | 5 => 3259073233
  | 6 => 206446272660
  | 7 => 70866964480
  | 8 => 81607406656
  | 9 => 209925775435
  | 10 => 2510832842824
  | 11 => 1653604451618
  | 12 => 2210873094940
  | 13 => 1884424311488
  | _ => 0

def C086_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 317531634243800616128569672451
  | 1 => 238923641230265055720507442176
  | 2 => 61165380614717987410329043206404
  | 3 => 20362261571925749399454759322625
  | 4 => 20520097727472068099119868150787
  | 5 => 40882661530834201793441053213696
  | 6 => 81367326543149373796250063864580
  | 7 => 61006925512782377515792692609793
  | 8 => 159076503973991263636302332161
  | 9 => 3645666925338316058394624
  | 10 => 61086153670629759437554642452736
  | 11 => 60926461809191000812038591348739
  | 12 => 60847233660843908825068706464516
  | 13 => 61165074751744811115947443356416
  | _ => 0

def C086_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 60848467974087504228305403577344
  | 1 => 61164455800688638351881344647939
  | 2 => 81129639633032719472389685249028
  | 3 => 309499250708051447508894467
  | 4 => 40882973424195805622960958669314
  | 5 => 20441795592690823546339843899392
  | 6 => 81288713719099730424623987163904
  | 7 => 4722366482869678768384
  | 8 => 311917102563453488005710080
  | 9 => 60926766467960940707089982948096
  | 10 => 79542497413127070706110301188
  | 11 => 40882972215306664168122052771843
  | 12 => 81368562065355682866308625530884
  | 13 => 929668714832695653545739011
  | _ => 0

def C086_digit (i j : Fin 14) : ℕ := packedDigit 3 (C086_lowColumnCode j) i.val

private theorem C086_bound_00 : ∀ j : Fin 14, C086_digit 0 j < 5 := by decide +kernel

private theorem C086_bound_01 : ∀ j : Fin 14, C086_digit 1 j < 5 := by decide +kernel

private theorem C086_bound_02 : ∀ j : Fin 14, C086_digit 2 j < 5 := by decide +kernel

private theorem C086_bound_03 : ∀ j : Fin 14, C086_digit 3 j < 5 := by decide +kernel

private theorem C086_bound_04 : ∀ j : Fin 14, C086_digit 4 j < 5 := by decide +kernel

private theorem C086_bound_05 : ∀ j : Fin 14, C086_digit 5 j < 5 := by decide +kernel

private theorem C086_bound_06 : ∀ j : Fin 14, C086_digit 6 j < 5 := by decide +kernel

private theorem C086_bound_07 : ∀ j : Fin 14, C086_digit 7 j < 5 := by decide +kernel

private theorem C086_bound_08 : ∀ j : Fin 14, C086_digit 8 j < 5 := by decide +kernel

private theorem C086_bound_09 : ∀ j : Fin 14, C086_digit 9 j < 5 := by decide +kernel

private theorem C086_bound_10 : ∀ j : Fin 14, C086_digit 10 j < 5 := by decide +kernel

private theorem C086_bound_11 : ∀ j : Fin 14, C086_digit 11 j < 5 := by decide +kernel

private theorem C086_bound_12 : ∀ j : Fin 14, C086_digit 12 j < 5 := by decide +kernel

private theorem C086_bound_13 : ∀ j : Fin 14, C086_digit 13 j < 5 := by decide +kernel

theorem C086_bound : ∀ i j : Fin 14, C086_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C086_bound_00 j
  · exact C086_bound_01 j
  · exact C086_bound_02 j
  · exact C086_bound_03 j
  · exact C086_bound_04 j
  · exact C086_bound_05 j
  · exact C086_bound_06 j
  · exact C086_bound_07 j
  · exact C086_bound_08 j
  · exact C086_bound_09 j
  · exact C086_bound_10 j
  · exact C086_bound_11 j
  · exact C086_bound_12 j
  · exact C086_bound_13 j

private theorem C086_row_00 : pack 256 (C086_digit 0)=C086_rowCode 0 := by decide +kernel

private theorem C086_row_01 : pack 256 (C086_digit 1)=C086_rowCode 1 := by decide +kernel

private theorem C086_row_02 : pack 256 (C086_digit 2)=C086_rowCode 2 := by decide +kernel

private theorem C086_row_03 : pack 256 (C086_digit 3)=C086_rowCode 3 := by decide +kernel

private theorem C086_row_04 : pack 256 (C086_digit 4)=C086_rowCode 4 := by decide +kernel

private theorem C086_row_05 : pack 256 (C086_digit 5)=C086_rowCode 5 := by decide +kernel

private theorem C086_row_06 : pack 256 (C086_digit 6)=C086_rowCode 6 := by decide +kernel

private theorem C086_row_07 : pack 256 (C086_digit 7)=C086_rowCode 7 := by decide +kernel

private theorem C086_row_08 : pack 256 (C086_digit 8)=C086_rowCode 8 := by decide +kernel

private theorem C086_row_09 : pack 256 (C086_digit 9)=C086_rowCode 9 := by decide +kernel

private theorem C086_row_10 : pack 256 (C086_digit 10)=C086_rowCode 10 := by decide +kernel

private theorem C086_row_11 : pack 256 (C086_digit 11)=C086_rowCode 11 := by decide +kernel

private theorem C086_row_12 : pack 256 (C086_digit 12)=C086_rowCode 12 := by decide +kernel

private theorem C086_row_13 : pack 256 (C086_digit 13)=C086_rowCode 13 := by decide +kernel

theorem C086_row_binding : ∀ i : Fin 14, pack 256 (C086_digit i)=C086_rowCode i := by
  intro i
  fin_cases i
  · exact C086_row_00
  · exact C086_row_01
  · exact C086_row_02
  · exact C086_row_03
  · exact C086_row_04
  · exact C086_row_05
  · exact C086_row_06
  · exact C086_row_07
  · exact C086_row_08
  · exact C086_row_09
  · exact C086_row_10
  · exact C086_row_11
  · exact C086_row_12
  · exact C086_row_13

private theorem C086_column_00 : reversePack 256 (fun j : Fin 14 => C086_digit j 0)=C086_columnCode 0 := by decide +kernel

private theorem C086_column_01 : reversePack 256 (fun j : Fin 14 => C086_digit j 1)=C086_columnCode 1 := by decide +kernel

private theorem C086_column_02 : reversePack 256 (fun j : Fin 14 => C086_digit j 2)=C086_columnCode 2 := by decide +kernel

private theorem C086_column_03 : reversePack 256 (fun j : Fin 14 => C086_digit j 3)=C086_columnCode 3 := by decide +kernel

private theorem C086_column_04 : reversePack 256 (fun j : Fin 14 => C086_digit j 4)=C086_columnCode 4 := by decide +kernel

private theorem C086_column_05 : reversePack 256 (fun j : Fin 14 => C086_digit j 5)=C086_columnCode 5 := by decide +kernel

private theorem C086_column_06 : reversePack 256 (fun j : Fin 14 => C086_digit j 6)=C086_columnCode 6 := by decide +kernel

private theorem C086_column_07 : reversePack 256 (fun j : Fin 14 => C086_digit j 7)=C086_columnCode 7 := by decide +kernel

private theorem C086_column_08 : reversePack 256 (fun j : Fin 14 => C086_digit j 8)=C086_columnCode 8 := by decide +kernel

private theorem C086_column_09 : reversePack 256 (fun j : Fin 14 => C086_digit j 9)=C086_columnCode 9 := by decide +kernel

private theorem C086_column_10 : reversePack 256 (fun j : Fin 14 => C086_digit j 10)=C086_columnCode 10 := by decide +kernel

private theorem C086_column_11 : reversePack 256 (fun j : Fin 14 => C086_digit j 11)=C086_columnCode 11 := by decide +kernel

private theorem C086_column_12 : reversePack 256 (fun j : Fin 14 => C086_digit j 12)=C086_columnCode 12 := by decide +kernel

private theorem C086_column_13 : reversePack 256 (fun j : Fin 14 => C086_digit j 13)=C086_columnCode 13 := by decide +kernel

theorem C086_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C086_digit j i)=C086_columnCode i := by
  intro i
  fin_cases i
  · exact C086_column_00
  · exact C086_column_01
  · exact C086_column_02
  · exact C086_column_03
  · exact C086_column_04
  · exact C086_column_05
  · exact C086_column_06
  · exact C086_column_07
  · exact C086_column_08
  · exact C086_column_09
  · exact C086_column_10
  · exact C086_column_11
  · exact C086_column_12
  · exact C086_column_13

def C086_data : PackedData 14 5 256 where
  raw := C086_digit
  digit_lt := C086_bound
  rowCode := C086_rowCode
  columnCode := C086_columnCode
  row_binding := C086_row_binding
  column_binding := C086_column_binding

def C087_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 86202224652
  | 1 => 699144347779
  | 2 => 78721462370
  | 3 => 2225867985633
  | 4 => 1386218340892
  | 5 => 225542477468
  | 6 => 1195094640290
  | 7 => 1873948816410
  | 8 => 767863882786
  | 9 => 551903313920
  | 10 => 240594339921
  | 11 => 1169779082521
  | 12 => 2210873094940
  | 13 => 1884424311488
  | _ => 0

def C087_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 317223344029736480772766958340
  | 1 => 238615360497900555533501595649
  | 2 => 61165380609977174182269030564352
  | 3 => 20362261571925894361258215342080
  | 4 => 20521336885826709380896884195841
  | 5 => 40881736693100786882872544067587
  | 6 => 81367634805011152581591683956739
  | 7 => 61006308941743354868603920908800
  | 8 => 159699100771092798756492673026
  | 9 => 928455048054894467959881986
  | 10 => 61085222793007771168932469211904
  | 11 => 60926461809191145773842080792834
  | 12 => 60847541922797848150591936725505
  | 13 => 61164760435772741275037458235648
  | _ => 0

def C087_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 81208866581898868923463050068224
  | 1 => 60847847790419387490672792633857
  | 2 => 40882041356611250369310882857216
  | 3 => 20600251922460453113697428242436
  | 4 => 81367324130001869916706487469058
  | 5 => 81367945503705837061335173694208
  | 6 => 40882354454194681733391728181506
  | 7 => 40802506126920428943554268758787
  | 8 => 40881734275248931478628745675521
  | 9 => 18889465931478614409217
  | 10 => 20441180268356697055979211326208
  | 11 => 20521334467974926602694652068098
  | 12 => 81368562065355682866308625530884
  | 13 => 929668714832695653545739011
  | _ => 0

def C087_digit (i j : Fin 14) : ℕ := packedDigit 3 (C087_lowColumnCode j) i.val

private theorem C087_bound_00 : ∀ j : Fin 14, C087_digit 0 j < 5 := by decide +kernel

private theorem C087_bound_01 : ∀ j : Fin 14, C087_digit 1 j < 5 := by decide +kernel

private theorem C087_bound_02 : ∀ j : Fin 14, C087_digit 2 j < 5 := by decide +kernel

private theorem C087_bound_03 : ∀ j : Fin 14, C087_digit 3 j < 5 := by decide +kernel

private theorem C087_bound_04 : ∀ j : Fin 14, C087_digit 4 j < 5 := by decide +kernel

private theorem C087_bound_05 : ∀ j : Fin 14, C087_digit 5 j < 5 := by decide +kernel

private theorem C087_bound_06 : ∀ j : Fin 14, C087_digit 6 j < 5 := by decide +kernel

private theorem C087_bound_07 : ∀ j : Fin 14, C087_digit 7 j < 5 := by decide +kernel

private theorem C087_bound_08 : ∀ j : Fin 14, C087_digit 8 j < 5 := by decide +kernel

private theorem C087_bound_09 : ∀ j : Fin 14, C087_digit 9 j < 5 := by decide +kernel

private theorem C087_bound_10 : ∀ j : Fin 14, C087_digit 10 j < 5 := by decide +kernel

private theorem C087_bound_11 : ∀ j : Fin 14, C087_digit 11 j < 5 := by decide +kernel

private theorem C087_bound_12 : ∀ j : Fin 14, C087_digit 12 j < 5 := by decide +kernel

private theorem C087_bound_13 : ∀ j : Fin 14, C087_digit 13 j < 5 := by decide +kernel

theorem C087_bound : ∀ i j : Fin 14, C087_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C087_bound_00 j
  · exact C087_bound_01 j
  · exact C087_bound_02 j
  · exact C087_bound_03 j
  · exact C087_bound_04 j
  · exact C087_bound_05 j
  · exact C087_bound_06 j
  · exact C087_bound_07 j
  · exact C087_bound_08 j
  · exact C087_bound_09 j
  · exact C087_bound_10 j
  · exact C087_bound_11 j
  · exact C087_bound_12 j
  · exact C087_bound_13 j

private theorem C087_row_00 : pack 256 (C087_digit 0)=C087_rowCode 0 := by decide +kernel

private theorem C087_row_01 : pack 256 (C087_digit 1)=C087_rowCode 1 := by decide +kernel

private theorem C087_row_02 : pack 256 (C087_digit 2)=C087_rowCode 2 := by decide +kernel

private theorem C087_row_03 : pack 256 (C087_digit 3)=C087_rowCode 3 := by decide +kernel

private theorem C087_row_04 : pack 256 (C087_digit 4)=C087_rowCode 4 := by decide +kernel

private theorem C087_row_05 : pack 256 (C087_digit 5)=C087_rowCode 5 := by decide +kernel

private theorem C087_row_06 : pack 256 (C087_digit 6)=C087_rowCode 6 := by decide +kernel

private theorem C087_row_07 : pack 256 (C087_digit 7)=C087_rowCode 7 := by decide +kernel

private theorem C087_row_08 : pack 256 (C087_digit 8)=C087_rowCode 8 := by decide +kernel

private theorem C087_row_09 : pack 256 (C087_digit 9)=C087_rowCode 9 := by decide +kernel

private theorem C087_row_10 : pack 256 (C087_digit 10)=C087_rowCode 10 := by decide +kernel

private theorem C087_row_11 : pack 256 (C087_digit 11)=C087_rowCode 11 := by decide +kernel

private theorem C087_row_12 : pack 256 (C087_digit 12)=C087_rowCode 12 := by decide +kernel

private theorem C087_row_13 : pack 256 (C087_digit 13)=C087_rowCode 13 := by decide +kernel

theorem C087_row_binding : ∀ i : Fin 14, pack 256 (C087_digit i)=C087_rowCode i := by
  intro i
  fin_cases i
  · exact C087_row_00
  · exact C087_row_01
  · exact C087_row_02
  · exact C087_row_03
  · exact C087_row_04
  · exact C087_row_05
  · exact C087_row_06
  · exact C087_row_07
  · exact C087_row_08
  · exact C087_row_09
  · exact C087_row_10
  · exact C087_row_11
  · exact C087_row_12
  · exact C087_row_13

private theorem C087_column_00 : reversePack 256 (fun j : Fin 14 => C087_digit j 0)=C087_columnCode 0 := by decide +kernel

private theorem C087_column_01 : reversePack 256 (fun j : Fin 14 => C087_digit j 1)=C087_columnCode 1 := by decide +kernel

private theorem C087_column_02 : reversePack 256 (fun j : Fin 14 => C087_digit j 2)=C087_columnCode 2 := by decide +kernel

private theorem C087_column_03 : reversePack 256 (fun j : Fin 14 => C087_digit j 3)=C087_columnCode 3 := by decide +kernel

private theorem C087_column_04 : reversePack 256 (fun j : Fin 14 => C087_digit j 4)=C087_columnCode 4 := by decide +kernel

private theorem C087_column_05 : reversePack 256 (fun j : Fin 14 => C087_digit j 5)=C087_columnCode 5 := by decide +kernel

private theorem C087_column_06 : reversePack 256 (fun j : Fin 14 => C087_digit j 6)=C087_columnCode 6 := by decide +kernel

private theorem C087_column_07 : reversePack 256 (fun j : Fin 14 => C087_digit j 7)=C087_columnCode 7 := by decide +kernel

private theorem C087_column_08 : reversePack 256 (fun j : Fin 14 => C087_digit j 8)=C087_columnCode 8 := by decide +kernel

private theorem C087_column_09 : reversePack 256 (fun j : Fin 14 => C087_digit j 9)=C087_columnCode 9 := by decide +kernel

private theorem C087_column_10 : reversePack 256 (fun j : Fin 14 => C087_digit j 10)=C087_columnCode 10 := by decide +kernel

private theorem C087_column_11 : reversePack 256 (fun j : Fin 14 => C087_digit j 11)=C087_columnCode 11 := by decide +kernel

private theorem C087_column_12 : reversePack 256 (fun j : Fin 14 => C087_digit j 12)=C087_columnCode 12 := by decide +kernel

private theorem C087_column_13 : reversePack 256 (fun j : Fin 14 => C087_digit j 13)=C087_columnCode 13 := by decide +kernel

theorem C087_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C087_digit j i)=C087_columnCode i := by
  intro i
  fin_cases i
  · exact C087_column_00
  · exact C087_column_01
  · exact C087_column_02
  · exact C087_column_03
  · exact C087_column_04
  · exact C087_column_05
  · exact C087_column_06
  · exact C087_column_07
  · exact C087_column_08
  · exact C087_column_09
  · exact C087_column_10
  · exact C087_column_11
  · exact C087_column_12
  · exact C087_column_13

def C087_data : PackedData 14 5 256 where
  raw := C087_digit
  digit_lt := C087_bound
  rowCode := C087_rowCode
  columnCode := C087_columnCode
  row_binding := C087_row_binding
  column_binding := C087_column_binding

def C088_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 2434752610584
  | 1 => 1745423058506
  | 2 => 1659220833859
  | 3 => 1952080572579
  | 4 => 571230963852
  | 5 => 1195094640290
  | 6 => 767863882786
  | 7 => 551903313920
  | 8 => 225542477468
  | 9 => 240594339921
  | 10 => 1873948816410
  | 11 => 2210873094940
  | 12 => 1884424311488
  | 13 => 1169779082521
  | _ => 0

def C088_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 20283649966338749057811190317568
  | 1 => 60848160902262008479198186832131
  | 2 => 81368560846948020062069247246596
  | 3 => 40644359291623872489780498596608
  | 4 => 81209798677836069818421920072704
  | 5 => 159697910771632884128833143809
  | 6 => 20600254344960383623556824630276
  | 7 => 40803122683810583278561758675460
  | 8 => 81130257403571130550725692687106
  | 9 => 60847231228806650782575080113156
  | 10 => 20521023755186785535440382394627
  | 11 => 237996409330613291515857928963
  | 12 => 20520097732194362806969980420355
  | 13 => 40803745261662950426109941056260
  | _ => 0

def C088_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 238922427600814495621552734980
  | 1 => 40644360500568427078859551342851
  | 2 => 60847541936927910275132757704707
  | 3 => 61164760445254439224659140609027
  | 4 => 81209490401751851915183093055489
  | 5 => 40882354454194681733391728181506
  | 6 => 40881734275248931478628745675521
  | 7 => 18889465931478614409217
  | 8 => 81367945503705837061335173694208
  | 9 => 20441180268356697055979211326208
  | 10 => 40802506126920428943554268758787
  | 11 => 81368562065355682866308625530884
  | 12 => 929668714832695653545739011
  | 13 => 20521334467974926602694652068098
  | _ => 0

def C088_digit (i j : Fin 14) : ℕ := packedDigit 3 (C088_lowColumnCode j) i.val

private theorem C088_bound_00 : ∀ j : Fin 14, C088_digit 0 j < 5 := by decide +kernel

private theorem C088_bound_01 : ∀ j : Fin 14, C088_digit 1 j < 5 := by decide +kernel

private theorem C088_bound_02 : ∀ j : Fin 14, C088_digit 2 j < 5 := by decide +kernel

private theorem C088_bound_03 : ∀ j : Fin 14, C088_digit 3 j < 5 := by decide +kernel

private theorem C088_bound_04 : ∀ j : Fin 14, C088_digit 4 j < 5 := by decide +kernel

private theorem C088_bound_05 : ∀ j : Fin 14, C088_digit 5 j < 5 := by decide +kernel

private theorem C088_bound_06 : ∀ j : Fin 14, C088_digit 6 j < 5 := by decide +kernel

private theorem C088_bound_07 : ∀ j : Fin 14, C088_digit 7 j < 5 := by decide +kernel

private theorem C088_bound_08 : ∀ j : Fin 14, C088_digit 8 j < 5 := by decide +kernel

private theorem C088_bound_09 : ∀ j : Fin 14, C088_digit 9 j < 5 := by decide +kernel

private theorem C088_bound_10 : ∀ j : Fin 14, C088_digit 10 j < 5 := by decide +kernel

private theorem C088_bound_11 : ∀ j : Fin 14, C088_digit 11 j < 5 := by decide +kernel

private theorem C088_bound_12 : ∀ j : Fin 14, C088_digit 12 j < 5 := by decide +kernel

private theorem C088_bound_13 : ∀ j : Fin 14, C088_digit 13 j < 5 := by decide +kernel

theorem C088_bound : ∀ i j : Fin 14, C088_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C088_bound_00 j
  · exact C088_bound_01 j
  · exact C088_bound_02 j
  · exact C088_bound_03 j
  · exact C088_bound_04 j
  · exact C088_bound_05 j
  · exact C088_bound_06 j
  · exact C088_bound_07 j
  · exact C088_bound_08 j
  · exact C088_bound_09 j
  · exact C088_bound_10 j
  · exact C088_bound_11 j
  · exact C088_bound_12 j
  · exact C088_bound_13 j

private theorem C088_row_00 : pack 256 (C088_digit 0)=C088_rowCode 0 := by decide +kernel

private theorem C088_row_01 : pack 256 (C088_digit 1)=C088_rowCode 1 := by decide +kernel

private theorem C088_row_02 : pack 256 (C088_digit 2)=C088_rowCode 2 := by decide +kernel

private theorem C088_row_03 : pack 256 (C088_digit 3)=C088_rowCode 3 := by decide +kernel

private theorem C088_row_04 : pack 256 (C088_digit 4)=C088_rowCode 4 := by decide +kernel

private theorem C088_row_05 : pack 256 (C088_digit 5)=C088_rowCode 5 := by decide +kernel

private theorem C088_row_06 : pack 256 (C088_digit 6)=C088_rowCode 6 := by decide +kernel

private theorem C088_row_07 : pack 256 (C088_digit 7)=C088_rowCode 7 := by decide +kernel

private theorem C088_row_08 : pack 256 (C088_digit 8)=C088_rowCode 8 := by decide +kernel

private theorem C088_row_09 : pack 256 (C088_digit 9)=C088_rowCode 9 := by decide +kernel

private theorem C088_row_10 : pack 256 (C088_digit 10)=C088_rowCode 10 := by decide +kernel

private theorem C088_row_11 : pack 256 (C088_digit 11)=C088_rowCode 11 := by decide +kernel

private theorem C088_row_12 : pack 256 (C088_digit 12)=C088_rowCode 12 := by decide +kernel

private theorem C088_row_13 : pack 256 (C088_digit 13)=C088_rowCode 13 := by decide +kernel

theorem C088_row_binding : ∀ i : Fin 14, pack 256 (C088_digit i)=C088_rowCode i := by
  intro i
  fin_cases i
  · exact C088_row_00
  · exact C088_row_01
  · exact C088_row_02
  · exact C088_row_03
  · exact C088_row_04
  · exact C088_row_05
  · exact C088_row_06
  · exact C088_row_07
  · exact C088_row_08
  · exact C088_row_09
  · exact C088_row_10
  · exact C088_row_11
  · exact C088_row_12
  · exact C088_row_13

private theorem C088_column_00 : reversePack 256 (fun j : Fin 14 => C088_digit j 0)=C088_columnCode 0 := by decide +kernel

private theorem C088_column_01 : reversePack 256 (fun j : Fin 14 => C088_digit j 1)=C088_columnCode 1 := by decide +kernel

private theorem C088_column_02 : reversePack 256 (fun j : Fin 14 => C088_digit j 2)=C088_columnCode 2 := by decide +kernel

private theorem C088_column_03 : reversePack 256 (fun j : Fin 14 => C088_digit j 3)=C088_columnCode 3 := by decide +kernel

private theorem C088_column_04 : reversePack 256 (fun j : Fin 14 => C088_digit j 4)=C088_columnCode 4 := by decide +kernel

private theorem C088_column_05 : reversePack 256 (fun j : Fin 14 => C088_digit j 5)=C088_columnCode 5 := by decide +kernel

private theorem C088_column_06 : reversePack 256 (fun j : Fin 14 => C088_digit j 6)=C088_columnCode 6 := by decide +kernel

private theorem C088_column_07 : reversePack 256 (fun j : Fin 14 => C088_digit j 7)=C088_columnCode 7 := by decide +kernel

private theorem C088_column_08 : reversePack 256 (fun j : Fin 14 => C088_digit j 8)=C088_columnCode 8 := by decide +kernel

private theorem C088_column_09 : reversePack 256 (fun j : Fin 14 => C088_digit j 9)=C088_columnCode 9 := by decide +kernel

private theorem C088_column_10 : reversePack 256 (fun j : Fin 14 => C088_digit j 10)=C088_columnCode 10 := by decide +kernel

private theorem C088_column_11 : reversePack 256 (fun j : Fin 14 => C088_digit j 11)=C088_columnCode 11 := by decide +kernel

private theorem C088_column_12 : reversePack 256 (fun j : Fin 14 => C088_digit j 12)=C088_columnCode 12 := by decide +kernel

private theorem C088_column_13 : reversePack 256 (fun j : Fin 14 => C088_digit j 13)=C088_columnCode 13 := by decide +kernel

theorem C088_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C088_digit j i)=C088_columnCode i := by
  intro i
  fin_cases i
  · exact C088_column_00
  · exact C088_column_01
  · exact C088_column_02
  · exact C088_column_03
  · exact C088_column_04
  · exact C088_column_05
  · exact C088_column_06
  · exact C088_column_07
  · exact C088_column_08
  · exact C088_column_09
  · exact C088_column_10
  · exact C088_column_11
  · exact C088_column_12
  · exact C088_column_13

def C088_data : PackedData 14 5 256 where
  raw := C088_digit
  digit_lt := C088_bound
  rowCode := C088_rowCode
  columnCode := C088_columnCode
  row_binding := C088_row_binding
  column_binding := C088_column_binding

end SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedCaches09
