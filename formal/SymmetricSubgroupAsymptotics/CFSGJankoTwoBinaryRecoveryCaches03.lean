import SymmetricSubgroupAsymptotics.MatrixKroneckerProductReflection
import Mathlib.Tactic.FinCases

/-! Literal14/F5 selected caches; digit bounds and both pack bindings are independently kernel checked. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryCaches03
open MatrixKroneckerProductReflection MatrixKroneckerDotReflection
open MatrixNaturalRowDotReflection SmallNaturalMatrixProductReflection

def C016_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 1333755782338
  | 1 => 549941260320
  | 2 => 2492293227554
  | 3 => 172393235732
  | 4 => 137982133450
  | 5 => 26843545600
  | 6 => 223641085219
  | 7 => 654216073496
  | 8 => 1237353795584
  | 9 => 68736262292
  | 10 => 17179901952
  | 11 => 8589934592
  | 12 => 309523921044
  | 13 => 208862447257
  | _ => 0

def C016_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 20599322272598194550233595248642
  | 1 => 61005685145428490211454481597440
  | 2 => 40723275541776891845109891465219
  | 3 => 61164141461012069185174506700802
  | 4 => 237684497006045343154803180290
  | 5 => 1208944410473890960179972
  | 6 => 61164141461049251185164497715970
  | 7 => 20282409603651814539148262506496
  | 8 => 20361637770888445922548520059650
  | 9 => 81288094739690695281352498020609
  | 10 => 40564819207303412906588052193282
  | 11 => 317224552918806721325957251075
  | 12 => 61164141465771401495260585787395
  | 13 => 36965545741457293570
  | _ => 0

def C016_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 40565750089703108171784582791938
  | 1 => 316912664279713207289183731713
  | 2 => 40881734284675217700294293062660
  | 3 => 81289335097526424058626138440192
  | 4 => 40644978261588175225873261134336
  | 5 => 16973824
  | 6 => 61165381828347942372478195729152
  | 7 => 238922432341627159606330654977
  | 8 => 4740957342144315523586
  | 9 => 81288713719099586027952344662272
  | 10 => 18446744073709682688
  | 11 => 65536
  | 12 => 81288718559525519199723430609920
  | 13 => 20520716687991781426126672364288
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
  | 0 => 1108657686561
  | 1 => 713435390488
  | 2 => 4899737804
  | 3 => 551962415112
  | 4 => 1804077144320
  | 5 => 21474836480
  | 6 => 215021791442
  | 7 => 649135961179
  | 8 => 28085887184
  | 9 => 1323142321866
  | 10 => 17180000256
  | 11 => 8589934592
  | 12 => 580295098496
  | 13 => 1385135482897
  | _ => 0

def C017_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 20282409613096620125418609180673
  | 1 => 40564819212062817554643650937604
  | 2 => 158456339251041258053300322304
  | 3 => 81129638428773926385503103353092
  | 4 => 40564819212062817554647945904644
  | 5 => 81208871427009842742180293115907
  | 6 => 158456339251041258036137231361
  | 7 => 81288094753802598612924085829633
  | 8 => 316912654816533494186289398785
  | 9 => 237684497006261515924032193284
  | 10 => 40881731857397579921190329516032
  | 11 => 20520406003556213665480080098049
  | 12 => 81129638428773854046425498780160
  | 13 => 40644047379262410208834276557058
  | _ => 0

def C017_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 20599327108356884736723541622786
  | 1 => 237685705913633827936180306433
  | 2 => 81209795036872992728655775924224
  | 3 => 79228167310490983550540578817
  | 4 => 1242780483377913462712828419
  | 5 => 67239936
  | 6 => 40724208832509561718284411273984
  | 7 => 61085225215544884238441831923969
  | 8 => 159384789521388595191727980544
  | 9 => 40644979456402451797987664462594
  | 10 => 73786976294838337536
  | 11 => 65536
  | 12 => 618970038234116760187109377
  | 13 => 20440870773901998625585107108866
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
  | 0 => 150796867291
  | 1 => 1790213928083
  | 2 => 1189108590147
  | 3 => 2417129559649
  | 4 => 2210080628801
  | 5 => 26843545600
  | 6 => 1668649452316
  | 7 => 654198842499
  | 8 => 795139674320
  | 9 => 2364671903331
  | 10 => 17179901952
  | 11 => 8589934592
  | 12 => 77501112857
  | 13 => 1748259840736
  | _ => 0

def C018_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 79228176681581084888812159747
  | 1 => 81367322921075834972620634194435
  | 2 => 60847228815732863228024822235651
  | 3 => 20361637780333178606812833972739
  | 4 => 40723275551239926313830563578625
  | 5 => 158457548140183838792213463299
  | 6 => 40802503709031824168563052184580
  | 7 => 61084913312665048411369367601153
  | 8 => 81367322906908807581618554536196
  | 9 => 20361637775684598818771606635011
  | 10 => 81129638424125274259475277218564
  | 11 => 60926768890571911405295097741313
  | 12 => 20361637775666080017095302644226
  | 13 => 60847228829862996849430259434240
  | _ => 0

def C018_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 61085845385082722395068985049600
  | 1 => 61006306538040656290591589532163
  | 2 => 60847541932223990821114662224130
  | 3 => 20599635370292233761515519410948
  | 4 => 20282719098180299944733414850564
  | 5 => 16973824
  | 6 => 81368562051188367246017071022083
  | 7 => 60847850208344957812517829345537
  | 8 => 159384784798877997146925433601
  | 9 => 61164454591744371993187067298308
  | 10 => 18446744073709682688
  | 11 => 65536
  | 12 => 20520095309602126525753641206016
  | 13 => 317842323457218929964230050051
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
  | 0 => 2431243257992
  | 1 => 1240377923330
  | 2 => 284827399394
  | 3 => 1929027564769
  | 4 => 2236655206682
  | 5 => 268968084
  | 6 => 842889703585
  | 7 => 1823555831585
  | 8 => 1126395349026
  | 9 => 296775201992
  | 10 => 1791305532625
  | 11 => 1332975113884
  | 12 => 77501112857
  | 13 => 1748259840736
  | _ => 0

def C019_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 80467311516335164120704877056
  | 1 => 81368253779827020790686678253569
  | 2 => 60847851421919501050018021966850
  | 3 => 20362568648565774140821595095812
  | 4 => 40723589867212357852276105347328
  | 5 => 159696701846028877145646957056
  | 6 => 40802503709031752394634407576065
  | 7 => 61086152452240832448874323902979
  | 8 => 81368253779790126174440312079361
  | 9 => 20362568653214281592001420984578
  | 10 => 81129952754227838571602723799808
  | 11 => 60927385437999101635945176301571
  | 12 => 20362568657936649198571949916675
  | 13 => 60847851407789222748288467337732
  | _ => 0

def C019_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 79851968237258389374762156804
  | 1 => 40566060778879489725614411219458
  | 2 => 40882662744445638515785751135232
  | 3 => 20600253140775377234784377897987
  | 4 => 40803741634959350335731533086724
  | 5 => 81288713719099730142049498824704
  | 6 => 20599941237895542252136843838465
  | 7 => 20600563839470351068609198162435
  | 8 => 40881736693100643049150804590594
  | 9 => 80159049636470482331395818496
  | 10 => 20441796820487662066907519910403
  | 11 => 81367945503742730830970437698306
  | 12 => 20520095309602126525753641206016
  | 13 => 317842323457218929964230050051
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

end SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryCaches03
