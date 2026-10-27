import SymmetricSubgroupAsymptotics.MatrixKroneckerProductReflection
import Mathlib.Tactic.FinCases

/-! Literal14/F5 selected caches; digit bounds and both pack bindings are independently kernel checked. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedCaches06
open MatrixKroneckerProductReflection MatrixKroneckerDotReflection
open MatrixNaturalRowDotReflection SmallNaturalMatrixProductReflection

def C051_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 2424576786712
  | 1 => 1652526748697
  | 2 => 1662341750796
  | 3 => 1675360474636
  | 4 => 240524604059
  | 5 => 760233436931
  | 6 => 636066277404
  | 7 => 766004200065
  | 8 => 1868518691018
  | 9 => 561909109452
  | 10 => 11816546466
  | 11 => 285016666817
  | 12 => 630607360012
  | 13 => 1687436009538
  | _ => 0

def C051_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 40882043779148291379027184451840
  | 1 => 79233002958356867491429417731
  | 2 => 20283340490755357488836551639044
  | 3 => 309489732261014735194948096
  | 4 => 40803435781393870531874066137348
  | 5 => 81209490387584753032839758610947
  | 6 => 20283652384135191609268343275778
  | 7 => 79849564608203239812881318400
  | 8 => 61086151257500414631364303979012
  | 9 => 81289023204128071133202344902656
  | 10 => 61085226424526042960474493158146
  | 11 => 81209177275797472840585024962562
  | 12 => 80466102609106407658082009091
  | 13 => 60926456978247054664694648472324
  | _ => 0

def C051_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 238922446527028676341396538116
  | 1 => 20520096513805435259746361802755
  | 2 => 81208866586639610656857604030467
  | 3 => 81208870208620843983990834790403
  | 4 => 61085533491684153858717714219776
  | 5 => 60848470387272117769865256764161
  | 6 => 81367327747334380746885837226241
  | 7 => 20283029782615724433513004466945
  | 8 => 40644975829587955354058952344323
  | 9 => 81209796245817115816586907811841
  | 10 => 40882350841621216106636057313280
  | 11 => 20283339281811235808276008469504
  | 12 => 81208866591306492510847346213121
  | 13 => 40565128701831754195907159261187
  | _ => 0

def C051_digit (i j : Fin 14) : ℕ := packedDigit 3 (C051_lowColumnCode j) i.val

private theorem C051_bound_00 : ∀ j : Fin 14, C051_digit 0 j < 5 := by decide +kernel

private theorem C051_bound_01 : ∀ j : Fin 14, C051_digit 1 j < 5 := by decide +kernel

private theorem C051_bound_02 : ∀ j : Fin 14, C051_digit 2 j < 5 := by decide +kernel

private theorem C051_bound_03 : ∀ j : Fin 14, C051_digit 3 j < 5 := by decide +kernel

private theorem C051_bound_04 : ∀ j : Fin 14, C051_digit 4 j < 5 := by decide +kernel

private theorem C051_bound_05 : ∀ j : Fin 14, C051_digit 5 j < 5 := by decide +kernel

private theorem C051_bound_06 : ∀ j : Fin 14, C051_digit 6 j < 5 := by decide +kernel

private theorem C051_bound_07 : ∀ j : Fin 14, C051_digit 7 j < 5 := by decide +kernel

private theorem C051_bound_08 : ∀ j : Fin 14, C051_digit 8 j < 5 := by decide +kernel

private theorem C051_bound_09 : ∀ j : Fin 14, C051_digit 9 j < 5 := by decide +kernel

private theorem C051_bound_10 : ∀ j : Fin 14, C051_digit 10 j < 5 := by decide +kernel

private theorem C051_bound_11 : ∀ j : Fin 14, C051_digit 11 j < 5 := by decide +kernel

private theorem C051_bound_12 : ∀ j : Fin 14, C051_digit 12 j < 5 := by decide +kernel

private theorem C051_bound_13 : ∀ j : Fin 14, C051_digit 13 j < 5 := by decide +kernel

theorem C051_bound : ∀ i j : Fin 14, C051_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C051_bound_00 j
  · exact C051_bound_01 j
  · exact C051_bound_02 j
  · exact C051_bound_03 j
  · exact C051_bound_04 j
  · exact C051_bound_05 j
  · exact C051_bound_06 j
  · exact C051_bound_07 j
  · exact C051_bound_08 j
  · exact C051_bound_09 j
  · exact C051_bound_10 j
  · exact C051_bound_11 j
  · exact C051_bound_12 j
  · exact C051_bound_13 j

private theorem C051_row_00 : pack 256 (C051_digit 0)=C051_rowCode 0 := by decide +kernel

private theorem C051_row_01 : pack 256 (C051_digit 1)=C051_rowCode 1 := by decide +kernel

private theorem C051_row_02 : pack 256 (C051_digit 2)=C051_rowCode 2 := by decide +kernel

private theorem C051_row_03 : pack 256 (C051_digit 3)=C051_rowCode 3 := by decide +kernel

private theorem C051_row_04 : pack 256 (C051_digit 4)=C051_rowCode 4 := by decide +kernel

private theorem C051_row_05 : pack 256 (C051_digit 5)=C051_rowCode 5 := by decide +kernel

private theorem C051_row_06 : pack 256 (C051_digit 6)=C051_rowCode 6 := by decide +kernel

private theorem C051_row_07 : pack 256 (C051_digit 7)=C051_rowCode 7 := by decide +kernel

private theorem C051_row_08 : pack 256 (C051_digit 8)=C051_rowCode 8 := by decide +kernel

private theorem C051_row_09 : pack 256 (C051_digit 9)=C051_rowCode 9 := by decide +kernel

private theorem C051_row_10 : pack 256 (C051_digit 10)=C051_rowCode 10 := by decide +kernel

private theorem C051_row_11 : pack 256 (C051_digit 11)=C051_rowCode 11 := by decide +kernel

private theorem C051_row_12 : pack 256 (C051_digit 12)=C051_rowCode 12 := by decide +kernel

private theorem C051_row_13 : pack 256 (C051_digit 13)=C051_rowCode 13 := by decide +kernel

theorem C051_row_binding : ∀ i : Fin 14, pack 256 (C051_digit i)=C051_rowCode i := by
  intro i
  fin_cases i
  · exact C051_row_00
  · exact C051_row_01
  · exact C051_row_02
  · exact C051_row_03
  · exact C051_row_04
  · exact C051_row_05
  · exact C051_row_06
  · exact C051_row_07
  · exact C051_row_08
  · exact C051_row_09
  · exact C051_row_10
  · exact C051_row_11
  · exact C051_row_12
  · exact C051_row_13

private theorem C051_column_00 : reversePack 256 (fun j : Fin 14 => C051_digit j 0)=C051_columnCode 0 := by decide +kernel

private theorem C051_column_01 : reversePack 256 (fun j : Fin 14 => C051_digit j 1)=C051_columnCode 1 := by decide +kernel

private theorem C051_column_02 : reversePack 256 (fun j : Fin 14 => C051_digit j 2)=C051_columnCode 2 := by decide +kernel

private theorem C051_column_03 : reversePack 256 (fun j : Fin 14 => C051_digit j 3)=C051_columnCode 3 := by decide +kernel

private theorem C051_column_04 : reversePack 256 (fun j : Fin 14 => C051_digit j 4)=C051_columnCode 4 := by decide +kernel

private theorem C051_column_05 : reversePack 256 (fun j : Fin 14 => C051_digit j 5)=C051_columnCode 5 := by decide +kernel

private theorem C051_column_06 : reversePack 256 (fun j : Fin 14 => C051_digit j 6)=C051_columnCode 6 := by decide +kernel

private theorem C051_column_07 : reversePack 256 (fun j : Fin 14 => C051_digit j 7)=C051_columnCode 7 := by decide +kernel

private theorem C051_column_08 : reversePack 256 (fun j : Fin 14 => C051_digit j 8)=C051_columnCode 8 := by decide +kernel

private theorem C051_column_09 : reversePack 256 (fun j : Fin 14 => C051_digit j 9)=C051_columnCode 9 := by decide +kernel

private theorem C051_column_10 : reversePack 256 (fun j : Fin 14 => C051_digit j 10)=C051_columnCode 10 := by decide +kernel

private theorem C051_column_11 : reversePack 256 (fun j : Fin 14 => C051_digit j 11)=C051_columnCode 11 := by decide +kernel

private theorem C051_column_12 : reversePack 256 (fun j : Fin 14 => C051_digit j 12)=C051_columnCode 12 := by decide +kernel

private theorem C051_column_13 : reversePack 256 (fun j : Fin 14 => C051_digit j 13)=C051_columnCode 13 := by decide +kernel

theorem C051_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C051_digit j i)=C051_columnCode i := by
  intro i
  fin_cases i
  · exact C051_column_00
  · exact C051_column_01
  · exact C051_column_02
  · exact C051_column_03
  · exact C051_column_04
  · exact C051_column_05
  · exact C051_column_06
  · exact C051_column_07
  · exact C051_column_08
  · exact C051_column_09
  · exact C051_column_10
  · exact C051_column_11
  · exact C051_column_12
  · exact C051_column_13

def C051_data : PackedData 14 5 256 where
  raw := C051_digit
  digit_lt := C051_bound
  rowCode := C051_rowCode
  columnCode := C051_columnCode
  row_binding := C051_row_binding
  column_binding := C051_column_binding

def C052_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 225939329745
  | 1 => 1746307457124
  | 2 => 89144209474
  | 3 => 1867430892249
  | 4 => 166741248225
  | 5 => 783351550154
  | 6 => 87427155740
  | 7 => 2235668968668
  | 8 => 781844615964
  | 9 => 1951262312659
  | 10 => 2224997315276
  | 11 => 11965411457
  | 12 => 1962960077451
  | 13 => 1925798200320
  | _ => 0

def C052_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 237998822497068599749222990849
  | 1 => 79229380940374168506923484162
  | 2 => 159078936066733936109326237955
  | 3 => 40644048597651482435299714269185
  | 4 => 317844731882643147423226200577
  | 5 => 20521023755223678459534075036161
  | 6 => 20442107509737830875212890112514
  | 7 => 81446861768118044066399066980352
  | 8 => 40644361690549152580879285026819
  | 9 => 81209177280519839609319069844227
  | 10 => 20600250713460702690172746269186
  | 11 => 317225776067066016798030824194
  | 12 => 81446551083608545494645042381059
  | 13 => 61084918148386917167297443398400
  | _ => 0

def C052_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 20441795597376440094412572328704
  | 1 => 81446860559155330960319609766147
  | 2 => 40565128706498853346358440624384
  | 3 => 20521023759946117847712616481539
  | 4 => 20600255544497027801155113255424
  | 5 => 40644975829569508608898565866241
  | 6 => 81368564468984953910493358194944
  | 7 => 81368253789234571472744797700100
  | 8 => 81368562055911022520018059592449
  | 9 => 61006618426716499176492389041155
  | 10 => 81209796255261992334559975505924
  | 11 => 20283028587894041307869750558720
  | 12 => 60927077171359689320093488251907
  | 13 => 2417870159159042223637507
  | _ => 0

def C052_digit (i j : Fin 14) : ℕ := packedDigit 3 (C052_lowColumnCode j) i.val

private theorem C052_bound_00 : ∀ j : Fin 14, C052_digit 0 j < 5 := by decide +kernel

private theorem C052_bound_01 : ∀ j : Fin 14, C052_digit 1 j < 5 := by decide +kernel

private theorem C052_bound_02 : ∀ j : Fin 14, C052_digit 2 j < 5 := by decide +kernel

private theorem C052_bound_03 : ∀ j : Fin 14, C052_digit 3 j < 5 := by decide +kernel

private theorem C052_bound_04 : ∀ j : Fin 14, C052_digit 4 j < 5 := by decide +kernel

private theorem C052_bound_05 : ∀ j : Fin 14, C052_digit 5 j < 5 := by decide +kernel

private theorem C052_bound_06 : ∀ j : Fin 14, C052_digit 6 j < 5 := by decide +kernel

private theorem C052_bound_07 : ∀ j : Fin 14, C052_digit 7 j < 5 := by decide +kernel

private theorem C052_bound_08 : ∀ j : Fin 14, C052_digit 8 j < 5 := by decide +kernel

private theorem C052_bound_09 : ∀ j : Fin 14, C052_digit 9 j < 5 := by decide +kernel

private theorem C052_bound_10 : ∀ j : Fin 14, C052_digit 10 j < 5 := by decide +kernel

private theorem C052_bound_11 : ∀ j : Fin 14, C052_digit 11 j < 5 := by decide +kernel

private theorem C052_bound_12 : ∀ j : Fin 14, C052_digit 12 j < 5 := by decide +kernel

private theorem C052_bound_13 : ∀ j : Fin 14, C052_digit 13 j < 5 := by decide +kernel

theorem C052_bound : ∀ i j : Fin 14, C052_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C052_bound_00 j
  · exact C052_bound_01 j
  · exact C052_bound_02 j
  · exact C052_bound_03 j
  · exact C052_bound_04 j
  · exact C052_bound_05 j
  · exact C052_bound_06 j
  · exact C052_bound_07 j
  · exact C052_bound_08 j
  · exact C052_bound_09 j
  · exact C052_bound_10 j
  · exact C052_bound_11 j
  · exact C052_bound_12 j
  · exact C052_bound_13 j

private theorem C052_row_00 : pack 256 (C052_digit 0)=C052_rowCode 0 := by decide +kernel

private theorem C052_row_01 : pack 256 (C052_digit 1)=C052_rowCode 1 := by decide +kernel

private theorem C052_row_02 : pack 256 (C052_digit 2)=C052_rowCode 2 := by decide +kernel

private theorem C052_row_03 : pack 256 (C052_digit 3)=C052_rowCode 3 := by decide +kernel

private theorem C052_row_04 : pack 256 (C052_digit 4)=C052_rowCode 4 := by decide +kernel

private theorem C052_row_05 : pack 256 (C052_digit 5)=C052_rowCode 5 := by decide +kernel

private theorem C052_row_06 : pack 256 (C052_digit 6)=C052_rowCode 6 := by decide +kernel

private theorem C052_row_07 : pack 256 (C052_digit 7)=C052_rowCode 7 := by decide +kernel

private theorem C052_row_08 : pack 256 (C052_digit 8)=C052_rowCode 8 := by decide +kernel

private theorem C052_row_09 : pack 256 (C052_digit 9)=C052_rowCode 9 := by decide +kernel

private theorem C052_row_10 : pack 256 (C052_digit 10)=C052_rowCode 10 := by decide +kernel

private theorem C052_row_11 : pack 256 (C052_digit 11)=C052_rowCode 11 := by decide +kernel

private theorem C052_row_12 : pack 256 (C052_digit 12)=C052_rowCode 12 := by decide +kernel

private theorem C052_row_13 : pack 256 (C052_digit 13)=C052_rowCode 13 := by decide +kernel

theorem C052_row_binding : ∀ i : Fin 14, pack 256 (C052_digit i)=C052_rowCode i := by
  intro i
  fin_cases i
  · exact C052_row_00
  · exact C052_row_01
  · exact C052_row_02
  · exact C052_row_03
  · exact C052_row_04
  · exact C052_row_05
  · exact C052_row_06
  · exact C052_row_07
  · exact C052_row_08
  · exact C052_row_09
  · exact C052_row_10
  · exact C052_row_11
  · exact C052_row_12
  · exact C052_row_13

private theorem C052_column_00 : reversePack 256 (fun j : Fin 14 => C052_digit j 0)=C052_columnCode 0 := by decide +kernel

private theorem C052_column_01 : reversePack 256 (fun j : Fin 14 => C052_digit j 1)=C052_columnCode 1 := by decide +kernel

private theorem C052_column_02 : reversePack 256 (fun j : Fin 14 => C052_digit j 2)=C052_columnCode 2 := by decide +kernel

private theorem C052_column_03 : reversePack 256 (fun j : Fin 14 => C052_digit j 3)=C052_columnCode 3 := by decide +kernel

private theorem C052_column_04 : reversePack 256 (fun j : Fin 14 => C052_digit j 4)=C052_columnCode 4 := by decide +kernel

private theorem C052_column_05 : reversePack 256 (fun j : Fin 14 => C052_digit j 5)=C052_columnCode 5 := by decide +kernel

private theorem C052_column_06 : reversePack 256 (fun j : Fin 14 => C052_digit j 6)=C052_columnCode 6 := by decide +kernel

private theorem C052_column_07 : reversePack 256 (fun j : Fin 14 => C052_digit j 7)=C052_columnCode 7 := by decide +kernel

private theorem C052_column_08 : reversePack 256 (fun j : Fin 14 => C052_digit j 8)=C052_columnCode 8 := by decide +kernel

private theorem C052_column_09 : reversePack 256 (fun j : Fin 14 => C052_digit j 9)=C052_columnCode 9 := by decide +kernel

private theorem C052_column_10 : reversePack 256 (fun j : Fin 14 => C052_digit j 10)=C052_columnCode 10 := by decide +kernel

private theorem C052_column_11 : reversePack 256 (fun j : Fin 14 => C052_digit j 11)=C052_columnCode 11 := by decide +kernel

private theorem C052_column_12 : reversePack 256 (fun j : Fin 14 => C052_digit j 12)=C052_columnCode 12 := by decide +kernel

private theorem C052_column_13 : reversePack 256 (fun j : Fin 14 => C052_digit j 13)=C052_columnCode 13 := by decide +kernel

theorem C052_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C052_digit j i)=C052_columnCode i := by
  intro i
  fin_cases i
  · exact C052_column_00
  · exact C052_column_01
  · exact C052_column_02
  · exact C052_column_03
  · exact C052_column_04
  · exact C052_column_05
  · exact C052_column_06
  · exact C052_column_07
  · exact C052_column_08
  · exact C052_column_09
  · exact C052_column_10
  · exact C052_column_11
  · exact C052_column_12
  · exact C052_column_13

def C052_data : PackedData 14 5 256 where
  raw := C052_digit
  digit_lt := C052_bound
  rowCode := C052_rowCode
  columnCode := C052_columnCode
  row_binding := C052_row_binding
  column_binding := C052_column_binding

def C054_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 1953193332760
  | 1 => 1375674140176
  | 2 => 106846495844
  | 3 => 2375402406560
  | 4 => 1169374450778
  | 5 => 656610037964
  | 6 => 554194487442
  | 7 => 1893275275362
  | 8 => 1808584775177
  | 9 => 689497801754
  | 10 => 687786473699
  | 11 => 618947188760
  | 12 => 704952468003
  | 13 => 2492443002625
  | _ => 0

def C054_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 20520097727435246672973073219584
  | 1 => 317845954975634831218263196163
  | 2 => 81129642041384213163523384082432
  | 3 => 60927699758711913772095828525824
  | 4 => 313111805800117627777056769
  | 5 => 81288405447793291297394259919618
  | 6 => 61164142674715596077840097018881
  | 7 => 20520406003500658102698449830915
  | 8 => 20442107500219309807283115918339
  | 9 => 40882665152870991808143458304256
  | 10 => 20282409613170407667966297702659
  | 11 => 40723275532369051246003275169795
  | 12 => 81288406651978513573075830768644
  | 13 => 81209177275834510163536481616387
  | _ => 0

def C054_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 237684492302125889115249640451
  | 1 => 158459951861617111974157485058
  | 2 => 81446862976970149884928796655872
  | 3 => 317532847892057645321587786244
  | 4 => 40802815602503820237633769963778
  | 5 => 81209795036946563528869948948737
  | 6 => 40723899356962992703568449896449
  | 7 => 40882041347092586026215688897283
  | 8 => 20361641397721316493314159149571
  | 9 => 40802506112753185943802443989505
  | 10 => 61165074765930429932481154122241
  | 11 => 237689327986884984126593564929
  | 12 => 61164142669975070802009808568833
  | 13 => 20283651170542418079769721701380
  | _ => 0

def C054_digit (i j : Fin 14) : ℕ := packedDigit 3 (C054_lowColumnCode j) i.val

private theorem C054_bound_00 : ∀ j : Fin 14, C054_digit 0 j < 5 := by decide +kernel

private theorem C054_bound_01 : ∀ j : Fin 14, C054_digit 1 j < 5 := by decide +kernel

private theorem C054_bound_02 : ∀ j : Fin 14, C054_digit 2 j < 5 := by decide +kernel

private theorem C054_bound_03 : ∀ j : Fin 14, C054_digit 3 j < 5 := by decide +kernel

private theorem C054_bound_04 : ∀ j : Fin 14, C054_digit 4 j < 5 := by decide +kernel

private theorem C054_bound_05 : ∀ j : Fin 14, C054_digit 5 j < 5 := by decide +kernel

private theorem C054_bound_06 : ∀ j : Fin 14, C054_digit 6 j < 5 := by decide +kernel

private theorem C054_bound_07 : ∀ j : Fin 14, C054_digit 7 j < 5 := by decide +kernel

private theorem C054_bound_08 : ∀ j : Fin 14, C054_digit 8 j < 5 := by decide +kernel

private theorem C054_bound_09 : ∀ j : Fin 14, C054_digit 9 j < 5 := by decide +kernel

private theorem C054_bound_10 : ∀ j : Fin 14, C054_digit 10 j < 5 := by decide +kernel

private theorem C054_bound_11 : ∀ j : Fin 14, C054_digit 11 j < 5 := by decide +kernel

private theorem C054_bound_12 : ∀ j : Fin 14, C054_digit 12 j < 5 := by decide +kernel

private theorem C054_bound_13 : ∀ j : Fin 14, C054_digit 13 j < 5 := by decide +kernel

theorem C054_bound : ∀ i j : Fin 14, C054_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C054_bound_00 j
  · exact C054_bound_01 j
  · exact C054_bound_02 j
  · exact C054_bound_03 j
  · exact C054_bound_04 j
  · exact C054_bound_05 j
  · exact C054_bound_06 j
  · exact C054_bound_07 j
  · exact C054_bound_08 j
  · exact C054_bound_09 j
  · exact C054_bound_10 j
  · exact C054_bound_11 j
  · exact C054_bound_12 j
  · exact C054_bound_13 j

private theorem C054_row_00 : pack 256 (C054_digit 0)=C054_rowCode 0 := by decide +kernel

private theorem C054_row_01 : pack 256 (C054_digit 1)=C054_rowCode 1 := by decide +kernel

private theorem C054_row_02 : pack 256 (C054_digit 2)=C054_rowCode 2 := by decide +kernel

private theorem C054_row_03 : pack 256 (C054_digit 3)=C054_rowCode 3 := by decide +kernel

private theorem C054_row_04 : pack 256 (C054_digit 4)=C054_rowCode 4 := by decide +kernel

private theorem C054_row_05 : pack 256 (C054_digit 5)=C054_rowCode 5 := by decide +kernel

private theorem C054_row_06 : pack 256 (C054_digit 6)=C054_rowCode 6 := by decide +kernel

private theorem C054_row_07 : pack 256 (C054_digit 7)=C054_rowCode 7 := by decide +kernel

private theorem C054_row_08 : pack 256 (C054_digit 8)=C054_rowCode 8 := by decide +kernel

private theorem C054_row_09 : pack 256 (C054_digit 9)=C054_rowCode 9 := by decide +kernel

private theorem C054_row_10 : pack 256 (C054_digit 10)=C054_rowCode 10 := by decide +kernel

private theorem C054_row_11 : pack 256 (C054_digit 11)=C054_rowCode 11 := by decide +kernel

private theorem C054_row_12 : pack 256 (C054_digit 12)=C054_rowCode 12 := by decide +kernel

private theorem C054_row_13 : pack 256 (C054_digit 13)=C054_rowCode 13 := by decide +kernel

theorem C054_row_binding : ∀ i : Fin 14, pack 256 (C054_digit i)=C054_rowCode i := by
  intro i
  fin_cases i
  · exact C054_row_00
  · exact C054_row_01
  · exact C054_row_02
  · exact C054_row_03
  · exact C054_row_04
  · exact C054_row_05
  · exact C054_row_06
  · exact C054_row_07
  · exact C054_row_08
  · exact C054_row_09
  · exact C054_row_10
  · exact C054_row_11
  · exact C054_row_12
  · exact C054_row_13

private theorem C054_column_00 : reversePack 256 (fun j : Fin 14 => C054_digit j 0)=C054_columnCode 0 := by decide +kernel

private theorem C054_column_01 : reversePack 256 (fun j : Fin 14 => C054_digit j 1)=C054_columnCode 1 := by decide +kernel

private theorem C054_column_02 : reversePack 256 (fun j : Fin 14 => C054_digit j 2)=C054_columnCode 2 := by decide +kernel

private theorem C054_column_03 : reversePack 256 (fun j : Fin 14 => C054_digit j 3)=C054_columnCode 3 := by decide +kernel

private theorem C054_column_04 : reversePack 256 (fun j : Fin 14 => C054_digit j 4)=C054_columnCode 4 := by decide +kernel

private theorem C054_column_05 : reversePack 256 (fun j : Fin 14 => C054_digit j 5)=C054_columnCode 5 := by decide +kernel

private theorem C054_column_06 : reversePack 256 (fun j : Fin 14 => C054_digit j 6)=C054_columnCode 6 := by decide +kernel

private theorem C054_column_07 : reversePack 256 (fun j : Fin 14 => C054_digit j 7)=C054_columnCode 7 := by decide +kernel

private theorem C054_column_08 : reversePack 256 (fun j : Fin 14 => C054_digit j 8)=C054_columnCode 8 := by decide +kernel

private theorem C054_column_09 : reversePack 256 (fun j : Fin 14 => C054_digit j 9)=C054_columnCode 9 := by decide +kernel

private theorem C054_column_10 : reversePack 256 (fun j : Fin 14 => C054_digit j 10)=C054_columnCode 10 := by decide +kernel

private theorem C054_column_11 : reversePack 256 (fun j : Fin 14 => C054_digit j 11)=C054_columnCode 11 := by decide +kernel

private theorem C054_column_12 : reversePack 256 (fun j : Fin 14 => C054_digit j 12)=C054_columnCode 12 := by decide +kernel

private theorem C054_column_13 : reversePack 256 (fun j : Fin 14 => C054_digit j 13)=C054_columnCode 13 := by decide +kernel

theorem C054_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C054_digit j i)=C054_columnCode i := by
  intro i
  fin_cases i
  · exact C054_column_00
  · exact C054_column_01
  · exact C054_column_02
  · exact C054_column_03
  · exact C054_column_04
  · exact C054_column_05
  · exact C054_column_06
  · exact C054_column_07
  · exact C054_column_08
  · exact C054_column_09
  · exact C054_column_10
  · exact C054_column_11
  · exact C054_column_12
  · exact C054_column_13

def C054_data : PackedData 14 5 256 where
  raw := C054_digit
  digit_lt := C054_bound
  rowCode := C054_rowCode
  columnCode := C054_columnCode
  row_binding := C054_row_binding
  column_binding := C054_column_binding

def C056_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 1412262282896
  | 1 => 1924418877017
  | 2 => 1258744809233
  | 3 => 833767744227
  | 4 => 860134586073
  | 5 => 1857615956176
  | 6 => 724965622795
  | 7 => 309313685779
  | 8 => 209656546332
  | 9 => 1668111210720
  | 10 => 709225678619
  | 11 => 2354184340001
  | 12 => 1881673842841
  | 13 => 2432498286876
  | _ => 0

def C056_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 81209179688982230215845025480960
  | 1 => 61086154884259499071359546426114
  | 2 => 81288099589505876511789349601538
  | 3 => 313130713928406319302378243
  | 4 => 81447789009425679139696795452164
  | 5 => 81130878781979233608032007160576
  | 6 => 81130877577739031382593366000385
  | 7 => 20599942437450632335976736752131
  | 8 => 81446552287756947186418576457729
  | 9 => 61086156093166727824515027567106
  | 10 => 20282414444132656444182972596227
  | 11 => 61085534695814108526050730442756
  | 12 => 61085534686424715232881200464900
  | 13 => 81368562065281679436860469936898
  | _ => 0

def C056_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 159078940715169043817762653186
  | 1 => 20520407217204400042254853473283
  | 2 => 20442107495552427674013158998530
  | 3 => 61165071134486089231309631194113
  | 4 => 20521026187168557826422618719233
  | 5 => 159389615835203388491838784259
  | 6 => 60926459391376543867543761453569
  | 7 => 61006927930615714962785050035200
  | 8 => 81367325320038008551883952620288
  | 9 => 317845945549276272686935441411
  | 10 => 61086154865351514337118001431041
  | 11 => 20599323481598089090067305988612
  | 12 => 20520713080103573188654752006915
  | 13 => 81368560861152301512880031990532
  | _ => 0

def C056_digit (i j : Fin 14) : ℕ := packedDigit 3 (C056_lowColumnCode j) i.val

private theorem C056_bound_00 : ∀ j : Fin 14, C056_digit 0 j < 5 := by decide +kernel

private theorem C056_bound_01 : ∀ j : Fin 14, C056_digit 1 j < 5 := by decide +kernel

private theorem C056_bound_02 : ∀ j : Fin 14, C056_digit 2 j < 5 := by decide +kernel

private theorem C056_bound_03 : ∀ j : Fin 14, C056_digit 3 j < 5 := by decide +kernel

private theorem C056_bound_04 : ∀ j : Fin 14, C056_digit 4 j < 5 := by decide +kernel

private theorem C056_bound_05 : ∀ j : Fin 14, C056_digit 5 j < 5 := by decide +kernel

private theorem C056_bound_06 : ∀ j : Fin 14, C056_digit 6 j < 5 := by decide +kernel

private theorem C056_bound_07 : ∀ j : Fin 14, C056_digit 7 j < 5 := by decide +kernel

private theorem C056_bound_08 : ∀ j : Fin 14, C056_digit 8 j < 5 := by decide +kernel

private theorem C056_bound_09 : ∀ j : Fin 14, C056_digit 9 j < 5 := by decide +kernel

private theorem C056_bound_10 : ∀ j : Fin 14, C056_digit 10 j < 5 := by decide +kernel

private theorem C056_bound_11 : ∀ j : Fin 14, C056_digit 11 j < 5 := by decide +kernel

private theorem C056_bound_12 : ∀ j : Fin 14, C056_digit 12 j < 5 := by decide +kernel

private theorem C056_bound_13 : ∀ j : Fin 14, C056_digit 13 j < 5 := by decide +kernel

theorem C056_bound : ∀ i j : Fin 14, C056_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C056_bound_00 j
  · exact C056_bound_01 j
  · exact C056_bound_02 j
  · exact C056_bound_03 j
  · exact C056_bound_04 j
  · exact C056_bound_05 j
  · exact C056_bound_06 j
  · exact C056_bound_07 j
  · exact C056_bound_08 j
  · exact C056_bound_09 j
  · exact C056_bound_10 j
  · exact C056_bound_11 j
  · exact C056_bound_12 j
  · exact C056_bound_13 j

private theorem C056_row_00 : pack 256 (C056_digit 0)=C056_rowCode 0 := by decide +kernel

private theorem C056_row_01 : pack 256 (C056_digit 1)=C056_rowCode 1 := by decide +kernel

private theorem C056_row_02 : pack 256 (C056_digit 2)=C056_rowCode 2 := by decide +kernel

private theorem C056_row_03 : pack 256 (C056_digit 3)=C056_rowCode 3 := by decide +kernel

private theorem C056_row_04 : pack 256 (C056_digit 4)=C056_rowCode 4 := by decide +kernel

private theorem C056_row_05 : pack 256 (C056_digit 5)=C056_rowCode 5 := by decide +kernel

private theorem C056_row_06 : pack 256 (C056_digit 6)=C056_rowCode 6 := by decide +kernel

private theorem C056_row_07 : pack 256 (C056_digit 7)=C056_rowCode 7 := by decide +kernel

private theorem C056_row_08 : pack 256 (C056_digit 8)=C056_rowCode 8 := by decide +kernel

private theorem C056_row_09 : pack 256 (C056_digit 9)=C056_rowCode 9 := by decide +kernel

private theorem C056_row_10 : pack 256 (C056_digit 10)=C056_rowCode 10 := by decide +kernel

private theorem C056_row_11 : pack 256 (C056_digit 11)=C056_rowCode 11 := by decide +kernel

private theorem C056_row_12 : pack 256 (C056_digit 12)=C056_rowCode 12 := by decide +kernel

private theorem C056_row_13 : pack 256 (C056_digit 13)=C056_rowCode 13 := by decide +kernel

theorem C056_row_binding : ∀ i : Fin 14, pack 256 (C056_digit i)=C056_rowCode i := by
  intro i
  fin_cases i
  · exact C056_row_00
  · exact C056_row_01
  · exact C056_row_02
  · exact C056_row_03
  · exact C056_row_04
  · exact C056_row_05
  · exact C056_row_06
  · exact C056_row_07
  · exact C056_row_08
  · exact C056_row_09
  · exact C056_row_10
  · exact C056_row_11
  · exact C056_row_12
  · exact C056_row_13

private theorem C056_column_00 : reversePack 256 (fun j : Fin 14 => C056_digit j 0)=C056_columnCode 0 := by decide +kernel

private theorem C056_column_01 : reversePack 256 (fun j : Fin 14 => C056_digit j 1)=C056_columnCode 1 := by decide +kernel

private theorem C056_column_02 : reversePack 256 (fun j : Fin 14 => C056_digit j 2)=C056_columnCode 2 := by decide +kernel

private theorem C056_column_03 : reversePack 256 (fun j : Fin 14 => C056_digit j 3)=C056_columnCode 3 := by decide +kernel

private theorem C056_column_04 : reversePack 256 (fun j : Fin 14 => C056_digit j 4)=C056_columnCode 4 := by decide +kernel

private theorem C056_column_05 : reversePack 256 (fun j : Fin 14 => C056_digit j 5)=C056_columnCode 5 := by decide +kernel

private theorem C056_column_06 : reversePack 256 (fun j : Fin 14 => C056_digit j 6)=C056_columnCode 6 := by decide +kernel

private theorem C056_column_07 : reversePack 256 (fun j : Fin 14 => C056_digit j 7)=C056_columnCode 7 := by decide +kernel

private theorem C056_column_08 : reversePack 256 (fun j : Fin 14 => C056_digit j 8)=C056_columnCode 8 := by decide +kernel

private theorem C056_column_09 : reversePack 256 (fun j : Fin 14 => C056_digit j 9)=C056_columnCode 9 := by decide +kernel

private theorem C056_column_10 : reversePack 256 (fun j : Fin 14 => C056_digit j 10)=C056_columnCode 10 := by decide +kernel

private theorem C056_column_11 : reversePack 256 (fun j : Fin 14 => C056_digit j 11)=C056_columnCode 11 := by decide +kernel

private theorem C056_column_12 : reversePack 256 (fun j : Fin 14 => C056_digit j 12)=C056_columnCode 12 := by decide +kernel

private theorem C056_column_13 : reversePack 256 (fun j : Fin 14 => C056_digit j 13)=C056_columnCode 13 := by decide +kernel

theorem C056_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C056_digit j i)=C056_columnCode i := by
  intro i
  fin_cases i
  · exact C056_column_00
  · exact C056_column_01
  · exact C056_column_02
  · exact C056_column_03
  · exact C056_column_04
  · exact C056_column_05
  · exact C056_column_06
  · exact C056_column_07
  · exact C056_column_08
  · exact C056_column_09
  · exact C056_column_10
  · exact C056_column_11
  · exact C056_column_12
  · exact C056_column_13

def C056_data : PackedData 14 5 256 where
  raw := C056_digit
  digit_lt := C056_bound
  rowCode := C056_rowCode
  columnCode := C056_columnCode
  row_binding := C056_row_binding
  column_binding := C056_column_binding

def C059_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 100
  | 1 => 1548
  | 2 => 1547
  | 3 => 6144
  | 4 => 2048
  | 5 => 262144
  | 6 => 16777216
  | 7 => 134217728
  | 8 => 32768
  | 9 => 1073741824
  | 10 => 2097152
  | 11 => 68719476736
  | 12 => 549755813888
  | 13 => 8589934592
  | _ => 0

def C059_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 197636
  | 1 => 65796
  | 2 => 1
  | 3 => 17247175424
  | 4 => 16777216
  | 5 => 18446744073709551616
  | 6 => 1099511627776
  | 7 => 1208925819614629174706176
  | 8 => 281474976710656
  | 9 => 72057594037927936
  | 10 => 4722366482869645213696
  | 11 => 20282409603651670423947251286016
  | 12 => 309485009821345068724781056
  | 13 => 79228162514264337593543950336
  | _ => 0

def C059_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 81446860549673560391231905726464
  | 1 => 81208870203898404877270073212928
  | 2 => 60926460600246734453322821926912
  | 3 => 4840425644941386344038400
  | 4 => 4835703278458516698824704
  | 5 => 72057594037927936
  | 6 => 1099511627776
  | 7 => 4294967296
  | 8 => 18446744073709551616
  | 9 => 16777216
  | 10 => 281474976710656
  | 11 => 256
  | 12 => 1
  | 13 => 65536
  | _ => 0

def C059_digit (i j : Fin 14) : ℕ := packedDigit 3 (C059_lowColumnCode j) i.val

private theorem C059_bound_00 : ∀ j : Fin 14, C059_digit 0 j < 5 := by decide +kernel

private theorem C059_bound_01 : ∀ j : Fin 14, C059_digit 1 j < 5 := by decide +kernel

private theorem C059_bound_02 : ∀ j : Fin 14, C059_digit 2 j < 5 := by decide +kernel

private theorem C059_bound_03 : ∀ j : Fin 14, C059_digit 3 j < 5 := by decide +kernel

private theorem C059_bound_04 : ∀ j : Fin 14, C059_digit 4 j < 5 := by decide +kernel

private theorem C059_bound_05 : ∀ j : Fin 14, C059_digit 5 j < 5 := by decide +kernel

private theorem C059_bound_06 : ∀ j : Fin 14, C059_digit 6 j < 5 := by decide +kernel

private theorem C059_bound_07 : ∀ j : Fin 14, C059_digit 7 j < 5 := by decide +kernel

private theorem C059_bound_08 : ∀ j : Fin 14, C059_digit 8 j < 5 := by decide +kernel

private theorem C059_bound_09 : ∀ j : Fin 14, C059_digit 9 j < 5 := by decide +kernel

private theorem C059_bound_10 : ∀ j : Fin 14, C059_digit 10 j < 5 := by decide +kernel

private theorem C059_bound_11 : ∀ j : Fin 14, C059_digit 11 j < 5 := by decide +kernel

private theorem C059_bound_12 : ∀ j : Fin 14, C059_digit 12 j < 5 := by decide +kernel

private theorem C059_bound_13 : ∀ j : Fin 14, C059_digit 13 j < 5 := by decide +kernel

theorem C059_bound : ∀ i j : Fin 14, C059_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C059_bound_00 j
  · exact C059_bound_01 j
  · exact C059_bound_02 j
  · exact C059_bound_03 j
  · exact C059_bound_04 j
  · exact C059_bound_05 j
  · exact C059_bound_06 j
  · exact C059_bound_07 j
  · exact C059_bound_08 j
  · exact C059_bound_09 j
  · exact C059_bound_10 j
  · exact C059_bound_11 j
  · exact C059_bound_12 j
  · exact C059_bound_13 j

private theorem C059_row_00 : pack 256 (C059_digit 0)=C059_rowCode 0 := by decide +kernel

private theorem C059_row_01 : pack 256 (C059_digit 1)=C059_rowCode 1 := by decide +kernel

private theorem C059_row_02 : pack 256 (C059_digit 2)=C059_rowCode 2 := by decide +kernel

private theorem C059_row_03 : pack 256 (C059_digit 3)=C059_rowCode 3 := by decide +kernel

private theorem C059_row_04 : pack 256 (C059_digit 4)=C059_rowCode 4 := by decide +kernel

private theorem C059_row_05 : pack 256 (C059_digit 5)=C059_rowCode 5 := by decide +kernel

private theorem C059_row_06 : pack 256 (C059_digit 6)=C059_rowCode 6 := by decide +kernel

private theorem C059_row_07 : pack 256 (C059_digit 7)=C059_rowCode 7 := by decide +kernel

private theorem C059_row_08 : pack 256 (C059_digit 8)=C059_rowCode 8 := by decide +kernel

private theorem C059_row_09 : pack 256 (C059_digit 9)=C059_rowCode 9 := by decide +kernel

private theorem C059_row_10 : pack 256 (C059_digit 10)=C059_rowCode 10 := by decide +kernel

private theorem C059_row_11 : pack 256 (C059_digit 11)=C059_rowCode 11 := by decide +kernel

private theorem C059_row_12 : pack 256 (C059_digit 12)=C059_rowCode 12 := by decide +kernel

private theorem C059_row_13 : pack 256 (C059_digit 13)=C059_rowCode 13 := by decide +kernel

theorem C059_row_binding : ∀ i : Fin 14, pack 256 (C059_digit i)=C059_rowCode i := by
  intro i
  fin_cases i
  · exact C059_row_00
  · exact C059_row_01
  · exact C059_row_02
  · exact C059_row_03
  · exact C059_row_04
  · exact C059_row_05
  · exact C059_row_06
  · exact C059_row_07
  · exact C059_row_08
  · exact C059_row_09
  · exact C059_row_10
  · exact C059_row_11
  · exact C059_row_12
  · exact C059_row_13

private theorem C059_column_00 : reversePack 256 (fun j : Fin 14 => C059_digit j 0)=C059_columnCode 0 := by decide +kernel

private theorem C059_column_01 : reversePack 256 (fun j : Fin 14 => C059_digit j 1)=C059_columnCode 1 := by decide +kernel

private theorem C059_column_02 : reversePack 256 (fun j : Fin 14 => C059_digit j 2)=C059_columnCode 2 := by decide +kernel

private theorem C059_column_03 : reversePack 256 (fun j : Fin 14 => C059_digit j 3)=C059_columnCode 3 := by decide +kernel

private theorem C059_column_04 : reversePack 256 (fun j : Fin 14 => C059_digit j 4)=C059_columnCode 4 := by decide +kernel

private theorem C059_column_05 : reversePack 256 (fun j : Fin 14 => C059_digit j 5)=C059_columnCode 5 := by decide +kernel

private theorem C059_column_06 : reversePack 256 (fun j : Fin 14 => C059_digit j 6)=C059_columnCode 6 := by decide +kernel

private theorem C059_column_07 : reversePack 256 (fun j : Fin 14 => C059_digit j 7)=C059_columnCode 7 := by decide +kernel

private theorem C059_column_08 : reversePack 256 (fun j : Fin 14 => C059_digit j 8)=C059_columnCode 8 := by decide +kernel

private theorem C059_column_09 : reversePack 256 (fun j : Fin 14 => C059_digit j 9)=C059_columnCode 9 := by decide +kernel

private theorem C059_column_10 : reversePack 256 (fun j : Fin 14 => C059_digit j 10)=C059_columnCode 10 := by decide +kernel

private theorem C059_column_11 : reversePack 256 (fun j : Fin 14 => C059_digit j 11)=C059_columnCode 11 := by decide +kernel

private theorem C059_column_12 : reversePack 256 (fun j : Fin 14 => C059_digit j 12)=C059_columnCode 12 := by decide +kernel

private theorem C059_column_13 : reversePack 256 (fun j : Fin 14 => C059_digit j 13)=C059_columnCode 13 := by decide +kernel

theorem C059_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C059_digit j i)=C059_columnCode i := by
  intro i
  fin_cases i
  · exact C059_column_00
  · exact C059_column_01
  · exact C059_column_02
  · exact C059_column_03
  · exact C059_column_04
  · exact C059_column_05
  · exact C059_column_06
  · exact C059_column_07
  · exact C059_column_08
  · exact C059_column_09
  · exact C059_column_10
  · exact C059_column_11
  · exact C059_column_12
  · exact C059_column_13

def C059_data : PackedData 14 5 256 where
  raw := C059_digit
  digit_lt := C059_bound
  rowCode := C059_rowCode
  columnCode := C059_columnCode
  row_binding := C059_row_binding
  column_binding := C059_column_binding

def C063_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 618666428417
  | 1 => 1103288632834
  | 2 => 1925226430976
  | 3 => 278233350144
  | 4 => 1787836859915
  | 5 => 1048576
  | 6 => 3271688256
  | 7 => 1073741824
  | 8 => 1867237031936
  | 9 => 70866964480
  | 10 => 274886295552
  | 11 => 68719476736
  | 12 => 1653629517824
  | 13 => 2474974904320
  | _ => 0

def C063_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 12884902401
  | 1 => 4294967296
  | 2 => 281474976710656
  | 3 => 12884968196
  | 4 => 4722366482869645213696
  | 5 => 1125912791744769
  | 6 => 4398046773249
  | 7 => 4835703278458529583923459
  | 8 => 316912650057058194811990835459
  | 9 => 16778241
  | 10 => 20599322263208873874305159594752
  | 11 => 18446744073709551616
  | 12 => 81129952740097488214473859923969
  | 13 => 81367322902204814940803650748929
  | _ => 0

def C063_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 20282414439373468531859457573121
  | 1 => 40564822834099246718447454781442
  | 2 => 1208926108689430273328131
  | 3 => 4345299968
  | 4 => 60926460600302075533267432374787
  | 5 => 288230376151711744
  | 6 => 309485083608324662148202496
  | 7 => 16777216
  | 8 => 50397955
  | 9 => 4722366482869678768384
  | 10 => 1125899906843648
  | 11 => 256
  | 12 => 4398113619971
  | 13 => 16778244
  | _ => 0

def C063_digit (i j : Fin 14) : ℕ := packedDigit 3 (C063_lowColumnCode j) i.val

private theorem C063_bound_00 : ∀ j : Fin 14, C063_digit 0 j < 5 := by decide +kernel

private theorem C063_bound_01 : ∀ j : Fin 14, C063_digit 1 j < 5 := by decide +kernel

private theorem C063_bound_02 : ∀ j : Fin 14, C063_digit 2 j < 5 := by decide +kernel

private theorem C063_bound_03 : ∀ j : Fin 14, C063_digit 3 j < 5 := by decide +kernel

private theorem C063_bound_04 : ∀ j : Fin 14, C063_digit 4 j < 5 := by decide +kernel

private theorem C063_bound_05 : ∀ j : Fin 14, C063_digit 5 j < 5 := by decide +kernel

private theorem C063_bound_06 : ∀ j : Fin 14, C063_digit 6 j < 5 := by decide +kernel

private theorem C063_bound_07 : ∀ j : Fin 14, C063_digit 7 j < 5 := by decide +kernel

private theorem C063_bound_08 : ∀ j : Fin 14, C063_digit 8 j < 5 := by decide +kernel

private theorem C063_bound_09 : ∀ j : Fin 14, C063_digit 9 j < 5 := by decide +kernel

private theorem C063_bound_10 : ∀ j : Fin 14, C063_digit 10 j < 5 := by decide +kernel

private theorem C063_bound_11 : ∀ j : Fin 14, C063_digit 11 j < 5 := by decide +kernel

private theorem C063_bound_12 : ∀ j : Fin 14, C063_digit 12 j < 5 := by decide +kernel

private theorem C063_bound_13 : ∀ j : Fin 14, C063_digit 13 j < 5 := by decide +kernel

theorem C063_bound : ∀ i j : Fin 14, C063_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C063_bound_00 j
  · exact C063_bound_01 j
  · exact C063_bound_02 j
  · exact C063_bound_03 j
  · exact C063_bound_04 j
  · exact C063_bound_05 j
  · exact C063_bound_06 j
  · exact C063_bound_07 j
  · exact C063_bound_08 j
  · exact C063_bound_09 j
  · exact C063_bound_10 j
  · exact C063_bound_11 j
  · exact C063_bound_12 j
  · exact C063_bound_13 j

private theorem C063_row_00 : pack 256 (C063_digit 0)=C063_rowCode 0 := by decide +kernel

private theorem C063_row_01 : pack 256 (C063_digit 1)=C063_rowCode 1 := by decide +kernel

private theorem C063_row_02 : pack 256 (C063_digit 2)=C063_rowCode 2 := by decide +kernel

private theorem C063_row_03 : pack 256 (C063_digit 3)=C063_rowCode 3 := by decide +kernel

private theorem C063_row_04 : pack 256 (C063_digit 4)=C063_rowCode 4 := by decide +kernel

private theorem C063_row_05 : pack 256 (C063_digit 5)=C063_rowCode 5 := by decide +kernel

private theorem C063_row_06 : pack 256 (C063_digit 6)=C063_rowCode 6 := by decide +kernel

private theorem C063_row_07 : pack 256 (C063_digit 7)=C063_rowCode 7 := by decide +kernel

private theorem C063_row_08 : pack 256 (C063_digit 8)=C063_rowCode 8 := by decide +kernel

private theorem C063_row_09 : pack 256 (C063_digit 9)=C063_rowCode 9 := by decide +kernel

private theorem C063_row_10 : pack 256 (C063_digit 10)=C063_rowCode 10 := by decide +kernel

private theorem C063_row_11 : pack 256 (C063_digit 11)=C063_rowCode 11 := by decide +kernel

private theorem C063_row_12 : pack 256 (C063_digit 12)=C063_rowCode 12 := by decide +kernel

private theorem C063_row_13 : pack 256 (C063_digit 13)=C063_rowCode 13 := by decide +kernel

theorem C063_row_binding : ∀ i : Fin 14, pack 256 (C063_digit i)=C063_rowCode i := by
  intro i
  fin_cases i
  · exact C063_row_00
  · exact C063_row_01
  · exact C063_row_02
  · exact C063_row_03
  · exact C063_row_04
  · exact C063_row_05
  · exact C063_row_06
  · exact C063_row_07
  · exact C063_row_08
  · exact C063_row_09
  · exact C063_row_10
  · exact C063_row_11
  · exact C063_row_12
  · exact C063_row_13

private theorem C063_column_00 : reversePack 256 (fun j : Fin 14 => C063_digit j 0)=C063_columnCode 0 := by decide +kernel

private theorem C063_column_01 : reversePack 256 (fun j : Fin 14 => C063_digit j 1)=C063_columnCode 1 := by decide +kernel

private theorem C063_column_02 : reversePack 256 (fun j : Fin 14 => C063_digit j 2)=C063_columnCode 2 := by decide +kernel

private theorem C063_column_03 : reversePack 256 (fun j : Fin 14 => C063_digit j 3)=C063_columnCode 3 := by decide +kernel

private theorem C063_column_04 : reversePack 256 (fun j : Fin 14 => C063_digit j 4)=C063_columnCode 4 := by decide +kernel

private theorem C063_column_05 : reversePack 256 (fun j : Fin 14 => C063_digit j 5)=C063_columnCode 5 := by decide +kernel

private theorem C063_column_06 : reversePack 256 (fun j : Fin 14 => C063_digit j 6)=C063_columnCode 6 := by decide +kernel

private theorem C063_column_07 : reversePack 256 (fun j : Fin 14 => C063_digit j 7)=C063_columnCode 7 := by decide +kernel

private theorem C063_column_08 : reversePack 256 (fun j : Fin 14 => C063_digit j 8)=C063_columnCode 8 := by decide +kernel

private theorem C063_column_09 : reversePack 256 (fun j : Fin 14 => C063_digit j 9)=C063_columnCode 9 := by decide +kernel

private theorem C063_column_10 : reversePack 256 (fun j : Fin 14 => C063_digit j 10)=C063_columnCode 10 := by decide +kernel

private theorem C063_column_11 : reversePack 256 (fun j : Fin 14 => C063_digit j 11)=C063_columnCode 11 := by decide +kernel

private theorem C063_column_12 : reversePack 256 (fun j : Fin 14 => C063_digit j 12)=C063_columnCode 12 := by decide +kernel

private theorem C063_column_13 : reversePack 256 (fun j : Fin 14 => C063_digit j 13)=C063_columnCode 13 := by decide +kernel

theorem C063_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C063_digit j i)=C063_columnCode i := by
  intro i
  fin_cases i
  · exact C063_column_00
  · exact C063_column_01
  · exact C063_column_02
  · exact C063_column_03
  · exact C063_column_04
  · exact C063_column_05
  · exact C063_column_06
  · exact C063_column_07
  · exact C063_column_08
  · exact C063_column_09
  · exact C063_column_10
  · exact C063_column_11
  · exact C063_column_12
  · exact C063_column_13

def C063_data : PackedData 14 5 256 where
  raw := C063_digit
  digit_lt := C063_bound
  rowCode := C063_rowCode
  columnCode := C063_columnCode
  row_binding := C063_row_binding
  column_binding := C063_column_binding

end SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedCaches06
