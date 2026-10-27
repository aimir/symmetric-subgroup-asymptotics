import SymmetricSubgroupAsymptotics.MatrixKroneckerProductReflection
import Mathlib.Tactic.FinCases

/-! Literal14/F5 selected caches; digit bounds and both pack bindings are independently kernel checked. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryCaches01
open MatrixKroneckerProductReflection MatrixKroneckerDotReflection
open MatrixNaturalRowDotReflection SmallNaturalMatrixProductReflection

def C007_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 860673278108
  | 1 => 1817367872768
  | 2 => 1718008459491
  | 3 => 1652488679424
  | 4 => 645319627456
  | 5 => 138513231872
  | 6 => 767863882786
  | 7 => 551903313920
  | 8 => 16777216
  | 9 => 134217728
  | 10 => 138800005268
  | 11 => 140661243904
  | 12 => 2476082991360
  | 13 => 549755813888
  | _ => 0

def C007_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 4835703279021466652442628
  | 1 => 2417851640355158256517123
  | 2 => 316915067908696579645410313218
  | 3 => 562954248389120
  | 4 => 80466102553837951547475165184
  | 5 => 562949953487360
  | 6 => 238922427582078395267439264768
  | 7 => 1208925820177579128259585
  | 8 => 158457533972795033889972224772
  | 9 => 2422574005993602971337732
  | 10 => 159385988983957285739299865601
  | 11 => 281487861613316
  | 12 => 317534037928340116398223196676
  | 13 => 20599322253708800113394787222273
  | _ => 0

def C007_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 81367941872169117684597306688513
  | 1 => 1240357928107457272508252675
  | 2 => 61165069930227223529342290100483
  | 3 => 14167099448608985972739
  | 4 => 929668677866305487125020929
  | 5 => 14167243563797028274688
  | 6 => 40881734275248931478628745675521
  | 7 => 18889465931478614409217
  | 8 => 1099511627776
  | 9 => 4294967296
  | 10 => 81288713709654853343696637657600
  | 11 => 18889754161854782898688
  | 12 => 1237944761868038125714932740
  | 13 => 1
  | _ => 0

def C007_digit (i j : Fin 14) : ℕ := packedDigit 3 (C007_lowColumnCode j) i.val

private theorem C007_bound_00 : ∀ j : Fin 14, C007_digit 0 j < 5 := by decide +kernel

private theorem C007_bound_01 : ∀ j : Fin 14, C007_digit 1 j < 5 := by decide +kernel

private theorem C007_bound_02 : ∀ j : Fin 14, C007_digit 2 j < 5 := by decide +kernel

private theorem C007_bound_03 : ∀ j : Fin 14, C007_digit 3 j < 5 := by decide +kernel

private theorem C007_bound_04 : ∀ j : Fin 14, C007_digit 4 j < 5 := by decide +kernel

private theorem C007_bound_05 : ∀ j : Fin 14, C007_digit 5 j < 5 := by decide +kernel

private theorem C007_bound_06 : ∀ j : Fin 14, C007_digit 6 j < 5 := by decide +kernel

private theorem C007_bound_07 : ∀ j : Fin 14, C007_digit 7 j < 5 := by decide +kernel

private theorem C007_bound_08 : ∀ j : Fin 14, C007_digit 8 j < 5 := by decide +kernel

private theorem C007_bound_09 : ∀ j : Fin 14, C007_digit 9 j < 5 := by decide +kernel

private theorem C007_bound_10 : ∀ j : Fin 14, C007_digit 10 j < 5 := by decide +kernel

private theorem C007_bound_11 : ∀ j : Fin 14, C007_digit 11 j < 5 := by decide +kernel

private theorem C007_bound_12 : ∀ j : Fin 14, C007_digit 12 j < 5 := by decide +kernel

private theorem C007_bound_13 : ∀ j : Fin 14, C007_digit 13 j < 5 := by decide +kernel

theorem C007_bound : ∀ i j : Fin 14, C007_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C007_bound_00 j
  · exact C007_bound_01 j
  · exact C007_bound_02 j
  · exact C007_bound_03 j
  · exact C007_bound_04 j
  · exact C007_bound_05 j
  · exact C007_bound_06 j
  · exact C007_bound_07 j
  · exact C007_bound_08 j
  · exact C007_bound_09 j
  · exact C007_bound_10 j
  · exact C007_bound_11 j
  · exact C007_bound_12 j
  · exact C007_bound_13 j

private theorem C007_row_00 : pack 256 (C007_digit 0)=C007_rowCode 0 := by decide +kernel

private theorem C007_row_01 : pack 256 (C007_digit 1)=C007_rowCode 1 := by decide +kernel

private theorem C007_row_02 : pack 256 (C007_digit 2)=C007_rowCode 2 := by decide +kernel

private theorem C007_row_03 : pack 256 (C007_digit 3)=C007_rowCode 3 := by decide +kernel

private theorem C007_row_04 : pack 256 (C007_digit 4)=C007_rowCode 4 := by decide +kernel

private theorem C007_row_05 : pack 256 (C007_digit 5)=C007_rowCode 5 := by decide +kernel

private theorem C007_row_06 : pack 256 (C007_digit 6)=C007_rowCode 6 := by decide +kernel

private theorem C007_row_07 : pack 256 (C007_digit 7)=C007_rowCode 7 := by decide +kernel

private theorem C007_row_08 : pack 256 (C007_digit 8)=C007_rowCode 8 := by decide +kernel

private theorem C007_row_09 : pack 256 (C007_digit 9)=C007_rowCode 9 := by decide +kernel

private theorem C007_row_10 : pack 256 (C007_digit 10)=C007_rowCode 10 := by decide +kernel

private theorem C007_row_11 : pack 256 (C007_digit 11)=C007_rowCode 11 := by decide +kernel

private theorem C007_row_12 : pack 256 (C007_digit 12)=C007_rowCode 12 := by decide +kernel

private theorem C007_row_13 : pack 256 (C007_digit 13)=C007_rowCode 13 := by decide +kernel

theorem C007_row_binding : ∀ i : Fin 14, pack 256 (C007_digit i)=C007_rowCode i := by
  intro i
  fin_cases i
  · exact C007_row_00
  · exact C007_row_01
  · exact C007_row_02
  · exact C007_row_03
  · exact C007_row_04
  · exact C007_row_05
  · exact C007_row_06
  · exact C007_row_07
  · exact C007_row_08
  · exact C007_row_09
  · exact C007_row_10
  · exact C007_row_11
  · exact C007_row_12
  · exact C007_row_13

private theorem C007_column_00 : reversePack 256 (fun j : Fin 14 => C007_digit j 0)=C007_columnCode 0 := by decide +kernel

private theorem C007_column_01 : reversePack 256 (fun j : Fin 14 => C007_digit j 1)=C007_columnCode 1 := by decide +kernel

private theorem C007_column_02 : reversePack 256 (fun j : Fin 14 => C007_digit j 2)=C007_columnCode 2 := by decide +kernel

private theorem C007_column_03 : reversePack 256 (fun j : Fin 14 => C007_digit j 3)=C007_columnCode 3 := by decide +kernel

private theorem C007_column_04 : reversePack 256 (fun j : Fin 14 => C007_digit j 4)=C007_columnCode 4 := by decide +kernel

private theorem C007_column_05 : reversePack 256 (fun j : Fin 14 => C007_digit j 5)=C007_columnCode 5 := by decide +kernel

private theorem C007_column_06 : reversePack 256 (fun j : Fin 14 => C007_digit j 6)=C007_columnCode 6 := by decide +kernel

private theorem C007_column_07 : reversePack 256 (fun j : Fin 14 => C007_digit j 7)=C007_columnCode 7 := by decide +kernel

private theorem C007_column_08 : reversePack 256 (fun j : Fin 14 => C007_digit j 8)=C007_columnCode 8 := by decide +kernel

private theorem C007_column_09 : reversePack 256 (fun j : Fin 14 => C007_digit j 9)=C007_columnCode 9 := by decide +kernel

private theorem C007_column_10 : reversePack 256 (fun j : Fin 14 => C007_digit j 10)=C007_columnCode 10 := by decide +kernel

private theorem C007_column_11 : reversePack 256 (fun j : Fin 14 => C007_digit j 11)=C007_columnCode 11 := by decide +kernel

private theorem C007_column_12 : reversePack 256 (fun j : Fin 14 => C007_digit j 12)=C007_columnCode 12 := by decide +kernel

private theorem C007_column_13 : reversePack 256 (fun j : Fin 14 => C007_digit j 13)=C007_columnCode 13 := by decide +kernel

theorem C007_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C007_digit j i)=C007_columnCode i := by
  intro i
  fin_cases i
  · exact C007_column_00
  · exact C007_column_01
  · exact C007_column_02
  · exact C007_column_03
  · exact C007_column_04
  · exact C007_column_05
  · exact C007_column_06
  · exact C007_column_07
  · exact C007_column_08
  · exact C007_column_09
  · exact C007_column_10
  · exact C007_column_11
  · exact C007_column_12
  · exact C007_column_13

def C007_data : PackedData 14 5 256 where
  raw := C007_digit
  digit_lt := C007_bound
  rowCode := C007_rowCode
  columnCode := C007_columnCode
  row_binding := C007_row_binding
  column_binding := C007_column_binding

def C008_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 2492743156369
  | 1 => 37883556962
  | 2 => 103404605705
  | 3 => 275452530979
  | 4 => 845106518024
  | 5 => 3779604643
  | 6 => 1308405669952
  | 7 => 138800005268
  | 8 => 67108864
  | 9 => 2199560126464
  | 10 => 224987203683
  | 11 => 210791579860
  | 12 => 1867777127443
  | 13 => 549755813888
  | _ => 0

def C008_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 238926054359825470617792086529
  | 1 => 159080130751593943431720797186
  | 2 => 929663955428048697492242690
  | 3 => 158461160731807133720966595073
  | 4 => 238927263285357417825029915392
  | 5 => 158456325028529801104174744068
  | 6 => 317534037928340116398223196676
  | 7 => 79540065375796971722303012864
  | 8 => 1240357964784488963780051459
  | 9 => 317536474669589675993001492996
  | 10 => 238923636507970631540116816641
  | 11 => 79230580365903566860483560450
  | 12 => 238616569349860851504583344132
  | 13 => 20520094110083929931160712380420
  | _ => 0

def C008_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 20441486107699736613887685035012
  | 1 => 40882043774425995826747846950912
  | 2 => 20362875710964553018158851817728
  | 3 => 61165379405773721050526630544384
  | 4 => 79233003013768880216814519297
  | 5 => 61164760445198955440217085968384
  | 6 => 309494528557463200715506434
  | 7 => 81288713709654853343696637657600
  | 8 => 4398046511104
  | 9 => 17179869188
  | 10 => 61164455800614779037634183430912
  | 11 => 81289023213554284738730604364544
  | 12 => 61005687568039460624911904604931
  | 13 => 1
  | _ => 0

def C008_digit (i j : Fin 14) : ℕ := packedDigit 3 (C008_lowColumnCode j) i.val

private theorem C008_bound_00 : ∀ j : Fin 14, C008_digit 0 j < 5 := by decide +kernel

private theorem C008_bound_01 : ∀ j : Fin 14, C008_digit 1 j < 5 := by decide +kernel

private theorem C008_bound_02 : ∀ j : Fin 14, C008_digit 2 j < 5 := by decide +kernel

private theorem C008_bound_03 : ∀ j : Fin 14, C008_digit 3 j < 5 := by decide +kernel

private theorem C008_bound_04 : ∀ j : Fin 14, C008_digit 4 j < 5 := by decide +kernel

private theorem C008_bound_05 : ∀ j : Fin 14, C008_digit 5 j < 5 := by decide +kernel

private theorem C008_bound_06 : ∀ j : Fin 14, C008_digit 6 j < 5 := by decide +kernel

private theorem C008_bound_07 : ∀ j : Fin 14, C008_digit 7 j < 5 := by decide +kernel

private theorem C008_bound_08 : ∀ j : Fin 14, C008_digit 8 j < 5 := by decide +kernel

private theorem C008_bound_09 : ∀ j : Fin 14, C008_digit 9 j < 5 := by decide +kernel

private theorem C008_bound_10 : ∀ j : Fin 14, C008_digit 10 j < 5 := by decide +kernel

private theorem C008_bound_11 : ∀ j : Fin 14, C008_digit 11 j < 5 := by decide +kernel

private theorem C008_bound_12 : ∀ j : Fin 14, C008_digit 12 j < 5 := by decide +kernel

private theorem C008_bound_13 : ∀ j : Fin 14, C008_digit 13 j < 5 := by decide +kernel

theorem C008_bound : ∀ i j : Fin 14, C008_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C008_bound_00 j
  · exact C008_bound_01 j
  · exact C008_bound_02 j
  · exact C008_bound_03 j
  · exact C008_bound_04 j
  · exact C008_bound_05 j
  · exact C008_bound_06 j
  · exact C008_bound_07 j
  · exact C008_bound_08 j
  · exact C008_bound_09 j
  · exact C008_bound_10 j
  · exact C008_bound_11 j
  · exact C008_bound_12 j
  · exact C008_bound_13 j

private theorem C008_row_00 : pack 256 (C008_digit 0)=C008_rowCode 0 := by decide +kernel

private theorem C008_row_01 : pack 256 (C008_digit 1)=C008_rowCode 1 := by decide +kernel

private theorem C008_row_02 : pack 256 (C008_digit 2)=C008_rowCode 2 := by decide +kernel

private theorem C008_row_03 : pack 256 (C008_digit 3)=C008_rowCode 3 := by decide +kernel

private theorem C008_row_04 : pack 256 (C008_digit 4)=C008_rowCode 4 := by decide +kernel

private theorem C008_row_05 : pack 256 (C008_digit 5)=C008_rowCode 5 := by decide +kernel

private theorem C008_row_06 : pack 256 (C008_digit 6)=C008_rowCode 6 := by decide +kernel

private theorem C008_row_07 : pack 256 (C008_digit 7)=C008_rowCode 7 := by decide +kernel

private theorem C008_row_08 : pack 256 (C008_digit 8)=C008_rowCode 8 := by decide +kernel

private theorem C008_row_09 : pack 256 (C008_digit 9)=C008_rowCode 9 := by decide +kernel

private theorem C008_row_10 : pack 256 (C008_digit 10)=C008_rowCode 10 := by decide +kernel

private theorem C008_row_11 : pack 256 (C008_digit 11)=C008_rowCode 11 := by decide +kernel

private theorem C008_row_12 : pack 256 (C008_digit 12)=C008_rowCode 12 := by decide +kernel

private theorem C008_row_13 : pack 256 (C008_digit 13)=C008_rowCode 13 := by decide +kernel

theorem C008_row_binding : ∀ i : Fin 14, pack 256 (C008_digit i)=C008_rowCode i := by
  intro i
  fin_cases i
  · exact C008_row_00
  · exact C008_row_01
  · exact C008_row_02
  · exact C008_row_03
  · exact C008_row_04
  · exact C008_row_05
  · exact C008_row_06
  · exact C008_row_07
  · exact C008_row_08
  · exact C008_row_09
  · exact C008_row_10
  · exact C008_row_11
  · exact C008_row_12
  · exact C008_row_13

private theorem C008_column_00 : reversePack 256 (fun j : Fin 14 => C008_digit j 0)=C008_columnCode 0 := by decide +kernel

private theorem C008_column_01 : reversePack 256 (fun j : Fin 14 => C008_digit j 1)=C008_columnCode 1 := by decide +kernel

private theorem C008_column_02 : reversePack 256 (fun j : Fin 14 => C008_digit j 2)=C008_columnCode 2 := by decide +kernel

private theorem C008_column_03 : reversePack 256 (fun j : Fin 14 => C008_digit j 3)=C008_columnCode 3 := by decide +kernel

private theorem C008_column_04 : reversePack 256 (fun j : Fin 14 => C008_digit j 4)=C008_columnCode 4 := by decide +kernel

private theorem C008_column_05 : reversePack 256 (fun j : Fin 14 => C008_digit j 5)=C008_columnCode 5 := by decide +kernel

private theorem C008_column_06 : reversePack 256 (fun j : Fin 14 => C008_digit j 6)=C008_columnCode 6 := by decide +kernel

private theorem C008_column_07 : reversePack 256 (fun j : Fin 14 => C008_digit j 7)=C008_columnCode 7 := by decide +kernel

private theorem C008_column_08 : reversePack 256 (fun j : Fin 14 => C008_digit j 8)=C008_columnCode 8 := by decide +kernel

private theorem C008_column_09 : reversePack 256 (fun j : Fin 14 => C008_digit j 9)=C008_columnCode 9 := by decide +kernel

private theorem C008_column_10 : reversePack 256 (fun j : Fin 14 => C008_digit j 10)=C008_columnCode 10 := by decide +kernel

private theorem C008_column_11 : reversePack 256 (fun j : Fin 14 => C008_digit j 11)=C008_columnCode 11 := by decide +kernel

private theorem C008_column_12 : reversePack 256 (fun j : Fin 14 => C008_digit j 12)=C008_columnCode 12 := by decide +kernel

private theorem C008_column_13 : reversePack 256 (fun j : Fin 14 => C008_digit j 13)=C008_columnCode 13 := by decide +kernel

theorem C008_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C008_digit j i)=C008_columnCode i := by
  intro i
  fin_cases i
  · exact C008_column_00
  · exact C008_column_01
  · exact C008_column_02
  · exact C008_column_03
  · exact C008_column_04
  · exact C008_column_05
  · exact C008_column_06
  · exact C008_column_07
  · exact C008_column_08
  · exact C008_column_09
  · exact C008_column_10
  · exact C008_column_11
  · exact C008_column_12
  · exact C008_column_13

def C008_data : PackedData 14 5 256 where
  raw := C008_digit
  digit_lt := C008_bound
  rowCode := C008_rowCode
  columnCode := C008_columnCode
  row_binding := C008_row_binding
  column_binding := C008_column_binding

def C009_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 2443224593432
  | 1 => 1728746461251
  | 2 => 1720438622340
  | 3 => 655569995296
  | 4 => 833815167747
  | 5 => 20988965016
  | 6 => 206297216155
  | 7 => 304072995419
  | 8 => 16777216
  | 9 => 134217728
  | 10 => 241733539018
  | 11 => 842124796433
  | 12 => 726185018496
  | 13 => 549755813888
  | _ => 0

def C009_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 311902861677591547003273984
  | 1 => 620178945679325272270176259
  | 2 => 158459951806060141834806624512
  | 3 => 158768227890061870062499005442
  | 4 => 620178945679325289450045699
  | 5 => 311902861677595945049785089
  | 6 => 933290732886892584965768194
  | 7 => 1241566816816844715004592644
  | 8 => 317531620095435018272956875011
  | 9 => 159076508696429806307665641475
  | 10 => 316913858983093141084032860675
  | 11 => 317536455780194674013823303940
  | 12 => 159697891845561974167789699331
  | 13 => 20361947251175756106613831959300
  | _ => 0

def C009_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 237686919580123679121079534340
  | 1 => 60847543136446106584943601713411
  | 2 => 81130262220403390104420615192835
  | 3 => 316916295724054186650067271937
  | 4 => 60848467978864922996711205438465
  | 5 => 238303471803466246325696331776
  | 6 => 61085534700591598505396535296768
  | 7 => 61085224006656029326215794066432
  | 8 => 1099511627776
  | 9 => 4294967296
  | 10 => 40644978247458257495775028445952
  | 11 => 20440867147069415724466147820545
  | 12 => 621387871281923802502791681
  | 13 => 1
  | _ => 0

def C009_digit (i j : Fin 14) : ℕ := packedDigit 3 (C009_lowColumnCode j) i.val

private theorem C009_bound_00 : ∀ j : Fin 14, C009_digit 0 j < 5 := by decide +kernel

private theorem C009_bound_01 : ∀ j : Fin 14, C009_digit 1 j < 5 := by decide +kernel

private theorem C009_bound_02 : ∀ j : Fin 14, C009_digit 2 j < 5 := by decide +kernel

private theorem C009_bound_03 : ∀ j : Fin 14, C009_digit 3 j < 5 := by decide +kernel

private theorem C009_bound_04 : ∀ j : Fin 14, C009_digit 4 j < 5 := by decide +kernel

private theorem C009_bound_05 : ∀ j : Fin 14, C009_digit 5 j < 5 := by decide +kernel

private theorem C009_bound_06 : ∀ j : Fin 14, C009_digit 6 j < 5 := by decide +kernel

private theorem C009_bound_07 : ∀ j : Fin 14, C009_digit 7 j < 5 := by decide +kernel

private theorem C009_bound_08 : ∀ j : Fin 14, C009_digit 8 j < 5 := by decide +kernel

private theorem C009_bound_09 : ∀ j : Fin 14, C009_digit 9 j < 5 := by decide +kernel

private theorem C009_bound_10 : ∀ j : Fin 14, C009_digit 10 j < 5 := by decide +kernel

private theorem C009_bound_11 : ∀ j : Fin 14, C009_digit 11 j < 5 := by decide +kernel

private theorem C009_bound_12 : ∀ j : Fin 14, C009_digit 12 j < 5 := by decide +kernel

private theorem C009_bound_13 : ∀ j : Fin 14, C009_digit 13 j < 5 := by decide +kernel

theorem C009_bound : ∀ i j : Fin 14, C009_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C009_bound_00 j
  · exact C009_bound_01 j
  · exact C009_bound_02 j
  · exact C009_bound_03 j
  · exact C009_bound_04 j
  · exact C009_bound_05 j
  · exact C009_bound_06 j
  · exact C009_bound_07 j
  · exact C009_bound_08 j
  · exact C009_bound_09 j
  · exact C009_bound_10 j
  · exact C009_bound_11 j
  · exact C009_bound_12 j
  · exact C009_bound_13 j

private theorem C009_row_00 : pack 256 (C009_digit 0)=C009_rowCode 0 := by decide +kernel

private theorem C009_row_01 : pack 256 (C009_digit 1)=C009_rowCode 1 := by decide +kernel

private theorem C009_row_02 : pack 256 (C009_digit 2)=C009_rowCode 2 := by decide +kernel

private theorem C009_row_03 : pack 256 (C009_digit 3)=C009_rowCode 3 := by decide +kernel

private theorem C009_row_04 : pack 256 (C009_digit 4)=C009_rowCode 4 := by decide +kernel

private theorem C009_row_05 : pack 256 (C009_digit 5)=C009_rowCode 5 := by decide +kernel

private theorem C009_row_06 : pack 256 (C009_digit 6)=C009_rowCode 6 := by decide +kernel

private theorem C009_row_07 : pack 256 (C009_digit 7)=C009_rowCode 7 := by decide +kernel

private theorem C009_row_08 : pack 256 (C009_digit 8)=C009_rowCode 8 := by decide +kernel

private theorem C009_row_09 : pack 256 (C009_digit 9)=C009_rowCode 9 := by decide +kernel

private theorem C009_row_10 : pack 256 (C009_digit 10)=C009_rowCode 10 := by decide +kernel

private theorem C009_row_11 : pack 256 (C009_digit 11)=C009_rowCode 11 := by decide +kernel

private theorem C009_row_12 : pack 256 (C009_digit 12)=C009_rowCode 12 := by decide +kernel

private theorem C009_row_13 : pack 256 (C009_digit 13)=C009_rowCode 13 := by decide +kernel

theorem C009_row_binding : ∀ i : Fin 14, pack 256 (C009_digit i)=C009_rowCode i := by
  intro i
  fin_cases i
  · exact C009_row_00
  · exact C009_row_01
  · exact C009_row_02
  · exact C009_row_03
  · exact C009_row_04
  · exact C009_row_05
  · exact C009_row_06
  · exact C009_row_07
  · exact C009_row_08
  · exact C009_row_09
  · exact C009_row_10
  · exact C009_row_11
  · exact C009_row_12
  · exact C009_row_13

private theorem C009_column_00 : reversePack 256 (fun j : Fin 14 => C009_digit j 0)=C009_columnCode 0 := by decide +kernel

private theorem C009_column_01 : reversePack 256 (fun j : Fin 14 => C009_digit j 1)=C009_columnCode 1 := by decide +kernel

private theorem C009_column_02 : reversePack 256 (fun j : Fin 14 => C009_digit j 2)=C009_columnCode 2 := by decide +kernel

private theorem C009_column_03 : reversePack 256 (fun j : Fin 14 => C009_digit j 3)=C009_columnCode 3 := by decide +kernel

private theorem C009_column_04 : reversePack 256 (fun j : Fin 14 => C009_digit j 4)=C009_columnCode 4 := by decide +kernel

private theorem C009_column_05 : reversePack 256 (fun j : Fin 14 => C009_digit j 5)=C009_columnCode 5 := by decide +kernel

private theorem C009_column_06 : reversePack 256 (fun j : Fin 14 => C009_digit j 6)=C009_columnCode 6 := by decide +kernel

private theorem C009_column_07 : reversePack 256 (fun j : Fin 14 => C009_digit j 7)=C009_columnCode 7 := by decide +kernel

private theorem C009_column_08 : reversePack 256 (fun j : Fin 14 => C009_digit j 8)=C009_columnCode 8 := by decide +kernel

private theorem C009_column_09 : reversePack 256 (fun j : Fin 14 => C009_digit j 9)=C009_columnCode 9 := by decide +kernel

private theorem C009_column_10 : reversePack 256 (fun j : Fin 14 => C009_digit j 10)=C009_columnCode 10 := by decide +kernel

private theorem C009_column_11 : reversePack 256 (fun j : Fin 14 => C009_digit j 11)=C009_columnCode 11 := by decide +kernel

private theorem C009_column_12 : reversePack 256 (fun j : Fin 14 => C009_digit j 12)=C009_columnCode 12 := by decide +kernel

private theorem C009_column_13 : reversePack 256 (fun j : Fin 14 => C009_digit j 13)=C009_columnCode 13 := by decide +kernel

theorem C009_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C009_digit j i)=C009_columnCode i := by
  intro i
  fin_cases i
  · exact C009_column_00
  · exact C009_column_01
  · exact C009_column_02
  · exact C009_column_03
  · exact C009_column_04
  · exact C009_column_05
  · exact C009_column_06
  · exact C009_column_07
  · exact C009_column_08
  · exact C009_column_09
  · exact C009_column_10
  · exact C009_column_11
  · exact C009_column_12
  · exact C009_column_13

def C009_data : PackedData 14 5 256 where
  raw := C009_digit
  digit_lt := C009_bound
  rowCode := C009_rowCode
  columnCode := C009_columnCode
  row_binding := C009_row_binding
  column_binding := C009_column_binding

def C010_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 1394162348744
  | 1 => 1189895255057
  | 2 => 11332045091
  | 3 => 723708557378
  | 4 => 37045290275
  | 5 => 1666587820066
  | 6 => 3360822363
  | 7 => 165912621836
  | 8 => 67108864
  | 9 => 2199560126464
  | 10 => 18524743316
  | 11 => 1745407488642
  | 12 => 27120738458
  | 13 => 549755813888
  | _ => 0

def C010_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 159080130751738900854260039936
  | 1 => 237686905394505148473175966209
  | 2 => 159077712900099106451212206083
  | 3 => 313111787352809508897554945
  | 4 => 159387197909848393925932614403
  | 5 => 237996390404470885806906671362
  | 6 => 79540065375870153025797751299
  | 7 => 317842314012413624052101612036
  | 8 => 618970093501724026325893890
  | 9 => 159696701809207729166737473795
  | 10 => 79538856450050256913073046530
  | 11 => 238615360424112452243539689986
  | 12 => 309485009965460256834191620
  | 13 => 20283338077570600393930558145026
  | _ => 0

def C010_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 80157840673758225079210214402
  | 1 => 20440868360717529202516260159746
  | 2 => 61165384255681280958750357782528
  | 3 => 40565133542183613002107863695873
  | 4 => 61165381837866534369915962654720
  | 5 => 40881731857360399042697903603715
  | 6 => 61085225206155707111444393754624
  | 7 => 81210105740308635106896465035776
  | 8 => 4398046511104
  | 9 => 17179869188
  | 10 => 81288717345914082755559435665408
  | 11 => 40565439400434422249578960191747
  | 12 => 40803122674365922932275554746368
  | 13 => 1
  | _ => 0

def C010_digit (i j : Fin 14) : ℕ := packedDigit 3 (C010_lowColumnCode j) i.val

private theorem C010_bound_00 : ∀ j : Fin 14, C010_digit 0 j < 5 := by decide +kernel

private theorem C010_bound_01 : ∀ j : Fin 14, C010_digit 1 j < 5 := by decide +kernel

private theorem C010_bound_02 : ∀ j : Fin 14, C010_digit 2 j < 5 := by decide +kernel

private theorem C010_bound_03 : ∀ j : Fin 14, C010_digit 3 j < 5 := by decide +kernel

private theorem C010_bound_04 : ∀ j : Fin 14, C010_digit 4 j < 5 := by decide +kernel

private theorem C010_bound_05 : ∀ j : Fin 14, C010_digit 5 j < 5 := by decide +kernel

private theorem C010_bound_06 : ∀ j : Fin 14, C010_digit 6 j < 5 := by decide +kernel

private theorem C010_bound_07 : ∀ j : Fin 14, C010_digit 7 j < 5 := by decide +kernel

private theorem C010_bound_08 : ∀ j : Fin 14, C010_digit 8 j < 5 := by decide +kernel

private theorem C010_bound_09 : ∀ j : Fin 14, C010_digit 9 j < 5 := by decide +kernel

private theorem C010_bound_10 : ∀ j : Fin 14, C010_digit 10 j < 5 := by decide +kernel

private theorem C010_bound_11 : ∀ j : Fin 14, C010_digit 11 j < 5 := by decide +kernel

private theorem C010_bound_12 : ∀ j : Fin 14, C010_digit 12 j < 5 := by decide +kernel

private theorem C010_bound_13 : ∀ j : Fin 14, C010_digit 13 j < 5 := by decide +kernel

theorem C010_bound : ∀ i j : Fin 14, C010_digit i j < 5 := by
  intro i j
  fin_cases i
  · exact C010_bound_00 j
  · exact C010_bound_01 j
  · exact C010_bound_02 j
  · exact C010_bound_03 j
  · exact C010_bound_04 j
  · exact C010_bound_05 j
  · exact C010_bound_06 j
  · exact C010_bound_07 j
  · exact C010_bound_08 j
  · exact C010_bound_09 j
  · exact C010_bound_10 j
  · exact C010_bound_11 j
  · exact C010_bound_12 j
  · exact C010_bound_13 j

private theorem C010_row_00 : pack 256 (C010_digit 0)=C010_rowCode 0 := by decide +kernel

private theorem C010_row_01 : pack 256 (C010_digit 1)=C010_rowCode 1 := by decide +kernel

private theorem C010_row_02 : pack 256 (C010_digit 2)=C010_rowCode 2 := by decide +kernel

private theorem C010_row_03 : pack 256 (C010_digit 3)=C010_rowCode 3 := by decide +kernel

private theorem C010_row_04 : pack 256 (C010_digit 4)=C010_rowCode 4 := by decide +kernel

private theorem C010_row_05 : pack 256 (C010_digit 5)=C010_rowCode 5 := by decide +kernel

private theorem C010_row_06 : pack 256 (C010_digit 6)=C010_rowCode 6 := by decide +kernel

private theorem C010_row_07 : pack 256 (C010_digit 7)=C010_rowCode 7 := by decide +kernel

private theorem C010_row_08 : pack 256 (C010_digit 8)=C010_rowCode 8 := by decide +kernel

private theorem C010_row_09 : pack 256 (C010_digit 9)=C010_rowCode 9 := by decide +kernel

private theorem C010_row_10 : pack 256 (C010_digit 10)=C010_rowCode 10 := by decide +kernel

private theorem C010_row_11 : pack 256 (C010_digit 11)=C010_rowCode 11 := by decide +kernel

private theorem C010_row_12 : pack 256 (C010_digit 12)=C010_rowCode 12 := by decide +kernel

private theorem C010_row_13 : pack 256 (C010_digit 13)=C010_rowCode 13 := by decide +kernel

theorem C010_row_binding : ∀ i : Fin 14, pack 256 (C010_digit i)=C010_rowCode i := by
  intro i
  fin_cases i
  · exact C010_row_00
  · exact C010_row_01
  · exact C010_row_02
  · exact C010_row_03
  · exact C010_row_04
  · exact C010_row_05
  · exact C010_row_06
  · exact C010_row_07
  · exact C010_row_08
  · exact C010_row_09
  · exact C010_row_10
  · exact C010_row_11
  · exact C010_row_12
  · exact C010_row_13

private theorem C010_column_00 : reversePack 256 (fun j : Fin 14 => C010_digit j 0)=C010_columnCode 0 := by decide +kernel

private theorem C010_column_01 : reversePack 256 (fun j : Fin 14 => C010_digit j 1)=C010_columnCode 1 := by decide +kernel

private theorem C010_column_02 : reversePack 256 (fun j : Fin 14 => C010_digit j 2)=C010_columnCode 2 := by decide +kernel

private theorem C010_column_03 : reversePack 256 (fun j : Fin 14 => C010_digit j 3)=C010_columnCode 3 := by decide +kernel

private theorem C010_column_04 : reversePack 256 (fun j : Fin 14 => C010_digit j 4)=C010_columnCode 4 := by decide +kernel

private theorem C010_column_05 : reversePack 256 (fun j : Fin 14 => C010_digit j 5)=C010_columnCode 5 := by decide +kernel

private theorem C010_column_06 : reversePack 256 (fun j : Fin 14 => C010_digit j 6)=C010_columnCode 6 := by decide +kernel

private theorem C010_column_07 : reversePack 256 (fun j : Fin 14 => C010_digit j 7)=C010_columnCode 7 := by decide +kernel

private theorem C010_column_08 : reversePack 256 (fun j : Fin 14 => C010_digit j 8)=C010_columnCode 8 := by decide +kernel

private theorem C010_column_09 : reversePack 256 (fun j : Fin 14 => C010_digit j 9)=C010_columnCode 9 := by decide +kernel

private theorem C010_column_10 : reversePack 256 (fun j : Fin 14 => C010_digit j 10)=C010_columnCode 10 := by decide +kernel

private theorem C010_column_11 : reversePack 256 (fun j : Fin 14 => C010_digit j 11)=C010_columnCode 11 := by decide +kernel

private theorem C010_column_12 : reversePack 256 (fun j : Fin 14 => C010_digit j 12)=C010_columnCode 12 := by decide +kernel

private theorem C010_column_13 : reversePack 256 (fun j : Fin 14 => C010_digit j 13)=C010_columnCode 13 := by decide +kernel

theorem C010_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => C010_digit j i)=C010_columnCode i := by
  intro i
  fin_cases i
  · exact C010_column_00
  · exact C010_column_01
  · exact C010_column_02
  · exact C010_column_03
  · exact C010_column_04
  · exact C010_column_05
  · exact C010_column_06
  · exact C010_column_07
  · exact C010_column_08
  · exact C010_column_09
  · exact C010_column_10
  · exact C010_column_11
  · exact C010_column_12
  · exact C010_column_13

def C010_data : PackedData 14 5 256 where
  raw := C010_digit
  digit_lt := C010_bound
  rowCode := C010_rowCode
  columnCode := C010_columnCode
  row_binding := C010_row_binding
  column_binding := C010_column_binding

end SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryCaches01
