import SymmetricSubgroupAsymptotics.MatrixKroneckerProductReflection
import Mathlib.Tactic.FinCases

/-! Literal14/F5 selected caches; digit bounds and both pack bindings are independently kernel checked. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryCaches07
open MatrixKroneckerProductReflection MatrixKroneckerDotReflection
open MatrixNaturalRowDotReflection SmallNaturalMatrixProductReflection

def C032_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 1687960794841
  | 1 => 2217283462336
  | 2 => 300923535651
  | 3 => 96787796680
  | 4 => 68720640291
  | 5 => 1675306010624
  | 6 => 223741363274
  | 7 => 835676316899
  | 8 => 137447342080
  | 9 => 137440002048
  | 10 => 8590532756
  | 11 => 27385731283
  | 12 => 309506708116
  | 13 => 68719476736
  | _ => 0

def C032_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 317845940790016579842001272833
  | 1 => 159077712900099106451212206083
  | 2 => 159387197909848393925932614403
  | 3 => 80466102553694400404535640579
  | 4 => 79540065375870153025797751299
  | 5 => 238305875414148117882300596483
  | 6 => 159696701809207729166737473795
  | 7 => 618970093501724026325893890
  | 8 => 144115188092633090
  | 9 => 159694265067959017274033176576
  | 10 => 309485009965460256834191620
  | 11 => 317842314012413624052101612036
  | 12 => 20599322263190643303013530468352
  | 13 => 72060892572812291
  | _ => 0

def C032_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 20521026187224042734582803726339
  | 1 => 930882344355876296508702724
  | 2 => 61165379419959555752852791165952
  | 3 => 80157831210361215476088111360
  | 4 => 61165379419996448396566690005248
  | 5 => 4835740244004266745987075
  | 6 => 40644359291642390725195462738688
  | 7 => 61165072343356640110552228627457
  | 8 => 1125899906843136
  | 9 => 288230376151712256
  | 10 => 81288713719136623630188328058880
  | 11 => 61006618431475831205112081219584
  | 12 => 81288714923358523506030157235200
  | 13 => 256
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
  | 0 => 1408959910090
  | 1 => 2199464248985
  | 2 => 2210873000452
  | 3 => 36516147740
  | 4 => 1205209182992
  | 5 => 2558854930
  | 6 => 163553580249
  | 7 => 18392293410
  | 8 => 1048576
  | 9 => 274886295552
  | 10 => 1127572121697
  | 11 => 27385731283
  | 12 => 783202522640
  | 13 => 68719476736
  | _ => 0

def C033_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 929663955428048697492242690
  | 1 => 159080130751738900849981653761
  | 2 => 929663955284498675505562115
  | 3 => 238927263285357417825029915392
  | 4 => 79540065375869308596606205953
  | 5 => 317534037928340116398223196676
  | 6 => 1240357964784488963780051459
  | 7 => 317536474669589675993001492996
  | 8 => 158456325028529801104174744068
  | 9 => 238923636507970631540116816641
  | 10 => 79540065375796971722303012864
  | 11 => 238616569349860851504583344132
  | 12 => 20520094110083929931160712380420
  | 13 => 79230580365903566860483560450
  | _ => 0

def C033_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 40644975829643439982943066653698
  | 1 => 20520716688028603139250213355524
  | 2 => 81129639642440630723901611114500
  | 3 => 81367324125242539012895763857408
  | 4 => 159695488179468097560923865346
  | 5 => 40724517099185580418898296045568
  | 6 => 20521024968853490719371838030336
  | 7 => 40881731866805203784556272025600
  | 8 => 288230376151711744
  | 9 => 1125899906843648
  | 10 => 20599636583903599272885871640578
  | 11 => 61006618431475831205112081219584
  | 12 => 158459956602142106350927414017
  | 13 => 256
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

end SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryCaches07
