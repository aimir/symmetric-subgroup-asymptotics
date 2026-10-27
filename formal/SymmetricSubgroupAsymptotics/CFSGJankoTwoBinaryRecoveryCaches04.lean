import SymmetricSubgroupAsymptotics.MatrixKroneckerProductReflection
import Mathlib.Tactic.FinCases

/-! Literal14/F5 selected caches; digit bounds and both pack bindings are independently kernel checked. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryCaches04
open MatrixKroneckerProductReflection MatrixKroneckerDotReflection
open MatrixNaturalRowDotReflection SmallNaturalMatrixProductReflection

def C020_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 157173548131
  | 1 => 1102924317337
  | 2 => 2347233986338
  | 3 => 2363776714467
  | 4 => 2444025958680
  | 5 => 836580029634
  | 6 => 2276523574033
  | 7 => 1875963613700
  | 8 => 1670797951499
  | 9 => 1101795460352
  | 10 => 1177935488258
  | 11 => 716243616897
  | 12 => 558959265304
  | 13 => 1748259840736
  | _ => 0

def C020_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 311902917089320598404989187
  | 1 => 81367322902167922015606252241668
  | 2 => 60847852635567399481190155289089
  | 3 => 20520715488528997407204770513154
  | 4 => 40566059565194337518324686258176
  | 5 => 238924850211569019945092121348
  | 6 => 40882973424251001459631464841729
  | 7 => 61165073547578324374354250433282
  | 8 => 81447481937600183387286715630336
  | 9 => 20599322258431166597363943866627
  | 10 => 81130568088080701463756328272642
  | 11 => 60927386637461597145197860421634
  | 12 => 20283029782597349187381931147266
  | 13 => 60926768885831026681521570578944
  | _ => 0

def C020_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 61164453363947388793394751996416
  | 1 => 20520714270195410936631522230274
  | 2 => 40882973443066824528890853130756
  | 3 => 61165073561782532643870147281412
  | 4 => 238922432323108359033850168068
  | 5 => 40565750094425546710049259324417
  | 6 => 20442105077682198429913592168708
  | 7 => 81129639628291833620508604236547
  | 8 => 60926458182450724252910308425731
  | 9 => 1240357909371635086263320578
  | 10 => 40566059574676108930720544653570
  | 11 => 20283031010486494329216136577537
  | 12 => 237688114375881449580569624577
  | 13 => 317842323457218929964230050051
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

def C021_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 218120652058
  | 1 => 2233584886874
  | 2 => 1404647815392
  | 3 => 1206085796609
  | 4 => 2237952820962
  | 5 => 206231868416
  | 6 => 1118906222620
  | 7 => 225502630417
  | 8 => 795139674320
  | 9 => 2364671903331
  | 10 => 553532916800
  | 11 => 716243616897
  | 12 => 2208737363467
  | 13 => 1748259840736
  | _ => 0

def C021_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 237993986719786989960843756034
  | 1 => 81208866596047450412638735172355
  | 2 => 60847848994678180291712104202500
  | 3 => 20520715493232917990438487720450
  | 4 => 40566057166250610962415308964352
  | 5 => 238927277471048286459566031106
  | 6 => 40566057161528172420852114129408
  | 7 => 60848158489077394373597492150272
  | 8 => 81368252570864091517314041840641
  | 9 => 20282414448873468824506702299393
  | 10 => 81209798668446533532665635930115
  | 11 => 60927385442739770747700522451969
  | 12 => 20283028583171602488125785636867
  | 13 => 61164452173855622820433286530048
  | _ => 0

def C021_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 40803744052773951959459659055872
  | 1 => 40802815607170918264405626191876
  | 2 => 317845954975491281170574017538
  | 3 => 20283648771524976887738361184514
  | 4 => 40882663939241108898090802479108
  | 5 => 2422592453305024680821504
  | 6 => 81367327737926540147779254222850
  | 7 => 20440867142365278685880123523840
  | 8 => 159384784798877997146925433601
  | 9 => 61164454591744371993187067298308
  | 10 => 311902935247833213630939137
  | 11 => 20283031010486494329216136577537
  | 12 => 60926460600302074688842502307844
  | 13 => 317842323457218929964230050051
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
  | 0 => 2414850623633
  | 1 => 2217331509474
  | 2 => 1864302113872
  | 3 => 644841353242
  | 4 => 1120215901473
  | 5 => 137460073984
  | 6 => 1172962295819
  | 7 => 311928946756
  | 8 => 1169574180556
  | 9 => 2413831127297
  | 10 => 1877054132868
  | 11 => 716243616897
  | 12 => 631553209481
  | 13 => 2199074472483
  | _ => 0

def C022_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 60926771298978817946990615200257
  | 1 => 81208866577139393058948465689602
  | 2 => 159077731844688815893814248194
  | 3 => 20441486107681001639429217059844
  | 4 => 238923636563239370212428153860
  | 5 => 61006925493930093023574664217344
  | 6 => 60848467974142700062781181526020
  | 7 => 317842332902023106669309854210
  | 8 => 61085842976620187947124775781120
  | 9 => 79229371477266515179876777984
  | 10 => 317845940808391829271626121473
  | 11 => 80159040118022315312504963585
  | 12 => 79850773497200578351331475459
  | 13 => 81209179707834586204923358282756
  | _ => 0

def C022_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 20441489753292874972593190404868
  | 1 => 40882665167037947421939766263812
  | 2 => 158768242075823673681060627203
  | 3 => 40802503709087165529982605918465
  | 4 => 20600562621118460558472619622402
  | 5 => 3645740712315710408229376
  | 6 => 60926456992358741543125853929730
  | 7 => 81129947899690434976782787806208
  | 8 => 81209798673150524766097032347906
  | 9 => 20283647543691173106202705986308
  | 10 => 81130258598311476311745582203651
  | 11 => 20283031010486494329216136577537
  | 12 => 20362259168241210746895752823041
  | 13 => 61164142669993444645146881687556
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
  | 0 => 1196301780172
  | 1 => 1119261345354
  | 2 => 1266117854289
  | 3 => 859182601811
  | 4 => 2494588584225
  | 5 => 1855463657472
  | 6 => 1808517317274
  | 7 => 2424565795096
  | 8 => 2370875196504
  | 9 => 829349013650
  | 10 => 792627650816
  | 11 => 1795301389824
  | 12 => 631553209481
  | 13 => 2199074472483
  | _ => 0

def C023_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 60926456982914009138128887022084
  | 1 => 81208866586621236248567225647361
  | 2 => 158461170195275636860088549635
  | 3 => 20441794402636311065817692373762
  | 4 => 238615369868630369983881544704
  | 5 => 61006308955892295519849955852545
  | 6 => 60848159698058554780103491977985
  | 7 => 317534037947002188824855183617
  | 8 => 61084918138979006759115247714561
  | 9 => 79229385607183963790214497025
  | 10 => 316915086798307752211973865986
  | 11 => 79542483301295795620492280323
  | 12 => 79850778237942030292366786561
  | 13 => 81209796245872672220499195068930
  | _ => 0

def C023_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 81209797450020568382093637386498
  | 1 => 40644360500513014505366106537986
  | 2 => 20441177850468020221190688932354
  | 3 => 61005998252567046218996395541505
  | 4 => 20600560193785194874228049052676
  | 5 => 4740813792092331442947
  | 6 => 40803123892681206216515119088131
  | 7 => 238927263359144675590566707972
  | 8 => 237996390422916788737041236484
  | 9 => 40723899347555080043590735365121
  | 10 => 1237949557950004849432331009
  | 11 => 3640981668516375946134019
  | 12 => 20362259168241210746895752823041
  | 13 => 61164142669993444645146881687556
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

end SymmetricSubgroupAsymptotics.CFSGJankoTwoBinaryRecoveryCaches04
