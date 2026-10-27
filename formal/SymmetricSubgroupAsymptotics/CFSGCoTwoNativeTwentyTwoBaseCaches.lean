import SymmetricSubgroupAsymptotics.MatrixKroneckerProductReflection
import Mathlib.Tactic.FinCases

/-! Fixed Co2 binary22 shared caches. Every digit and pack binding is kernel checked. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoBaseCaches
open MatrixKroneckerProductReflection MatrixKroneckerDotReflection
open MatrixNaturalRowDotReflection SmallNaturalMatrixProductReflection

def A_lowColumnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 2114050
  | 1 => 2114049
  | 2 => 1048584
  | 3 => 1048580
  | 4 => 415936
  | 5 => 3150720
  | 6 => 415888
  | 7 => 128
  | 8 => 3150496
  | 9 => 512
  | 10 => 1024
  | 11 => 2048
  | 12 => 4096
  | 13 => 3473408
  | 14 => 16384
  | 15 => 917504
  | 16 => 3416064
  | 17 => 131072
  | 18 => 262144
  | 19 => 425984
  | 20 => 1048576
  | 21 => 2097152
  | _ => 0

def A_rowCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 32
  | 1 => 1
  | 2 => 32768
  | 3 => 1024
  | 4 => 1073741824
  | 5 => 1099511627776
  | 6 => 1048576
  | 7 => 1134979710976
  | 8 => 33554432
  | 9 => 36283917271073
  | 10 => 1125899906842624
  | 11 => 36028798093754368
  | 12 => 1152922605226819584
  | 13 => 1208925819614629174706176
  | 14 => 1180591620718486093857
  | 15 => 39614081257132168796771975168
  | 16 => 36893488147419103232
  | 17 => 39652804662291699888599072768
  | 18 => 40853268038062514806501408768
  | 19 => 37778931862957161709568
  | 20 => 1267651809190942505372842230784
  | 21 => 40564820416266053951770641563681
  | _ => 0

def A_columnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1267650600229382323035669790721
  | 1 => 40564819207304493769433469157377
  | 2 => 1237940039285380274899124256
  | 3 => 39614081257132168796771975200
  | 4 => 38959524644793212764160
  | 5 => 1218638065553809342497
  | 6 => 38686806820449969641652224
  | 7 => 1180591620717411303424
  | 8 => 1210107564192035564945441
  | 9 => 1152921504606846976
  | 10 => 36028797018963968
  | 11 => 1125899906842624
  | 12 => 35184372088832
  | 13 => 33587233
  | 14 => 34359738368
  | 15 => 1082368
  | 16 => 1099511660577
  | 17 => 1048576
  | 18 => 32768
  | 19 => 1074823168
  | 20 => 32
  | 21 => 1
  | _ => 0

def A_digit (i j : Fin 22) : ℕ := packedDigit 1 (A_lowColumnCode j) i.val

private theorem A_bound_00 : ∀ j : Fin 22,A_digit 0 j<2 := by decide +kernel

private theorem A_bound_01 : ∀ j : Fin 22,A_digit 1 j<2 := by decide +kernel

private theorem A_bound_02 : ∀ j : Fin 22,A_digit 2 j<2 := by decide +kernel

private theorem A_bound_03 : ∀ j : Fin 22,A_digit 3 j<2 := by decide +kernel

private theorem A_bound_04 : ∀ j : Fin 22,A_digit 4 j<2 := by decide +kernel

private theorem A_bound_05 : ∀ j : Fin 22,A_digit 5 j<2 := by decide +kernel

private theorem A_bound_06 : ∀ j : Fin 22,A_digit 6 j<2 := by decide +kernel

private theorem A_bound_07 : ∀ j : Fin 22,A_digit 7 j<2 := by decide +kernel

private theorem A_bound_08 : ∀ j : Fin 22,A_digit 8 j<2 := by decide +kernel

private theorem A_bound_09 : ∀ j : Fin 22,A_digit 9 j<2 := by decide +kernel

private theorem A_bound_10 : ∀ j : Fin 22,A_digit 10 j<2 := by decide +kernel

private theorem A_bound_11 : ∀ j : Fin 22,A_digit 11 j<2 := by decide +kernel

private theorem A_bound_12 : ∀ j : Fin 22,A_digit 12 j<2 := by decide +kernel

private theorem A_bound_13 : ∀ j : Fin 22,A_digit 13 j<2 := by decide +kernel

private theorem A_bound_14 : ∀ j : Fin 22,A_digit 14 j<2 := by decide +kernel

private theorem A_bound_15 : ∀ j : Fin 22,A_digit 15 j<2 := by decide +kernel

private theorem A_bound_16 : ∀ j : Fin 22,A_digit 16 j<2 := by decide +kernel

private theorem A_bound_17 : ∀ j : Fin 22,A_digit 17 j<2 := by decide +kernel

private theorem A_bound_18 : ∀ j : Fin 22,A_digit 18 j<2 := by decide +kernel

private theorem A_bound_19 : ∀ j : Fin 22,A_digit 19 j<2 := by decide +kernel

private theorem A_bound_20 : ∀ j : Fin 22,A_digit 20 j<2 := by decide +kernel

private theorem A_bound_21 : ∀ j : Fin 22,A_digit 21 j<2 := by decide +kernel

theorem A_bound : ∀ i j : Fin 22,A_digit i j<2 := by
  intro i j
  fin_cases i
  · exact A_bound_00 j
  · exact A_bound_01 j
  · exact A_bound_02 j
  · exact A_bound_03 j
  · exact A_bound_04 j
  · exact A_bound_05 j
  · exact A_bound_06 j
  · exact A_bound_07 j
  · exact A_bound_08 j
  · exact A_bound_09 j
  · exact A_bound_10 j
  · exact A_bound_11 j
  · exact A_bound_12 j
  · exact A_bound_13 j
  · exact A_bound_14 j
  · exact A_bound_15 j
  · exact A_bound_16 j
  · exact A_bound_17 j
  · exact A_bound_18 j
  · exact A_bound_19 j
  · exact A_bound_20 j
  · exact A_bound_21 j

private theorem A_row_00 : pack 32 (A_digit 0)=A_rowCode 0 := by decide +kernel

private theorem A_row_01 : pack 32 (A_digit 1)=A_rowCode 1 := by decide +kernel

private theorem A_row_02 : pack 32 (A_digit 2)=A_rowCode 2 := by decide +kernel

private theorem A_row_03 : pack 32 (A_digit 3)=A_rowCode 3 := by decide +kernel

private theorem A_row_04 : pack 32 (A_digit 4)=A_rowCode 4 := by decide +kernel

private theorem A_row_05 : pack 32 (A_digit 5)=A_rowCode 5 := by decide +kernel

private theorem A_row_06 : pack 32 (A_digit 6)=A_rowCode 6 := by decide +kernel

private theorem A_row_07 : pack 32 (A_digit 7)=A_rowCode 7 := by decide +kernel

private theorem A_row_08 : pack 32 (A_digit 8)=A_rowCode 8 := by decide +kernel

private theorem A_row_09 : pack 32 (A_digit 9)=A_rowCode 9 := by decide +kernel

private theorem A_row_10 : pack 32 (A_digit 10)=A_rowCode 10 := by decide +kernel

private theorem A_row_11 : pack 32 (A_digit 11)=A_rowCode 11 := by decide +kernel

private theorem A_row_12 : pack 32 (A_digit 12)=A_rowCode 12 := by decide +kernel

private theorem A_row_13 : pack 32 (A_digit 13)=A_rowCode 13 := by decide +kernel

private theorem A_row_14 : pack 32 (A_digit 14)=A_rowCode 14 := by decide +kernel

private theorem A_row_15 : pack 32 (A_digit 15)=A_rowCode 15 := by decide +kernel

private theorem A_row_16 : pack 32 (A_digit 16)=A_rowCode 16 := by decide +kernel

private theorem A_row_17 : pack 32 (A_digit 17)=A_rowCode 17 := by decide +kernel

private theorem A_row_18 : pack 32 (A_digit 18)=A_rowCode 18 := by decide +kernel

private theorem A_row_19 : pack 32 (A_digit 19)=A_rowCode 19 := by decide +kernel

private theorem A_row_20 : pack 32 (A_digit 20)=A_rowCode 20 := by decide +kernel

private theorem A_row_21 : pack 32 (A_digit 21)=A_rowCode 21 := by decide +kernel

theorem A_row_binding : ∀ i : Fin 22,pack 32 (A_digit i)=A_rowCode i := by
  intro i
  fin_cases i
  · exact A_row_00
  · exact A_row_01
  · exact A_row_02
  · exact A_row_03
  · exact A_row_04
  · exact A_row_05
  · exact A_row_06
  · exact A_row_07
  · exact A_row_08
  · exact A_row_09
  · exact A_row_10
  · exact A_row_11
  · exact A_row_12
  · exact A_row_13
  · exact A_row_14
  · exact A_row_15
  · exact A_row_16
  · exact A_row_17
  · exact A_row_18
  · exact A_row_19
  · exact A_row_20
  · exact A_row_21

private theorem A_column_00 : reversePack 32 (fun j : Fin 22 => A_digit j 0)=A_columnCode 0 := by decide +kernel

private theorem A_column_01 : reversePack 32 (fun j : Fin 22 => A_digit j 1)=A_columnCode 1 := by decide +kernel

private theorem A_column_02 : reversePack 32 (fun j : Fin 22 => A_digit j 2)=A_columnCode 2 := by decide +kernel

private theorem A_column_03 : reversePack 32 (fun j : Fin 22 => A_digit j 3)=A_columnCode 3 := by decide +kernel

private theorem A_column_04 : reversePack 32 (fun j : Fin 22 => A_digit j 4)=A_columnCode 4 := by decide +kernel

private theorem A_column_05 : reversePack 32 (fun j : Fin 22 => A_digit j 5)=A_columnCode 5 := by decide +kernel

private theorem A_column_06 : reversePack 32 (fun j : Fin 22 => A_digit j 6)=A_columnCode 6 := by decide +kernel

private theorem A_column_07 : reversePack 32 (fun j : Fin 22 => A_digit j 7)=A_columnCode 7 := by decide +kernel

private theorem A_column_08 : reversePack 32 (fun j : Fin 22 => A_digit j 8)=A_columnCode 8 := by decide +kernel

private theorem A_column_09 : reversePack 32 (fun j : Fin 22 => A_digit j 9)=A_columnCode 9 := by decide +kernel

private theorem A_column_10 : reversePack 32 (fun j : Fin 22 => A_digit j 10)=A_columnCode 10 := by decide +kernel

private theorem A_column_11 : reversePack 32 (fun j : Fin 22 => A_digit j 11)=A_columnCode 11 := by decide +kernel

private theorem A_column_12 : reversePack 32 (fun j : Fin 22 => A_digit j 12)=A_columnCode 12 := by decide +kernel

private theorem A_column_13 : reversePack 32 (fun j : Fin 22 => A_digit j 13)=A_columnCode 13 := by decide +kernel

private theorem A_column_14 : reversePack 32 (fun j : Fin 22 => A_digit j 14)=A_columnCode 14 := by decide +kernel

private theorem A_column_15 : reversePack 32 (fun j : Fin 22 => A_digit j 15)=A_columnCode 15 := by decide +kernel

private theorem A_column_16 : reversePack 32 (fun j : Fin 22 => A_digit j 16)=A_columnCode 16 := by decide +kernel

private theorem A_column_17 : reversePack 32 (fun j : Fin 22 => A_digit j 17)=A_columnCode 17 := by decide +kernel

private theorem A_column_18 : reversePack 32 (fun j : Fin 22 => A_digit j 18)=A_columnCode 18 := by decide +kernel

private theorem A_column_19 : reversePack 32 (fun j : Fin 22 => A_digit j 19)=A_columnCode 19 := by decide +kernel

private theorem A_column_20 : reversePack 32 (fun j : Fin 22 => A_digit j 20)=A_columnCode 20 := by decide +kernel

private theorem A_column_21 : reversePack 32 (fun j : Fin 22 => A_digit j 21)=A_columnCode 21 := by decide +kernel

theorem A_column_binding : ∀ i : Fin 22,reversePack 32 (fun j : Fin 22 => A_digit j i)=A_columnCode i := by
  intro i
  fin_cases i
  · exact A_column_00
  · exact A_column_01
  · exact A_column_02
  · exact A_column_03
  · exact A_column_04
  · exact A_column_05
  · exact A_column_06
  · exact A_column_07
  · exact A_column_08
  · exact A_column_09
  · exact A_column_10
  · exact A_column_11
  · exact A_column_12
  · exact A_column_13
  · exact A_column_14
  · exact A_column_15
  · exact A_column_16
  · exact A_column_17
  · exact A_column_18
  · exact A_column_19
  · exact A_column_20
  · exact A_column_21

def A_data : PackedData 22 2 32 where
  raw := A_digit
  digit_lt := A_bound
  rowCode := A_rowCode
  columnCode := A_columnCode
  row_binding := A_row_binding
  column_binding := A_column_binding

def rowsA : Array String := #["0100000000000000000000",
  "1000000000000000000000",
  "0001000000000000000000",
  "0010000000000000000000",
  "0000001000000000000000",
  "0000000010000000000000",
  "0000100000000000000000",
  "0000111110000000000000",
  "0000010000000000000000",
  "1100010011000000000000",
  "0000000000100000000000",
  "0000101000010000000000",
  "0000111010001000000000",
  "0000000000000000100000",
  "1100101000000010000000",
  "0000000000000000000100",
  "0000000000000100000000",
  "0000101000000001010100",
  "0000101000000101101100",
  "0000000000000001000000",
  "0011010010000100100010",
  "1100010010000100100001"]

def matrixA : Matrix (Fin 22) (Fin 22) (ZMod 2) := CFSG.Models.MatrixData.matrix 2 22 rowsA

private theorem A_source_row_00 : ∀ j : Fin 22,rawDigit rowsA 0 j.val=A_digit 0 j := by decide +kernel

private theorem A_source_row_01 : ∀ j : Fin 22,rawDigit rowsA 1 j.val=A_digit 1 j := by decide +kernel

private theorem A_source_row_02 : ∀ j : Fin 22,rawDigit rowsA 2 j.val=A_digit 2 j := by decide +kernel

private theorem A_source_row_03 : ∀ j : Fin 22,rawDigit rowsA 3 j.val=A_digit 3 j := by decide +kernel

private theorem A_source_row_04 : ∀ j : Fin 22,rawDigit rowsA 4 j.val=A_digit 4 j := by decide +kernel

private theorem A_source_row_05 : ∀ j : Fin 22,rawDigit rowsA 5 j.val=A_digit 5 j := by decide +kernel

private theorem A_source_row_06 : ∀ j : Fin 22,rawDigit rowsA 6 j.val=A_digit 6 j := by decide +kernel

private theorem A_source_row_07 : ∀ j : Fin 22,rawDigit rowsA 7 j.val=A_digit 7 j := by decide +kernel

private theorem A_source_row_08 : ∀ j : Fin 22,rawDigit rowsA 8 j.val=A_digit 8 j := by decide +kernel

private theorem A_source_row_09 : ∀ j : Fin 22,rawDigit rowsA 9 j.val=A_digit 9 j := by decide +kernel

private theorem A_source_row_10 : ∀ j : Fin 22,rawDigit rowsA 10 j.val=A_digit 10 j := by decide +kernel

private theorem A_source_row_11 : ∀ j : Fin 22,rawDigit rowsA 11 j.val=A_digit 11 j := by decide +kernel

private theorem A_source_row_12 : ∀ j : Fin 22,rawDigit rowsA 12 j.val=A_digit 12 j := by decide +kernel

private theorem A_source_row_13 : ∀ j : Fin 22,rawDigit rowsA 13 j.val=A_digit 13 j := by decide +kernel

private theorem A_source_row_14 : ∀ j : Fin 22,rawDigit rowsA 14 j.val=A_digit 14 j := by decide +kernel

private theorem A_source_row_15 : ∀ j : Fin 22,rawDigit rowsA 15 j.val=A_digit 15 j := by decide +kernel

private theorem A_source_row_16 : ∀ j : Fin 22,rawDigit rowsA 16 j.val=A_digit 16 j := by decide +kernel

private theorem A_source_row_17 : ∀ j : Fin 22,rawDigit rowsA 17 j.val=A_digit 17 j := by decide +kernel

private theorem A_source_row_18 : ∀ j : Fin 22,rawDigit rowsA 18 j.val=A_digit 18 j := by decide +kernel

private theorem A_source_row_19 : ∀ j : Fin 22,rawDigit rowsA 19 j.val=A_digit 19 j := by decide +kernel

private theorem A_source_row_20 : ∀ j : Fin 22,rawDigit rowsA 20 j.val=A_digit 20 j := by decide +kernel

private theorem A_source_row_21 : ∀ j : Fin 22,rawDigit rowsA 21 j.val=A_digit 21 j := by decide +kernel

theorem A_source_digits : ∀ i j : Fin 22,rawDigit rowsA i.val j.val=A_digit i j := by
  intro i j
  fin_cases i
  · exact A_source_row_00 j
  · exact A_source_row_01 j
  · exact A_source_row_02 j
  · exact A_source_row_03 j
  · exact A_source_row_04 j
  · exact A_source_row_05 j
  · exact A_source_row_06 j
  · exact A_source_row_07 j
  · exact A_source_row_08 j
  · exact A_source_row_09 j
  · exact A_source_row_10 j
  · exact A_source_row_11 j
  · exact A_source_row_12 j
  · exact A_source_row_13 j
  · exact A_source_row_14 j
  · exact A_source_row_15 j
  · exact A_source_row_16 j
  · exact A_source_row_17 j
  · exact A_source_row_18 j
  · exact A_source_row_19 j
  · exact A_source_row_20 j
  · exact A_source_row_21 j

theorem A_source_binding : matrixA=A_data.matrix 2 := by
  ext i j
  change (rawDigit rowsA i.val j.val : ZMod 2)=(A_digit i j : ZMod 2)
  exact congrArg (fun x : ℕ => (x : ZMod 2)) (A_source_digits i j)

def B_lowColumnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 2097280
  | 1 => 2097154
  | 2 => 2097283
  | 3 => 3047424
  | 4 => 2621572
  | 5 => 3014664
  | 6 => 655360
  | 7 => 2621584
  | 8 => 2883584
  | 9 => 3014688
  | 10 => 2228288
  | 11 => 2359552
  | 12 => 3015168
  | 13 => 2753536
  | 14 => 2361344
  | 15 => 3018752
  | 16 => 2097152
  | 17 => 2760704
  | 18 => 802816
  | 19 => 2621440
  | 20 => 2686976
  | 21 => 1048576
  | _ => 0

def B_rowCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1024
  | 1 => 1056
  | 2 => 1048576
  | 3 => 33554432
  | 4 => 34359738368
  | 5 => 35184372088832
  | 6 => 1125899906842624
  | 7 => 34360787969
  | 8 => 36028797018963968
  | 9 => 1152921504606846976
  | 10 => 36893488147419103232
  | 11 => 1180591620717411303424
  | 12 => 37778931862957161709568
  | 13 => 38685626227668133590597632
  | 14 => 1237940039285380274899124224
  | 15 => 32768
  | 16 => 1267650600228229401496703205376
  | 17 => 38723443207101828164517888
  | 18 => 1237978999997850535015251968
  | 19 => 1308541344967852927630504394752
  | 20 => 40564819207303340847894502572032
  | 21 => 1307304615035015937398043345953
  | _ => 0

def B_columnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1180591620717411303425
  | 1 => 1267650600228229401496703205377
  | 2 => 41832469808712161870108617080833
  | 3 => 1074824193
  | 4 => 39614082437723789514183279617
  | 5 => 1237940039285380274900206593
  | 6 => 1049600
  | 7 => 38686806819288851001902081
  | 8 => 33793
  | 9 => 1208925819614629175788545
  | 10 => 37778931862957162758145
  | 11 => 36893488147419136001
  | 12 => 1152921504607929345
  | 13 => 36028797020013569
  | 14 => 1125899906875393
  | 15 => 35184373171201
  | 16 => 1
  | 17 => 1099512677377
  | 18 => 34359772160
  | 19 => 1025
  | 20 => 33555457
  | 21 => 32
  | _ => 0

def B_digit (i j : Fin 22) : ℕ := packedDigit 1 (B_lowColumnCode j) i.val

private theorem B_bound_00 : ∀ j : Fin 22,B_digit 0 j<2 := by decide +kernel

private theorem B_bound_01 : ∀ j : Fin 22,B_digit 1 j<2 := by decide +kernel

private theorem B_bound_02 : ∀ j : Fin 22,B_digit 2 j<2 := by decide +kernel

private theorem B_bound_03 : ∀ j : Fin 22,B_digit 3 j<2 := by decide +kernel

private theorem B_bound_04 : ∀ j : Fin 22,B_digit 4 j<2 := by decide +kernel

private theorem B_bound_05 : ∀ j : Fin 22,B_digit 5 j<2 := by decide +kernel

private theorem B_bound_06 : ∀ j : Fin 22,B_digit 6 j<2 := by decide +kernel

private theorem B_bound_07 : ∀ j : Fin 22,B_digit 7 j<2 := by decide +kernel

private theorem B_bound_08 : ∀ j : Fin 22,B_digit 8 j<2 := by decide +kernel

private theorem B_bound_09 : ∀ j : Fin 22,B_digit 9 j<2 := by decide +kernel

private theorem B_bound_10 : ∀ j : Fin 22,B_digit 10 j<2 := by decide +kernel

private theorem B_bound_11 : ∀ j : Fin 22,B_digit 11 j<2 := by decide +kernel

private theorem B_bound_12 : ∀ j : Fin 22,B_digit 12 j<2 := by decide +kernel

private theorem B_bound_13 : ∀ j : Fin 22,B_digit 13 j<2 := by decide +kernel

private theorem B_bound_14 : ∀ j : Fin 22,B_digit 14 j<2 := by decide +kernel

private theorem B_bound_15 : ∀ j : Fin 22,B_digit 15 j<2 := by decide +kernel

private theorem B_bound_16 : ∀ j : Fin 22,B_digit 16 j<2 := by decide +kernel

private theorem B_bound_17 : ∀ j : Fin 22,B_digit 17 j<2 := by decide +kernel

private theorem B_bound_18 : ∀ j : Fin 22,B_digit 18 j<2 := by decide +kernel

private theorem B_bound_19 : ∀ j : Fin 22,B_digit 19 j<2 := by decide +kernel

private theorem B_bound_20 : ∀ j : Fin 22,B_digit 20 j<2 := by decide +kernel

private theorem B_bound_21 : ∀ j : Fin 22,B_digit 21 j<2 := by decide +kernel

theorem B_bound : ∀ i j : Fin 22,B_digit i j<2 := by
  intro i j
  fin_cases i
  · exact B_bound_00 j
  · exact B_bound_01 j
  · exact B_bound_02 j
  · exact B_bound_03 j
  · exact B_bound_04 j
  · exact B_bound_05 j
  · exact B_bound_06 j
  · exact B_bound_07 j
  · exact B_bound_08 j
  · exact B_bound_09 j
  · exact B_bound_10 j
  · exact B_bound_11 j
  · exact B_bound_12 j
  · exact B_bound_13 j
  · exact B_bound_14 j
  · exact B_bound_15 j
  · exact B_bound_16 j
  · exact B_bound_17 j
  · exact B_bound_18 j
  · exact B_bound_19 j
  · exact B_bound_20 j
  · exact B_bound_21 j

private theorem B_row_00 : pack 32 (B_digit 0)=B_rowCode 0 := by decide +kernel

private theorem B_row_01 : pack 32 (B_digit 1)=B_rowCode 1 := by decide +kernel

private theorem B_row_02 : pack 32 (B_digit 2)=B_rowCode 2 := by decide +kernel

private theorem B_row_03 : pack 32 (B_digit 3)=B_rowCode 3 := by decide +kernel

private theorem B_row_04 : pack 32 (B_digit 4)=B_rowCode 4 := by decide +kernel

private theorem B_row_05 : pack 32 (B_digit 5)=B_rowCode 5 := by decide +kernel

private theorem B_row_06 : pack 32 (B_digit 6)=B_rowCode 6 := by decide +kernel

private theorem B_row_07 : pack 32 (B_digit 7)=B_rowCode 7 := by decide +kernel

private theorem B_row_08 : pack 32 (B_digit 8)=B_rowCode 8 := by decide +kernel

private theorem B_row_09 : pack 32 (B_digit 9)=B_rowCode 9 := by decide +kernel

private theorem B_row_10 : pack 32 (B_digit 10)=B_rowCode 10 := by decide +kernel

private theorem B_row_11 : pack 32 (B_digit 11)=B_rowCode 11 := by decide +kernel

private theorem B_row_12 : pack 32 (B_digit 12)=B_rowCode 12 := by decide +kernel

private theorem B_row_13 : pack 32 (B_digit 13)=B_rowCode 13 := by decide +kernel

private theorem B_row_14 : pack 32 (B_digit 14)=B_rowCode 14 := by decide +kernel

private theorem B_row_15 : pack 32 (B_digit 15)=B_rowCode 15 := by decide +kernel

private theorem B_row_16 : pack 32 (B_digit 16)=B_rowCode 16 := by decide +kernel

private theorem B_row_17 : pack 32 (B_digit 17)=B_rowCode 17 := by decide +kernel

private theorem B_row_18 : pack 32 (B_digit 18)=B_rowCode 18 := by decide +kernel

private theorem B_row_19 : pack 32 (B_digit 19)=B_rowCode 19 := by decide +kernel

private theorem B_row_20 : pack 32 (B_digit 20)=B_rowCode 20 := by decide +kernel

private theorem B_row_21 : pack 32 (B_digit 21)=B_rowCode 21 := by decide +kernel

theorem B_row_binding : ∀ i : Fin 22,pack 32 (B_digit i)=B_rowCode i := by
  intro i
  fin_cases i
  · exact B_row_00
  · exact B_row_01
  · exact B_row_02
  · exact B_row_03
  · exact B_row_04
  · exact B_row_05
  · exact B_row_06
  · exact B_row_07
  · exact B_row_08
  · exact B_row_09
  · exact B_row_10
  · exact B_row_11
  · exact B_row_12
  · exact B_row_13
  · exact B_row_14
  · exact B_row_15
  · exact B_row_16
  · exact B_row_17
  · exact B_row_18
  · exact B_row_19
  · exact B_row_20
  · exact B_row_21

private theorem B_column_00 : reversePack 32 (fun j : Fin 22 => B_digit j 0)=B_columnCode 0 := by decide +kernel

private theorem B_column_01 : reversePack 32 (fun j : Fin 22 => B_digit j 1)=B_columnCode 1 := by decide +kernel

private theorem B_column_02 : reversePack 32 (fun j : Fin 22 => B_digit j 2)=B_columnCode 2 := by decide +kernel

private theorem B_column_03 : reversePack 32 (fun j : Fin 22 => B_digit j 3)=B_columnCode 3 := by decide +kernel

private theorem B_column_04 : reversePack 32 (fun j : Fin 22 => B_digit j 4)=B_columnCode 4 := by decide +kernel

private theorem B_column_05 : reversePack 32 (fun j : Fin 22 => B_digit j 5)=B_columnCode 5 := by decide +kernel

private theorem B_column_06 : reversePack 32 (fun j : Fin 22 => B_digit j 6)=B_columnCode 6 := by decide +kernel

private theorem B_column_07 : reversePack 32 (fun j : Fin 22 => B_digit j 7)=B_columnCode 7 := by decide +kernel

private theorem B_column_08 : reversePack 32 (fun j : Fin 22 => B_digit j 8)=B_columnCode 8 := by decide +kernel

private theorem B_column_09 : reversePack 32 (fun j : Fin 22 => B_digit j 9)=B_columnCode 9 := by decide +kernel

private theorem B_column_10 : reversePack 32 (fun j : Fin 22 => B_digit j 10)=B_columnCode 10 := by decide +kernel

private theorem B_column_11 : reversePack 32 (fun j : Fin 22 => B_digit j 11)=B_columnCode 11 := by decide +kernel

private theorem B_column_12 : reversePack 32 (fun j : Fin 22 => B_digit j 12)=B_columnCode 12 := by decide +kernel

private theorem B_column_13 : reversePack 32 (fun j : Fin 22 => B_digit j 13)=B_columnCode 13 := by decide +kernel

private theorem B_column_14 : reversePack 32 (fun j : Fin 22 => B_digit j 14)=B_columnCode 14 := by decide +kernel

private theorem B_column_15 : reversePack 32 (fun j : Fin 22 => B_digit j 15)=B_columnCode 15 := by decide +kernel

private theorem B_column_16 : reversePack 32 (fun j : Fin 22 => B_digit j 16)=B_columnCode 16 := by decide +kernel

private theorem B_column_17 : reversePack 32 (fun j : Fin 22 => B_digit j 17)=B_columnCode 17 := by decide +kernel

private theorem B_column_18 : reversePack 32 (fun j : Fin 22 => B_digit j 18)=B_columnCode 18 := by decide +kernel

private theorem B_column_19 : reversePack 32 (fun j : Fin 22 => B_digit j 19)=B_columnCode 19 := by decide +kernel

private theorem B_column_20 : reversePack 32 (fun j : Fin 22 => B_digit j 20)=B_columnCode 20 := by decide +kernel

private theorem B_column_21 : reversePack 32 (fun j : Fin 22 => B_digit j 21)=B_columnCode 21 := by decide +kernel

theorem B_column_binding : ∀ i : Fin 22,reversePack 32 (fun j : Fin 22 => B_digit j i)=B_columnCode i := by
  intro i
  fin_cases i
  · exact B_column_00
  · exact B_column_01
  · exact B_column_02
  · exact B_column_03
  · exact B_column_04
  · exact B_column_05
  · exact B_column_06
  · exact B_column_07
  · exact B_column_08
  · exact B_column_09
  · exact B_column_10
  · exact B_column_11
  · exact B_column_12
  · exact B_column_13
  · exact B_column_14
  · exact B_column_15
  · exact B_column_16
  · exact B_column_17
  · exact B_column_18
  · exact B_column_19
  · exact B_column_20
  · exact B_column_21

def B_data : PackedData 22 2 32 where
  raw := B_digit
  digit_lt := B_bound
  rowCode := B_rowCode
  columnCode := B_columnCode
  row_binding := B_row_binding
  column_binding := B_column_binding

def rowsB : Array String := #["0010000000000000000000",
  "0110000000000000000000",
  "0000100000000000000000",
  "0000010000000000000000",
  "0000000100000000000000",
  "0000000001000000000000",
  "0000000000100000000000",
  "1010100100000000000000",
  "0000000000010000000000",
  "0000000000001000000000",
  "0000000000000100000000",
  "0000000000000010000000",
  "0000000000000001000000",
  "0000000000000000010000",
  "0000000000000000001000",
  "0001000000000000000000",
  "0000000000000000000010",
  "0001011001101101010000",
  "0001010011011011001000",
  "0001111111001101011110",
  "0000000000000000000001",
  "1111110111111111110110"]

def matrixB : Matrix (Fin 22) (Fin 22) (ZMod 2) := CFSG.Models.MatrixData.matrix 2 22 rowsB

private theorem B_source_row_00 : ∀ j : Fin 22,rawDigit rowsB 0 j.val=B_digit 0 j := by decide +kernel

private theorem B_source_row_01 : ∀ j : Fin 22,rawDigit rowsB 1 j.val=B_digit 1 j := by decide +kernel

private theorem B_source_row_02 : ∀ j : Fin 22,rawDigit rowsB 2 j.val=B_digit 2 j := by decide +kernel

private theorem B_source_row_03 : ∀ j : Fin 22,rawDigit rowsB 3 j.val=B_digit 3 j := by decide +kernel

private theorem B_source_row_04 : ∀ j : Fin 22,rawDigit rowsB 4 j.val=B_digit 4 j := by decide +kernel

private theorem B_source_row_05 : ∀ j : Fin 22,rawDigit rowsB 5 j.val=B_digit 5 j := by decide +kernel

private theorem B_source_row_06 : ∀ j : Fin 22,rawDigit rowsB 6 j.val=B_digit 6 j := by decide +kernel

private theorem B_source_row_07 : ∀ j : Fin 22,rawDigit rowsB 7 j.val=B_digit 7 j := by decide +kernel

private theorem B_source_row_08 : ∀ j : Fin 22,rawDigit rowsB 8 j.val=B_digit 8 j := by decide +kernel

private theorem B_source_row_09 : ∀ j : Fin 22,rawDigit rowsB 9 j.val=B_digit 9 j := by decide +kernel

private theorem B_source_row_10 : ∀ j : Fin 22,rawDigit rowsB 10 j.val=B_digit 10 j := by decide +kernel

private theorem B_source_row_11 : ∀ j : Fin 22,rawDigit rowsB 11 j.val=B_digit 11 j := by decide +kernel

private theorem B_source_row_12 : ∀ j : Fin 22,rawDigit rowsB 12 j.val=B_digit 12 j := by decide +kernel

private theorem B_source_row_13 : ∀ j : Fin 22,rawDigit rowsB 13 j.val=B_digit 13 j := by decide +kernel

private theorem B_source_row_14 : ∀ j : Fin 22,rawDigit rowsB 14 j.val=B_digit 14 j := by decide +kernel

private theorem B_source_row_15 : ∀ j : Fin 22,rawDigit rowsB 15 j.val=B_digit 15 j := by decide +kernel

private theorem B_source_row_16 : ∀ j : Fin 22,rawDigit rowsB 16 j.val=B_digit 16 j := by decide +kernel

private theorem B_source_row_17 : ∀ j : Fin 22,rawDigit rowsB 17 j.val=B_digit 17 j := by decide +kernel

private theorem B_source_row_18 : ∀ j : Fin 22,rawDigit rowsB 18 j.val=B_digit 18 j := by decide +kernel

private theorem B_source_row_19 : ∀ j : Fin 22,rawDigit rowsB 19 j.val=B_digit 19 j := by decide +kernel

private theorem B_source_row_20 : ∀ j : Fin 22,rawDigit rowsB 20 j.val=B_digit 20 j := by decide +kernel

private theorem B_source_row_21 : ∀ j : Fin 22,rawDigit rowsB 21 j.val=B_digit 21 j := by decide +kernel

theorem B_source_digits : ∀ i j : Fin 22,rawDigit rowsB i.val j.val=B_digit i j := by
  intro i j
  fin_cases i
  · exact B_source_row_00 j
  · exact B_source_row_01 j
  · exact B_source_row_02 j
  · exact B_source_row_03 j
  · exact B_source_row_04 j
  · exact B_source_row_05 j
  · exact B_source_row_06 j
  · exact B_source_row_07 j
  · exact B_source_row_08 j
  · exact B_source_row_09 j
  · exact B_source_row_10 j
  · exact B_source_row_11 j
  · exact B_source_row_12 j
  · exact B_source_row_13 j
  · exact B_source_row_14 j
  · exact B_source_row_15 j
  · exact B_source_row_16 j
  · exact B_source_row_17 j
  · exact B_source_row_18 j
  · exact B_source_row_19 j
  · exact B_source_row_20 j
  · exact B_source_row_21 j

theorem B_source_binding : matrixB=B_data.matrix 2 := by
  ext i j
  change (rawDigit rowsB i.val j.val : ZMod 2)=(B_digit i j : ZMod 2)
  exact congrArg (fun x : ℕ => (x : ZMod 2)) (B_source_digits i j)

def I_lowColumnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1
  | 1 => 2
  | 2 => 4
  | 3 => 8
  | 4 => 16
  | 5 => 32
  | 6 => 64
  | 7 => 128
  | 8 => 256
  | 9 => 512
  | 10 => 1024
  | 11 => 2048
  | 12 => 4096
  | 13 => 8192
  | 14 => 16384
  | 15 => 32768
  | 16 => 65536
  | 17 => 131072
  | 18 => 262144
  | 19 => 524288
  | 20 => 1048576
  | 21 => 2097152
  | _ => 0

def I_rowCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1
  | 1 => 32
  | 2 => 1024
  | 3 => 32768
  | 4 => 1048576
  | 5 => 33554432
  | 6 => 1073741824
  | 7 => 34359738368
  | 8 => 1099511627776
  | 9 => 35184372088832
  | 10 => 1125899906842624
  | 11 => 36028797018963968
  | 12 => 1152921504606846976
  | 13 => 36893488147419103232
  | 14 => 1180591620717411303424
  | 15 => 37778931862957161709568
  | 16 => 1208925819614629174706176
  | 17 => 38685626227668133590597632
  | 18 => 1237940039285380274899124224
  | 19 => 39614081257132168796771975168
  | 20 => 1267650600228229401496703205376
  | 21 => 40564819207303340847894502572032
  | _ => 0

def I_columnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 40564819207303340847894502572032
  | 1 => 1267650600228229401496703205376
  | 2 => 39614081257132168796771975168
  | 3 => 1237940039285380274899124224
  | 4 => 38685626227668133590597632
  | 5 => 1208925819614629174706176
  | 6 => 37778931862957161709568
  | 7 => 1180591620717411303424
  | 8 => 36893488147419103232
  | 9 => 1152921504606846976
  | 10 => 36028797018963968
  | 11 => 1125899906842624
  | 12 => 35184372088832
  | 13 => 1099511627776
  | 14 => 34359738368
  | 15 => 1073741824
  | 16 => 33554432
  | 17 => 1048576
  | 18 => 32768
  | 19 => 1024
  | 20 => 32
  | 21 => 1
  | _ => 0

def I_digit (i j : Fin 22) : ℕ := packedDigit 1 (I_lowColumnCode j) i.val

private theorem I_bound_00 : ∀ j : Fin 22,I_digit 0 j<2 := by decide +kernel

private theorem I_bound_01 : ∀ j : Fin 22,I_digit 1 j<2 := by decide +kernel

private theorem I_bound_02 : ∀ j : Fin 22,I_digit 2 j<2 := by decide +kernel

private theorem I_bound_03 : ∀ j : Fin 22,I_digit 3 j<2 := by decide +kernel

private theorem I_bound_04 : ∀ j : Fin 22,I_digit 4 j<2 := by decide +kernel

private theorem I_bound_05 : ∀ j : Fin 22,I_digit 5 j<2 := by decide +kernel

private theorem I_bound_06 : ∀ j : Fin 22,I_digit 6 j<2 := by decide +kernel

private theorem I_bound_07 : ∀ j : Fin 22,I_digit 7 j<2 := by decide +kernel

private theorem I_bound_08 : ∀ j : Fin 22,I_digit 8 j<2 := by decide +kernel

private theorem I_bound_09 : ∀ j : Fin 22,I_digit 9 j<2 := by decide +kernel

private theorem I_bound_10 : ∀ j : Fin 22,I_digit 10 j<2 := by decide +kernel

private theorem I_bound_11 : ∀ j : Fin 22,I_digit 11 j<2 := by decide +kernel

private theorem I_bound_12 : ∀ j : Fin 22,I_digit 12 j<2 := by decide +kernel

private theorem I_bound_13 : ∀ j : Fin 22,I_digit 13 j<2 := by decide +kernel

private theorem I_bound_14 : ∀ j : Fin 22,I_digit 14 j<2 := by decide +kernel

private theorem I_bound_15 : ∀ j : Fin 22,I_digit 15 j<2 := by decide +kernel

private theorem I_bound_16 : ∀ j : Fin 22,I_digit 16 j<2 := by decide +kernel

private theorem I_bound_17 : ∀ j : Fin 22,I_digit 17 j<2 := by decide +kernel

private theorem I_bound_18 : ∀ j : Fin 22,I_digit 18 j<2 := by decide +kernel

private theorem I_bound_19 : ∀ j : Fin 22,I_digit 19 j<2 := by decide +kernel

private theorem I_bound_20 : ∀ j : Fin 22,I_digit 20 j<2 := by decide +kernel

private theorem I_bound_21 : ∀ j : Fin 22,I_digit 21 j<2 := by decide +kernel

theorem I_bound : ∀ i j : Fin 22,I_digit i j<2 := by
  intro i j
  fin_cases i
  · exact I_bound_00 j
  · exact I_bound_01 j
  · exact I_bound_02 j
  · exact I_bound_03 j
  · exact I_bound_04 j
  · exact I_bound_05 j
  · exact I_bound_06 j
  · exact I_bound_07 j
  · exact I_bound_08 j
  · exact I_bound_09 j
  · exact I_bound_10 j
  · exact I_bound_11 j
  · exact I_bound_12 j
  · exact I_bound_13 j
  · exact I_bound_14 j
  · exact I_bound_15 j
  · exact I_bound_16 j
  · exact I_bound_17 j
  · exact I_bound_18 j
  · exact I_bound_19 j
  · exact I_bound_20 j
  · exact I_bound_21 j

private theorem I_row_00 : pack 32 (I_digit 0)=I_rowCode 0 := by decide +kernel

private theorem I_row_01 : pack 32 (I_digit 1)=I_rowCode 1 := by decide +kernel

private theorem I_row_02 : pack 32 (I_digit 2)=I_rowCode 2 := by decide +kernel

private theorem I_row_03 : pack 32 (I_digit 3)=I_rowCode 3 := by decide +kernel

private theorem I_row_04 : pack 32 (I_digit 4)=I_rowCode 4 := by decide +kernel

private theorem I_row_05 : pack 32 (I_digit 5)=I_rowCode 5 := by decide +kernel

private theorem I_row_06 : pack 32 (I_digit 6)=I_rowCode 6 := by decide +kernel

private theorem I_row_07 : pack 32 (I_digit 7)=I_rowCode 7 := by decide +kernel

private theorem I_row_08 : pack 32 (I_digit 8)=I_rowCode 8 := by decide +kernel

private theorem I_row_09 : pack 32 (I_digit 9)=I_rowCode 9 := by decide +kernel

private theorem I_row_10 : pack 32 (I_digit 10)=I_rowCode 10 := by decide +kernel

private theorem I_row_11 : pack 32 (I_digit 11)=I_rowCode 11 := by decide +kernel

private theorem I_row_12 : pack 32 (I_digit 12)=I_rowCode 12 := by decide +kernel

private theorem I_row_13 : pack 32 (I_digit 13)=I_rowCode 13 := by decide +kernel

private theorem I_row_14 : pack 32 (I_digit 14)=I_rowCode 14 := by decide +kernel

private theorem I_row_15 : pack 32 (I_digit 15)=I_rowCode 15 := by decide +kernel

private theorem I_row_16 : pack 32 (I_digit 16)=I_rowCode 16 := by decide +kernel

private theorem I_row_17 : pack 32 (I_digit 17)=I_rowCode 17 := by decide +kernel

private theorem I_row_18 : pack 32 (I_digit 18)=I_rowCode 18 := by decide +kernel

private theorem I_row_19 : pack 32 (I_digit 19)=I_rowCode 19 := by decide +kernel

private theorem I_row_20 : pack 32 (I_digit 20)=I_rowCode 20 := by decide +kernel

private theorem I_row_21 : pack 32 (I_digit 21)=I_rowCode 21 := by decide +kernel

theorem I_row_binding : ∀ i : Fin 22,pack 32 (I_digit i)=I_rowCode i := by
  intro i
  fin_cases i
  · exact I_row_00
  · exact I_row_01
  · exact I_row_02
  · exact I_row_03
  · exact I_row_04
  · exact I_row_05
  · exact I_row_06
  · exact I_row_07
  · exact I_row_08
  · exact I_row_09
  · exact I_row_10
  · exact I_row_11
  · exact I_row_12
  · exact I_row_13
  · exact I_row_14
  · exact I_row_15
  · exact I_row_16
  · exact I_row_17
  · exact I_row_18
  · exact I_row_19
  · exact I_row_20
  · exact I_row_21

private theorem I_column_00 : reversePack 32 (fun j : Fin 22 => I_digit j 0)=I_columnCode 0 := by decide +kernel

private theorem I_column_01 : reversePack 32 (fun j : Fin 22 => I_digit j 1)=I_columnCode 1 := by decide +kernel

private theorem I_column_02 : reversePack 32 (fun j : Fin 22 => I_digit j 2)=I_columnCode 2 := by decide +kernel

private theorem I_column_03 : reversePack 32 (fun j : Fin 22 => I_digit j 3)=I_columnCode 3 := by decide +kernel

private theorem I_column_04 : reversePack 32 (fun j : Fin 22 => I_digit j 4)=I_columnCode 4 := by decide +kernel

private theorem I_column_05 : reversePack 32 (fun j : Fin 22 => I_digit j 5)=I_columnCode 5 := by decide +kernel

private theorem I_column_06 : reversePack 32 (fun j : Fin 22 => I_digit j 6)=I_columnCode 6 := by decide +kernel

private theorem I_column_07 : reversePack 32 (fun j : Fin 22 => I_digit j 7)=I_columnCode 7 := by decide +kernel

private theorem I_column_08 : reversePack 32 (fun j : Fin 22 => I_digit j 8)=I_columnCode 8 := by decide +kernel

private theorem I_column_09 : reversePack 32 (fun j : Fin 22 => I_digit j 9)=I_columnCode 9 := by decide +kernel

private theorem I_column_10 : reversePack 32 (fun j : Fin 22 => I_digit j 10)=I_columnCode 10 := by decide +kernel

private theorem I_column_11 : reversePack 32 (fun j : Fin 22 => I_digit j 11)=I_columnCode 11 := by decide +kernel

private theorem I_column_12 : reversePack 32 (fun j : Fin 22 => I_digit j 12)=I_columnCode 12 := by decide +kernel

private theorem I_column_13 : reversePack 32 (fun j : Fin 22 => I_digit j 13)=I_columnCode 13 := by decide +kernel

private theorem I_column_14 : reversePack 32 (fun j : Fin 22 => I_digit j 14)=I_columnCode 14 := by decide +kernel

private theorem I_column_15 : reversePack 32 (fun j : Fin 22 => I_digit j 15)=I_columnCode 15 := by decide +kernel

private theorem I_column_16 : reversePack 32 (fun j : Fin 22 => I_digit j 16)=I_columnCode 16 := by decide +kernel

private theorem I_column_17 : reversePack 32 (fun j : Fin 22 => I_digit j 17)=I_columnCode 17 := by decide +kernel

private theorem I_column_18 : reversePack 32 (fun j : Fin 22 => I_digit j 18)=I_columnCode 18 := by decide +kernel

private theorem I_column_19 : reversePack 32 (fun j : Fin 22 => I_digit j 19)=I_columnCode 19 := by decide +kernel

private theorem I_column_20 : reversePack 32 (fun j : Fin 22 => I_digit j 20)=I_columnCode 20 := by decide +kernel

private theorem I_column_21 : reversePack 32 (fun j : Fin 22 => I_digit j 21)=I_columnCode 21 := by decide +kernel

theorem I_column_binding : ∀ i : Fin 22,reversePack 32 (fun j : Fin 22 => I_digit j i)=I_columnCode i := by
  intro i
  fin_cases i
  · exact I_column_00
  · exact I_column_01
  · exact I_column_02
  · exact I_column_03
  · exact I_column_04
  · exact I_column_05
  · exact I_column_06
  · exact I_column_07
  · exact I_column_08
  · exact I_column_09
  · exact I_column_10
  · exact I_column_11
  · exact I_column_12
  · exact I_column_13
  · exact I_column_14
  · exact I_column_15
  · exact I_column_16
  · exact I_column_17
  · exact I_column_18
  · exact I_column_19
  · exact I_column_20
  · exact I_column_21

def I_data : PackedData 22 2 32 where
  raw := I_digit
  digit_lt := I_bound
  rowCode := I_rowCode
  columnCode := I_columnCode
  row_binding := I_row_binding
  column_binding := I_column_binding

private theorem I_one_00 : ∀ j : Fin 22,I_digit 0 j=(1 : Matrix (Fin 22) (Fin 22) ℕ) 0 j := by decide +kernel

private theorem I_one_01 : ∀ j : Fin 22,I_digit 1 j=(1 : Matrix (Fin 22) (Fin 22) ℕ) 1 j := by decide +kernel

private theorem I_one_02 : ∀ j : Fin 22,I_digit 2 j=(1 : Matrix (Fin 22) (Fin 22) ℕ) 2 j := by decide +kernel

private theorem I_one_03 : ∀ j : Fin 22,I_digit 3 j=(1 : Matrix (Fin 22) (Fin 22) ℕ) 3 j := by decide +kernel

private theorem I_one_04 : ∀ j : Fin 22,I_digit 4 j=(1 : Matrix (Fin 22) (Fin 22) ℕ) 4 j := by decide +kernel

private theorem I_one_05 : ∀ j : Fin 22,I_digit 5 j=(1 : Matrix (Fin 22) (Fin 22) ℕ) 5 j := by decide +kernel

private theorem I_one_06 : ∀ j : Fin 22,I_digit 6 j=(1 : Matrix (Fin 22) (Fin 22) ℕ) 6 j := by decide +kernel

private theorem I_one_07 : ∀ j : Fin 22,I_digit 7 j=(1 : Matrix (Fin 22) (Fin 22) ℕ) 7 j := by decide +kernel

private theorem I_one_08 : ∀ j : Fin 22,I_digit 8 j=(1 : Matrix (Fin 22) (Fin 22) ℕ) 8 j := by decide +kernel

private theorem I_one_09 : ∀ j : Fin 22,I_digit 9 j=(1 : Matrix (Fin 22) (Fin 22) ℕ) 9 j := by decide +kernel

private theorem I_one_10 : ∀ j : Fin 22,I_digit 10 j=(1 : Matrix (Fin 22) (Fin 22) ℕ) 10 j := by decide +kernel

private theorem I_one_11 : ∀ j : Fin 22,I_digit 11 j=(1 : Matrix (Fin 22) (Fin 22) ℕ) 11 j := by decide +kernel

private theorem I_one_12 : ∀ j : Fin 22,I_digit 12 j=(1 : Matrix (Fin 22) (Fin 22) ℕ) 12 j := by decide +kernel

private theorem I_one_13 : ∀ j : Fin 22,I_digit 13 j=(1 : Matrix (Fin 22) (Fin 22) ℕ) 13 j := by decide +kernel

private theorem I_one_14 : ∀ j : Fin 22,I_digit 14 j=(1 : Matrix (Fin 22) (Fin 22) ℕ) 14 j := by decide +kernel

private theorem I_one_15 : ∀ j : Fin 22,I_digit 15 j=(1 : Matrix (Fin 22) (Fin 22) ℕ) 15 j := by decide +kernel

private theorem I_one_16 : ∀ j : Fin 22,I_digit 16 j=(1 : Matrix (Fin 22) (Fin 22) ℕ) 16 j := by decide +kernel

private theorem I_one_17 : ∀ j : Fin 22,I_digit 17 j=(1 : Matrix (Fin 22) (Fin 22) ℕ) 17 j := by decide +kernel

private theorem I_one_18 : ∀ j : Fin 22,I_digit 18 j=(1 : Matrix (Fin 22) (Fin 22) ℕ) 18 j := by decide +kernel

private theorem I_one_19 : ∀ j : Fin 22,I_digit 19 j=(1 : Matrix (Fin 22) (Fin 22) ℕ) 19 j := by decide +kernel

private theorem I_one_20 : ∀ j : Fin 22,I_digit 20 j=(1 : Matrix (Fin 22) (Fin 22) ℕ) 20 j := by decide +kernel

private theorem I_one_21 : ∀ j : Fin 22,I_digit 21 j=(1 : Matrix (Fin 22) (Fin 22) ℕ) 21 j := by decide +kernel

theorem I_raw_one : I_digit=(1 : Matrix (Fin 22) (Fin 22) ℕ) := by
  funext i
  fin_cases i
  · exact funext I_one_00
  · exact funext I_one_01
  · exact funext I_one_02
  · exact funext I_one_03
  · exact funext I_one_04
  · exact funext I_one_05
  · exact funext I_one_06
  · exact funext I_one_07
  · exact funext I_one_08
  · exact funext I_one_09
  · exact funext I_one_10
  · exact funext I_one_11
  · exact funext I_one_12
  · exact funext I_one_13
  · exact funext I_one_14
  · exact funext I_one_15
  · exact funext I_one_16
  · exact funext I_one_17
  · exact funext I_one_18
  · exact funext I_one_19
  · exact funext I_one_20
  · exact funext I_one_21

theorem identity_binding : I_data.matrix 2=1 := by
  change castMatrix 2 22 I_digit=1
  rw [I_raw_one,castMatrix_one]

def B2_lowColumnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 3670160
  | 1 => 3145730
  | 2 => 3670034
  | 3 => 3174400
  | 4 => 3145747
  | 5 => 3203072
  | 6 => 139264
  | 7 => 3670036
  | 8 => 3424256
  | 9 => 3170312
  | 10 => 3153920
  | 11 => 3162112
  | 12 => 3170336
  | 13 => 3153984
  | 14 => 3686656
  | 15 => 3170816
  | 16 => 1048576
  | 17 => 3679232
  | 18 => 18432
  | 19 => 3670016
  | 20 => 1572864
  | 21 => 2686976
  | _ => 0

def B2_rowCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 1048576
  | 1 => 1049632
  | 2 => 34359738368
  | 3 => 35184372088832
  | 4 => 34360787969
  | 5 => 1152921504606846976
  | 6 => 36893488147419103232
  | 7 => 1
  | 8 => 1180591620717411303424
  | 9 => 37778931862957161709568
  | 10 => 38685626227668133590597632
  | 11 => 1237940039285380274899124224
  | 12 => 32768
  | 13 => 38723443207101828164517888
  | 14 => 1237978999997850535015251968
  | 15 => 33554432
  | 16 => 40564819207303340847894502572032
  | 17 => 1073741824
  | 18 => 1099511627776
  | 19 => 41872122575595521707073339393025
  | 20 => 1307304615035015937398043345953
  | 21 => 40604472013184307769166668006433
  | _ => 0

def B2_columnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 38686806819288851001902113
  | 1 => 1267650600228229401496703205409
  | 2 => 1267689285854457069630293804065
  | 3 => 36318243455009
  | 4 => 41832508493157797917524796375073
  | 5 => 1134945108001
  | 6 => 1099512676352
  | 7 => 39652766883359836930362573857
  | 8 => 34359771169
  | 9 => 1237940039285381408770490401
  | 10 => 1099511627809
  | 11 => 34359738401
  | 12 => 1208925819615763046072353
  | 13 => 37778931864056673337377
  | 14 => 36893488181778842657
  | 15 => 1152922638478213153
  | 16 => 32
  | 17 => 36029896530592801
  | 18 => 1125934266580992
  | 19 => 1057
  | 20 => 1056
  | 21 => 33555457
  | _ => 0

def B2_digit (i j : Fin 22) : ℕ := packedDigit 1 (B2_lowColumnCode j) i.val

private theorem B2_bound_00 : ∀ j : Fin 22,B2_digit 0 j<2 := by decide +kernel

private theorem B2_bound_01 : ∀ j : Fin 22,B2_digit 1 j<2 := by decide +kernel

private theorem B2_bound_02 : ∀ j : Fin 22,B2_digit 2 j<2 := by decide +kernel

private theorem B2_bound_03 : ∀ j : Fin 22,B2_digit 3 j<2 := by decide +kernel

private theorem B2_bound_04 : ∀ j : Fin 22,B2_digit 4 j<2 := by decide +kernel

private theorem B2_bound_05 : ∀ j : Fin 22,B2_digit 5 j<2 := by decide +kernel

private theorem B2_bound_06 : ∀ j : Fin 22,B2_digit 6 j<2 := by decide +kernel

private theorem B2_bound_07 : ∀ j : Fin 22,B2_digit 7 j<2 := by decide +kernel

private theorem B2_bound_08 : ∀ j : Fin 22,B2_digit 8 j<2 := by decide +kernel

private theorem B2_bound_09 : ∀ j : Fin 22,B2_digit 9 j<2 := by decide +kernel

private theorem B2_bound_10 : ∀ j : Fin 22,B2_digit 10 j<2 := by decide +kernel

private theorem B2_bound_11 : ∀ j : Fin 22,B2_digit 11 j<2 := by decide +kernel

private theorem B2_bound_12 : ∀ j : Fin 22,B2_digit 12 j<2 := by decide +kernel

private theorem B2_bound_13 : ∀ j : Fin 22,B2_digit 13 j<2 := by decide +kernel

private theorem B2_bound_14 : ∀ j : Fin 22,B2_digit 14 j<2 := by decide +kernel

private theorem B2_bound_15 : ∀ j : Fin 22,B2_digit 15 j<2 := by decide +kernel

private theorem B2_bound_16 : ∀ j : Fin 22,B2_digit 16 j<2 := by decide +kernel

private theorem B2_bound_17 : ∀ j : Fin 22,B2_digit 17 j<2 := by decide +kernel

private theorem B2_bound_18 : ∀ j : Fin 22,B2_digit 18 j<2 := by decide +kernel

private theorem B2_bound_19 : ∀ j : Fin 22,B2_digit 19 j<2 := by decide +kernel

private theorem B2_bound_20 : ∀ j : Fin 22,B2_digit 20 j<2 := by decide +kernel

private theorem B2_bound_21 : ∀ j : Fin 22,B2_digit 21 j<2 := by decide +kernel

theorem B2_bound : ∀ i j : Fin 22,B2_digit i j<2 := by
  intro i j
  fin_cases i
  · exact B2_bound_00 j
  · exact B2_bound_01 j
  · exact B2_bound_02 j
  · exact B2_bound_03 j
  · exact B2_bound_04 j
  · exact B2_bound_05 j
  · exact B2_bound_06 j
  · exact B2_bound_07 j
  · exact B2_bound_08 j
  · exact B2_bound_09 j
  · exact B2_bound_10 j
  · exact B2_bound_11 j
  · exact B2_bound_12 j
  · exact B2_bound_13 j
  · exact B2_bound_14 j
  · exact B2_bound_15 j
  · exact B2_bound_16 j
  · exact B2_bound_17 j
  · exact B2_bound_18 j
  · exact B2_bound_19 j
  · exact B2_bound_20 j
  · exact B2_bound_21 j

private theorem B2_row_00 : pack 32 (B2_digit 0)=B2_rowCode 0 := by decide +kernel

private theorem B2_row_01 : pack 32 (B2_digit 1)=B2_rowCode 1 := by decide +kernel

private theorem B2_row_02 : pack 32 (B2_digit 2)=B2_rowCode 2 := by decide +kernel

private theorem B2_row_03 : pack 32 (B2_digit 3)=B2_rowCode 3 := by decide +kernel

private theorem B2_row_04 : pack 32 (B2_digit 4)=B2_rowCode 4 := by decide +kernel

private theorem B2_row_05 : pack 32 (B2_digit 5)=B2_rowCode 5 := by decide +kernel

private theorem B2_row_06 : pack 32 (B2_digit 6)=B2_rowCode 6 := by decide +kernel

private theorem B2_row_07 : pack 32 (B2_digit 7)=B2_rowCode 7 := by decide +kernel

private theorem B2_row_08 : pack 32 (B2_digit 8)=B2_rowCode 8 := by decide +kernel

private theorem B2_row_09 : pack 32 (B2_digit 9)=B2_rowCode 9 := by decide +kernel

private theorem B2_row_10 : pack 32 (B2_digit 10)=B2_rowCode 10 := by decide +kernel

private theorem B2_row_11 : pack 32 (B2_digit 11)=B2_rowCode 11 := by decide +kernel

private theorem B2_row_12 : pack 32 (B2_digit 12)=B2_rowCode 12 := by decide +kernel

private theorem B2_row_13 : pack 32 (B2_digit 13)=B2_rowCode 13 := by decide +kernel

private theorem B2_row_14 : pack 32 (B2_digit 14)=B2_rowCode 14 := by decide +kernel

private theorem B2_row_15 : pack 32 (B2_digit 15)=B2_rowCode 15 := by decide +kernel

private theorem B2_row_16 : pack 32 (B2_digit 16)=B2_rowCode 16 := by decide +kernel

private theorem B2_row_17 : pack 32 (B2_digit 17)=B2_rowCode 17 := by decide +kernel

private theorem B2_row_18 : pack 32 (B2_digit 18)=B2_rowCode 18 := by decide +kernel

private theorem B2_row_19 : pack 32 (B2_digit 19)=B2_rowCode 19 := by decide +kernel

private theorem B2_row_20 : pack 32 (B2_digit 20)=B2_rowCode 20 := by decide +kernel

private theorem B2_row_21 : pack 32 (B2_digit 21)=B2_rowCode 21 := by decide +kernel

theorem B2_row_binding : ∀ i : Fin 22,pack 32 (B2_digit i)=B2_rowCode i := by
  intro i
  fin_cases i
  · exact B2_row_00
  · exact B2_row_01
  · exact B2_row_02
  · exact B2_row_03
  · exact B2_row_04
  · exact B2_row_05
  · exact B2_row_06
  · exact B2_row_07
  · exact B2_row_08
  · exact B2_row_09
  · exact B2_row_10
  · exact B2_row_11
  · exact B2_row_12
  · exact B2_row_13
  · exact B2_row_14
  · exact B2_row_15
  · exact B2_row_16
  · exact B2_row_17
  · exact B2_row_18
  · exact B2_row_19
  · exact B2_row_20
  · exact B2_row_21

private theorem B2_column_00 : reversePack 32 (fun j : Fin 22 => B2_digit j 0)=B2_columnCode 0 := by decide +kernel

private theorem B2_column_01 : reversePack 32 (fun j : Fin 22 => B2_digit j 1)=B2_columnCode 1 := by decide +kernel

private theorem B2_column_02 : reversePack 32 (fun j : Fin 22 => B2_digit j 2)=B2_columnCode 2 := by decide +kernel

private theorem B2_column_03 : reversePack 32 (fun j : Fin 22 => B2_digit j 3)=B2_columnCode 3 := by decide +kernel

private theorem B2_column_04 : reversePack 32 (fun j : Fin 22 => B2_digit j 4)=B2_columnCode 4 := by decide +kernel

private theorem B2_column_05 : reversePack 32 (fun j : Fin 22 => B2_digit j 5)=B2_columnCode 5 := by decide +kernel

private theorem B2_column_06 : reversePack 32 (fun j : Fin 22 => B2_digit j 6)=B2_columnCode 6 := by decide +kernel

private theorem B2_column_07 : reversePack 32 (fun j : Fin 22 => B2_digit j 7)=B2_columnCode 7 := by decide +kernel

private theorem B2_column_08 : reversePack 32 (fun j : Fin 22 => B2_digit j 8)=B2_columnCode 8 := by decide +kernel

private theorem B2_column_09 : reversePack 32 (fun j : Fin 22 => B2_digit j 9)=B2_columnCode 9 := by decide +kernel

private theorem B2_column_10 : reversePack 32 (fun j : Fin 22 => B2_digit j 10)=B2_columnCode 10 := by decide +kernel

private theorem B2_column_11 : reversePack 32 (fun j : Fin 22 => B2_digit j 11)=B2_columnCode 11 := by decide +kernel

private theorem B2_column_12 : reversePack 32 (fun j : Fin 22 => B2_digit j 12)=B2_columnCode 12 := by decide +kernel

private theorem B2_column_13 : reversePack 32 (fun j : Fin 22 => B2_digit j 13)=B2_columnCode 13 := by decide +kernel

private theorem B2_column_14 : reversePack 32 (fun j : Fin 22 => B2_digit j 14)=B2_columnCode 14 := by decide +kernel

private theorem B2_column_15 : reversePack 32 (fun j : Fin 22 => B2_digit j 15)=B2_columnCode 15 := by decide +kernel

private theorem B2_column_16 : reversePack 32 (fun j : Fin 22 => B2_digit j 16)=B2_columnCode 16 := by decide +kernel

private theorem B2_column_17 : reversePack 32 (fun j : Fin 22 => B2_digit j 17)=B2_columnCode 17 := by decide +kernel

private theorem B2_column_18 : reversePack 32 (fun j : Fin 22 => B2_digit j 18)=B2_columnCode 18 := by decide +kernel

private theorem B2_column_19 : reversePack 32 (fun j : Fin 22 => B2_digit j 19)=B2_columnCode 19 := by decide +kernel

private theorem B2_column_20 : reversePack 32 (fun j : Fin 22 => B2_digit j 20)=B2_columnCode 20 := by decide +kernel

private theorem B2_column_21 : reversePack 32 (fun j : Fin 22 => B2_digit j 21)=B2_columnCode 21 := by decide +kernel

theorem B2_column_binding : ∀ i : Fin 22,reversePack 32 (fun j : Fin 22 => B2_digit j i)=B2_columnCode i := by
  intro i
  fin_cases i
  · exact B2_column_00
  · exact B2_column_01
  · exact B2_column_02
  · exact B2_column_03
  · exact B2_column_04
  · exact B2_column_05
  · exact B2_column_06
  · exact B2_column_07
  · exact B2_column_08
  · exact B2_column_09
  · exact B2_column_10
  · exact B2_column_11
  · exact B2_column_12
  · exact B2_column_13
  · exact B2_column_14
  · exact B2_column_15
  · exact B2_column_16
  · exact B2_column_17
  · exact B2_column_18
  · exact B2_column_19
  · exact B2_column_20
  · exact B2_column_21

def B2_data : PackedData 22 2 32 where
  raw := B2_digit
  digit_lt := B2_bound
  rowCode := B2_rowCode
  columnCode := B2_columnCode
  row_binding := B2_row_binding
  column_binding := B2_column_binding

def B4_lowColumnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 65543
  | 1 => 65538
  | 2 => 589841
  | 3 => 590176
  | 4 => 589953
  | 5 => 590656
  | 6 => 525376
  | 7 => 65537
  | 8 => 592128
  | 9 => 594240
  | 10 => 73792
  | 11 => 606464
  | 12 => 622912
  | 13 => 196672
  | 14 => 327936
  | 15 => 590152
  | 16 => 1572864
  | 17 => 589888
  | 18 => 524544
  | 19 => 589824
  | 20 => 2097152
  | 21 => 65536
  | _ => 0

def B4_rowCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 34360787969
  | 1 => 33
  | 2 => 1
  | 3 => 37778931862957161709568
  | 4 => 1024
  | 5 => 32768
  | 6 => 38723443207101828164517888
  | 7 => 1048576
  | 8 => 1237978999997850535015251968
  | 9 => 33554432
  | 10 => 1073741824
  | 11 => 1099511627776
  | 12 => 35184372088832
  | 13 => 1125899906842624
  | 14 => 36028797018963968
  | 15 => 1152921504606846976
  | 16 => 40604472013184307769166668006433
  | 17 => 36893488147419103232
  | 18 => 1180591620717411303424
  | 19 => 40891953628585681378216018944
  | 20 => 1208925819614629174706176
  | 21 => 1267650600228229401496703205376
  | _ => 0

def B4_columnCode (i : Fin 22) : ℕ :=
  match i.val with
  | 0 => 41872083888788702418188011307008
  | 1 => 1267650600228229401496736759808
  | 2 => 40564857892929568516028126725120
  | 3 => 1246741644965733789074432
  | 4 => 40564819208483932468611947430912
  | 5 => 37816978272609221215232
  | 6 => 37778967891754180674560
  | 7 => 40564819207303340847894536126464
  | 8 => 36894614047359501312
  | 9 => 37815825386288986457088
  | 10 => 37778931864056706891776
  | 11 => 36893488181812397056
  | 12 => 37815825351105688110080
  | 13 => 37778931862957196312576
  | 14 => 36893488147452690432
  | 15 => 1237977855110731379513492480
  | 16 => 1056
  | 17 => 37778931862957195265024
  | 18 => 36893488147419104256
  | 19 => 33555456
  | 20 => 1
  | 21 => 33554432
  | _ => 0

def B4_digit (i j : Fin 22) : ℕ := packedDigit 1 (B4_lowColumnCode j) i.val

private theorem B4_bound_00 : ∀ j : Fin 22,B4_digit 0 j<2 := by decide +kernel

private theorem B4_bound_01 : ∀ j : Fin 22,B4_digit 1 j<2 := by decide +kernel

private theorem B4_bound_02 : ∀ j : Fin 22,B4_digit 2 j<2 := by decide +kernel

private theorem B4_bound_03 : ∀ j : Fin 22,B4_digit 3 j<2 := by decide +kernel

private theorem B4_bound_04 : ∀ j : Fin 22,B4_digit 4 j<2 := by decide +kernel

private theorem B4_bound_05 : ∀ j : Fin 22,B4_digit 5 j<2 := by decide +kernel

private theorem B4_bound_06 : ∀ j : Fin 22,B4_digit 6 j<2 := by decide +kernel

private theorem B4_bound_07 : ∀ j : Fin 22,B4_digit 7 j<2 := by decide +kernel

private theorem B4_bound_08 : ∀ j : Fin 22,B4_digit 8 j<2 := by decide +kernel

private theorem B4_bound_09 : ∀ j : Fin 22,B4_digit 9 j<2 := by decide +kernel

private theorem B4_bound_10 : ∀ j : Fin 22,B4_digit 10 j<2 := by decide +kernel

private theorem B4_bound_11 : ∀ j : Fin 22,B4_digit 11 j<2 := by decide +kernel

private theorem B4_bound_12 : ∀ j : Fin 22,B4_digit 12 j<2 := by decide +kernel

private theorem B4_bound_13 : ∀ j : Fin 22,B4_digit 13 j<2 := by decide +kernel

private theorem B4_bound_14 : ∀ j : Fin 22,B4_digit 14 j<2 := by decide +kernel

private theorem B4_bound_15 : ∀ j : Fin 22,B4_digit 15 j<2 := by decide +kernel

private theorem B4_bound_16 : ∀ j : Fin 22,B4_digit 16 j<2 := by decide +kernel

private theorem B4_bound_17 : ∀ j : Fin 22,B4_digit 17 j<2 := by decide +kernel

private theorem B4_bound_18 : ∀ j : Fin 22,B4_digit 18 j<2 := by decide +kernel

private theorem B4_bound_19 : ∀ j : Fin 22,B4_digit 19 j<2 := by decide +kernel

private theorem B4_bound_20 : ∀ j : Fin 22,B4_digit 20 j<2 := by decide +kernel

private theorem B4_bound_21 : ∀ j : Fin 22,B4_digit 21 j<2 := by decide +kernel

theorem B4_bound : ∀ i j : Fin 22,B4_digit i j<2 := by
  intro i j
  fin_cases i
  · exact B4_bound_00 j
  · exact B4_bound_01 j
  · exact B4_bound_02 j
  · exact B4_bound_03 j
  · exact B4_bound_04 j
  · exact B4_bound_05 j
  · exact B4_bound_06 j
  · exact B4_bound_07 j
  · exact B4_bound_08 j
  · exact B4_bound_09 j
  · exact B4_bound_10 j
  · exact B4_bound_11 j
  · exact B4_bound_12 j
  · exact B4_bound_13 j
  · exact B4_bound_14 j
  · exact B4_bound_15 j
  · exact B4_bound_16 j
  · exact B4_bound_17 j
  · exact B4_bound_18 j
  · exact B4_bound_19 j
  · exact B4_bound_20 j
  · exact B4_bound_21 j

private theorem B4_row_00 : pack 32 (B4_digit 0)=B4_rowCode 0 := by decide +kernel

private theorem B4_row_01 : pack 32 (B4_digit 1)=B4_rowCode 1 := by decide +kernel

private theorem B4_row_02 : pack 32 (B4_digit 2)=B4_rowCode 2 := by decide +kernel

private theorem B4_row_03 : pack 32 (B4_digit 3)=B4_rowCode 3 := by decide +kernel

private theorem B4_row_04 : pack 32 (B4_digit 4)=B4_rowCode 4 := by decide +kernel

private theorem B4_row_05 : pack 32 (B4_digit 5)=B4_rowCode 5 := by decide +kernel

private theorem B4_row_06 : pack 32 (B4_digit 6)=B4_rowCode 6 := by decide +kernel

private theorem B4_row_07 : pack 32 (B4_digit 7)=B4_rowCode 7 := by decide +kernel

private theorem B4_row_08 : pack 32 (B4_digit 8)=B4_rowCode 8 := by decide +kernel

private theorem B4_row_09 : pack 32 (B4_digit 9)=B4_rowCode 9 := by decide +kernel

private theorem B4_row_10 : pack 32 (B4_digit 10)=B4_rowCode 10 := by decide +kernel

private theorem B4_row_11 : pack 32 (B4_digit 11)=B4_rowCode 11 := by decide +kernel

private theorem B4_row_12 : pack 32 (B4_digit 12)=B4_rowCode 12 := by decide +kernel

private theorem B4_row_13 : pack 32 (B4_digit 13)=B4_rowCode 13 := by decide +kernel

private theorem B4_row_14 : pack 32 (B4_digit 14)=B4_rowCode 14 := by decide +kernel

private theorem B4_row_15 : pack 32 (B4_digit 15)=B4_rowCode 15 := by decide +kernel

private theorem B4_row_16 : pack 32 (B4_digit 16)=B4_rowCode 16 := by decide +kernel

private theorem B4_row_17 : pack 32 (B4_digit 17)=B4_rowCode 17 := by decide +kernel

private theorem B4_row_18 : pack 32 (B4_digit 18)=B4_rowCode 18 := by decide +kernel

private theorem B4_row_19 : pack 32 (B4_digit 19)=B4_rowCode 19 := by decide +kernel

private theorem B4_row_20 : pack 32 (B4_digit 20)=B4_rowCode 20 := by decide +kernel

private theorem B4_row_21 : pack 32 (B4_digit 21)=B4_rowCode 21 := by decide +kernel

theorem B4_row_binding : ∀ i : Fin 22,pack 32 (B4_digit i)=B4_rowCode i := by
  intro i
  fin_cases i
  · exact B4_row_00
  · exact B4_row_01
  · exact B4_row_02
  · exact B4_row_03
  · exact B4_row_04
  · exact B4_row_05
  · exact B4_row_06
  · exact B4_row_07
  · exact B4_row_08
  · exact B4_row_09
  · exact B4_row_10
  · exact B4_row_11
  · exact B4_row_12
  · exact B4_row_13
  · exact B4_row_14
  · exact B4_row_15
  · exact B4_row_16
  · exact B4_row_17
  · exact B4_row_18
  · exact B4_row_19
  · exact B4_row_20
  · exact B4_row_21

private theorem B4_column_00 : reversePack 32 (fun j : Fin 22 => B4_digit j 0)=B4_columnCode 0 := by decide +kernel

private theorem B4_column_01 : reversePack 32 (fun j : Fin 22 => B4_digit j 1)=B4_columnCode 1 := by decide +kernel

private theorem B4_column_02 : reversePack 32 (fun j : Fin 22 => B4_digit j 2)=B4_columnCode 2 := by decide +kernel

private theorem B4_column_03 : reversePack 32 (fun j : Fin 22 => B4_digit j 3)=B4_columnCode 3 := by decide +kernel

private theorem B4_column_04 : reversePack 32 (fun j : Fin 22 => B4_digit j 4)=B4_columnCode 4 := by decide +kernel

private theorem B4_column_05 : reversePack 32 (fun j : Fin 22 => B4_digit j 5)=B4_columnCode 5 := by decide +kernel

private theorem B4_column_06 : reversePack 32 (fun j : Fin 22 => B4_digit j 6)=B4_columnCode 6 := by decide +kernel

private theorem B4_column_07 : reversePack 32 (fun j : Fin 22 => B4_digit j 7)=B4_columnCode 7 := by decide +kernel

private theorem B4_column_08 : reversePack 32 (fun j : Fin 22 => B4_digit j 8)=B4_columnCode 8 := by decide +kernel

private theorem B4_column_09 : reversePack 32 (fun j : Fin 22 => B4_digit j 9)=B4_columnCode 9 := by decide +kernel

private theorem B4_column_10 : reversePack 32 (fun j : Fin 22 => B4_digit j 10)=B4_columnCode 10 := by decide +kernel

private theorem B4_column_11 : reversePack 32 (fun j : Fin 22 => B4_digit j 11)=B4_columnCode 11 := by decide +kernel

private theorem B4_column_12 : reversePack 32 (fun j : Fin 22 => B4_digit j 12)=B4_columnCode 12 := by decide +kernel

private theorem B4_column_13 : reversePack 32 (fun j : Fin 22 => B4_digit j 13)=B4_columnCode 13 := by decide +kernel

private theorem B4_column_14 : reversePack 32 (fun j : Fin 22 => B4_digit j 14)=B4_columnCode 14 := by decide +kernel

private theorem B4_column_15 : reversePack 32 (fun j : Fin 22 => B4_digit j 15)=B4_columnCode 15 := by decide +kernel

private theorem B4_column_16 : reversePack 32 (fun j : Fin 22 => B4_digit j 16)=B4_columnCode 16 := by decide +kernel

private theorem B4_column_17 : reversePack 32 (fun j : Fin 22 => B4_digit j 17)=B4_columnCode 17 := by decide +kernel

private theorem B4_column_18 : reversePack 32 (fun j : Fin 22 => B4_digit j 18)=B4_columnCode 18 := by decide +kernel

private theorem B4_column_19 : reversePack 32 (fun j : Fin 22 => B4_digit j 19)=B4_columnCode 19 := by decide +kernel

private theorem B4_column_20 : reversePack 32 (fun j : Fin 22 => B4_digit j 20)=B4_columnCode 20 := by decide +kernel

private theorem B4_column_21 : reversePack 32 (fun j : Fin 22 => B4_digit j 21)=B4_columnCode 21 := by decide +kernel

theorem B4_column_binding : ∀ i : Fin 22,reversePack 32 (fun j : Fin 22 => B4_digit j i)=B4_columnCode i := by
  intro i
  fin_cases i
  · exact B4_column_00
  · exact B4_column_01
  · exact B4_column_02
  · exact B4_column_03
  · exact B4_column_04
  · exact B4_column_05
  · exact B4_column_06
  · exact B4_column_07
  · exact B4_column_08
  · exact B4_column_09
  · exact B4_column_10
  · exact B4_column_11
  · exact B4_column_12
  · exact B4_column_13
  · exact B4_column_14
  · exact B4_column_15
  · exact B4_column_16
  · exact B4_column_17
  · exact B4_column_18
  · exact B4_column_19
  · exact B4_column_20
  · exact B4_column_21

def B4_data : PackedData 22 2 32 where
  raw := B4_digit
  digit_lt := B4_bound
  rowCode := B4_rowCode
  columnCode := B4_columnCode
  row_binding := B4_row_binding
  column_binding := B4_column_binding

end SymmetricSubgroupAsymptotics.CFSGCoTwoNativeTwentyTwoBaseCaches
