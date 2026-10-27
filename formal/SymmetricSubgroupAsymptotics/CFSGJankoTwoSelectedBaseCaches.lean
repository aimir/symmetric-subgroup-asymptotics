import SymmetricSubgroupAsymptotics.MatrixKroneckerProductReflection
import Mathlib.Tactic.FinCases

/-! Literal14/F5 selected caches; digit bounds and both pack bindings are independently kernel checked. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedBaseCaches
open MatrixKroneckerProductReflection MatrixKroneckerDotReflection
open MatrixNaturalRowDotReflection SmallNaturalMatrixProductReflection

def A_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 206628192264
  | 1 => 687781969921
  | 2 => 1787109048832
  | 3 => 755964575808
  | 4 => 1786706427904
  | 5 => 1305670062080
  | 6 => 206160527360
  | 7 => 137439215616
  | 8 => 1100048498688
  | 9 => 1099578736640
  | 10 => 627065225216
  | 11 => 2474974904320
  | 12 => 68719476736
  | 13 => 549755813888
  | _ => 0

def A_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 256
  | 1 => 1
  | 2 => 16777216
  | 3 => 65536
  | 4 => 1099511627776
  | 5 => 4294967296
  | 6 => 72057594037927936
  | 7 => 281474976710656
  | 8 => 18889465931478631187204
  | 9 => 73786976294838404099
  | 10 => 309485009821345068724781056
  | 11 => 1208925819614629174706176
  | 12 => 80467311479514295417799049731
  | 13 => 20283648762098401874949959778560
  | _ => 0

def A_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 79228162514264342004475364096
  | 1 => 20282409603651670427262966039041
  | 2 => 1208925819614642059608579
  | 3 => 309485009821348367259665153
  | 4 => 18446744073709552131
  | 5 => 4722366482869645214466
  | 6 => 281474976711424
  | 7 => 72057594037928448
  | 8 => 17179869186
  | 9 => 4398046511106
  | 10 => 65793
  | 11 => 16778244
  | 12 => 256
  | 13 => 1
  | _ => 0

def A_digit (i j : Fin 14) : ℕ := packedDigit 3 (A_lowColumnCode j) i.val

private theorem A_bound_00 : ∀ j : Fin 14, A_digit 0 j < 5 := by decide +kernel

private theorem A_bound_01 : ∀ j : Fin 14, A_digit 1 j < 5 := by decide +kernel

private theorem A_bound_02 : ∀ j : Fin 14, A_digit 2 j < 5 := by decide +kernel

private theorem A_bound_03 : ∀ j : Fin 14, A_digit 3 j < 5 := by decide +kernel

private theorem A_bound_04 : ∀ j : Fin 14, A_digit 4 j < 5 := by decide +kernel

private theorem A_bound_05 : ∀ j : Fin 14, A_digit 5 j < 5 := by decide +kernel

private theorem A_bound_06 : ∀ j : Fin 14, A_digit 6 j < 5 := by decide +kernel

private theorem A_bound_07 : ∀ j : Fin 14, A_digit 7 j < 5 := by decide +kernel

private theorem A_bound_08 : ∀ j : Fin 14, A_digit 8 j < 5 := by decide +kernel

private theorem A_bound_09 : ∀ j : Fin 14, A_digit 9 j < 5 := by decide +kernel

private theorem A_bound_10 : ∀ j : Fin 14, A_digit 10 j < 5 := by decide +kernel

private theorem A_bound_11 : ∀ j : Fin 14, A_digit 11 j < 5 := by decide +kernel

private theorem A_bound_12 : ∀ j : Fin 14, A_digit 12 j < 5 := by decide +kernel

private theorem A_bound_13 : ∀ j : Fin 14, A_digit 13 j < 5 := by decide +kernel

theorem A_bound : ∀ i j : Fin 14, A_digit i j < 5 := by
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

private theorem A_row_00 : pack 256 (A_digit 0)=A_rowCode 0 := by decide +kernel

private theorem A_row_01 : pack 256 (A_digit 1)=A_rowCode 1 := by decide +kernel

private theorem A_row_02 : pack 256 (A_digit 2)=A_rowCode 2 := by decide +kernel

private theorem A_row_03 : pack 256 (A_digit 3)=A_rowCode 3 := by decide +kernel

private theorem A_row_04 : pack 256 (A_digit 4)=A_rowCode 4 := by decide +kernel

private theorem A_row_05 : pack 256 (A_digit 5)=A_rowCode 5 := by decide +kernel

private theorem A_row_06 : pack 256 (A_digit 6)=A_rowCode 6 := by decide +kernel

private theorem A_row_07 : pack 256 (A_digit 7)=A_rowCode 7 := by decide +kernel

private theorem A_row_08 : pack 256 (A_digit 8)=A_rowCode 8 := by decide +kernel

private theorem A_row_09 : pack 256 (A_digit 9)=A_rowCode 9 := by decide +kernel

private theorem A_row_10 : pack 256 (A_digit 10)=A_rowCode 10 := by decide +kernel

private theorem A_row_11 : pack 256 (A_digit 11)=A_rowCode 11 := by decide +kernel

private theorem A_row_12 : pack 256 (A_digit 12)=A_rowCode 12 := by decide +kernel

private theorem A_row_13 : pack 256 (A_digit 13)=A_rowCode 13 := by decide +kernel

theorem A_row_binding : ∀ i : Fin 14, pack 256 (A_digit i)=A_rowCode i := by
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

private theorem A_column_00 : reversePack 256 (fun j : Fin 14 => A_digit j 0)=A_columnCode 0 := by decide +kernel

private theorem A_column_01 : reversePack 256 (fun j : Fin 14 => A_digit j 1)=A_columnCode 1 := by decide +kernel

private theorem A_column_02 : reversePack 256 (fun j : Fin 14 => A_digit j 2)=A_columnCode 2 := by decide +kernel

private theorem A_column_03 : reversePack 256 (fun j : Fin 14 => A_digit j 3)=A_columnCode 3 := by decide +kernel

private theorem A_column_04 : reversePack 256 (fun j : Fin 14 => A_digit j 4)=A_columnCode 4 := by decide +kernel

private theorem A_column_05 : reversePack 256 (fun j : Fin 14 => A_digit j 5)=A_columnCode 5 := by decide +kernel

private theorem A_column_06 : reversePack 256 (fun j : Fin 14 => A_digit j 6)=A_columnCode 6 := by decide +kernel

private theorem A_column_07 : reversePack 256 (fun j : Fin 14 => A_digit j 7)=A_columnCode 7 := by decide +kernel

private theorem A_column_08 : reversePack 256 (fun j : Fin 14 => A_digit j 8)=A_columnCode 8 := by decide +kernel

private theorem A_column_09 : reversePack 256 (fun j : Fin 14 => A_digit j 9)=A_columnCode 9 := by decide +kernel

private theorem A_column_10 : reversePack 256 (fun j : Fin 14 => A_digit j 10)=A_columnCode 10 := by decide +kernel

private theorem A_column_11 : reversePack 256 (fun j : Fin 14 => A_digit j 11)=A_columnCode 11 := by decide +kernel

private theorem A_column_12 : reversePack 256 (fun j : Fin 14 => A_digit j 12)=A_columnCode 12 := by decide +kernel

private theorem A_column_13 : reversePack 256 (fun j : Fin 14 => A_digit j 13)=A_columnCode 13 := by decide +kernel

theorem A_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => A_digit j i)=A_columnCode i := by
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

def A_data : PackedData 14 5 256 where
  raw := A_digit
  digit_lt := A_bound
  rowCode := A_rowCode
  columnCode := A_columnCode
  row_binding := A_row_binding
  column_binding := A_column_binding

def rowsA : List (List ℕ) := [[0,1,0,0,0,0,0,0,0,0,0,0,0,0],[1,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,1,0,0,0,0,0,0,0,0,0,0],[0,0,1,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,1,0,0,0,0,0,0,0,0],[0,0,0,0,1,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,1,0,0,0,0,0,0],[0,0,0,0,0,0,1,0,0,0,0,0,0,0],[4,3,0,3,0,0,0,0,0,4,0,0,0,0],[3,4,3,0,0,0,0,0,4,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,1,0,0],[0,0,0,0,0,0,0,0,0,0,1,0,0,0],[3,2,2,3,2,3,3,2,0,0,1,4,1,0],[0,1,3,1,3,2,0,0,2,2,1,4,0,1]]

def matrixA : Matrix (Fin 14) (Fin 14) (ZMod 5) := Matrix.of (fun i j => (((rowsA.getD i.val []).getD j.val 0 : ℕ) : ZMod 5))

private theorem A_source_00 : ∀ j : Fin 14, (rowsA.getD 0 []).getD j.val 0=A_digit 0 j := by decide +kernel

private theorem A_source_01 : ∀ j : Fin 14, (rowsA.getD 1 []).getD j.val 0=A_digit 1 j := by decide +kernel

private theorem A_source_02 : ∀ j : Fin 14, (rowsA.getD 2 []).getD j.val 0=A_digit 2 j := by decide +kernel

private theorem A_source_03 : ∀ j : Fin 14, (rowsA.getD 3 []).getD j.val 0=A_digit 3 j := by decide +kernel

private theorem A_source_04 : ∀ j : Fin 14, (rowsA.getD 4 []).getD j.val 0=A_digit 4 j := by decide +kernel

private theorem A_source_05 : ∀ j : Fin 14, (rowsA.getD 5 []).getD j.val 0=A_digit 5 j := by decide +kernel

private theorem A_source_06 : ∀ j : Fin 14, (rowsA.getD 6 []).getD j.val 0=A_digit 6 j := by decide +kernel

private theorem A_source_07 : ∀ j : Fin 14, (rowsA.getD 7 []).getD j.val 0=A_digit 7 j := by decide +kernel

private theorem A_source_08 : ∀ j : Fin 14, (rowsA.getD 8 []).getD j.val 0=A_digit 8 j := by decide +kernel

private theorem A_source_09 : ∀ j : Fin 14, (rowsA.getD 9 []).getD j.val 0=A_digit 9 j := by decide +kernel

private theorem A_source_10 : ∀ j : Fin 14, (rowsA.getD 10 []).getD j.val 0=A_digit 10 j := by decide +kernel

private theorem A_source_11 : ∀ j : Fin 14, (rowsA.getD 11 []).getD j.val 0=A_digit 11 j := by decide +kernel

private theorem A_source_12 : ∀ j : Fin 14, (rowsA.getD 12 []).getD j.val 0=A_digit 12 j := by decide +kernel

private theorem A_source_13 : ∀ j : Fin 14, (rowsA.getD 13 []).getD j.val 0=A_digit 13 j := by decide +kernel

theorem A_source_digits : ∀ i j : Fin 14, (rowsA.getD i.val []).getD j.val 0=A_digit i j := by
  intro i j
  fin_cases i
  · exact A_source_00 j
  · exact A_source_01 j
  · exact A_source_02 j
  · exact A_source_03 j
  · exact A_source_04 j
  · exact A_source_05 j
  · exact A_source_06 j
  · exact A_source_07 j
  · exact A_source_08 j
  · exact A_source_09 j
  · exact A_source_10 j
  · exact A_source_11 j
  · exact A_source_12 j
  · exact A_source_13 j

theorem A_source_binding : matrixA=A_data.matrix 5 := by
  ext i j
  exact congrArg (fun x : ℕ => (x : ZMod 5)) (A_source_digits i j)

def B_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 264
  | 1 => 12560
  | 2 => 12505
  | 3 => 16384
  | 4 => 16896
  | 5 => 16777216
  | 6 => 32768
  | 7 => 1073741824
  | 8 => 262144
  | 9 => 2097152
  | 10 => 134217728
  | 11 => 549755813888
  | 12 => 8589934592
  | 13 => 68719476736
  | _ => 0

def B_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 65536
  | 1 => 197121
  | 2 => 197636
  | 3 => 4294967296
  | 4 => 17247175424
  | 5 => 281474976710656
  | 6 => 18446744073709551616
  | 7 => 4722366482869645213696
  | 8 => 1099511627776
  | 9 => 1208925819614629174706176
  | 10 => 72057594037927936
  | 11 => 79228162514264337593543950336
  | 12 => 20282409603651670423947251286016
  | 13 => 309485009821345068724781056
  | _ => 0

def B_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 80466102553549717868443074560
  | 1 => 159694279234913504070922665984
  | 2 => 20521022560391026920542993121280
  | 3 => 18889465931478580854784
  | 4 => 1227815285546107755560960
  | 5 => 1099511627776
  | 6 => 18446744073709551616
  | 7 => 16777216
  | 8 => 72057594037927936
  | 9 => 281474976710656
  | 10 => 4294967296
  | 11 => 1
  | 12 => 65536
  | 13 => 256
  | _ => 0

def B_digit (i j : Fin 14) : ℕ := packedDigit 3 (B_lowColumnCode j) i.val

private theorem B_bound_00 : ∀ j : Fin 14, B_digit 0 j < 5 := by decide +kernel

private theorem B_bound_01 : ∀ j : Fin 14, B_digit 1 j < 5 := by decide +kernel

private theorem B_bound_02 : ∀ j : Fin 14, B_digit 2 j < 5 := by decide +kernel

private theorem B_bound_03 : ∀ j : Fin 14, B_digit 3 j < 5 := by decide +kernel

private theorem B_bound_04 : ∀ j : Fin 14, B_digit 4 j < 5 := by decide +kernel

private theorem B_bound_05 : ∀ j : Fin 14, B_digit 5 j < 5 := by decide +kernel

private theorem B_bound_06 : ∀ j : Fin 14, B_digit 6 j < 5 := by decide +kernel

private theorem B_bound_07 : ∀ j : Fin 14, B_digit 7 j < 5 := by decide +kernel

private theorem B_bound_08 : ∀ j : Fin 14, B_digit 8 j < 5 := by decide +kernel

private theorem B_bound_09 : ∀ j : Fin 14, B_digit 9 j < 5 := by decide +kernel

private theorem B_bound_10 : ∀ j : Fin 14, B_digit 10 j < 5 := by decide +kernel

private theorem B_bound_11 : ∀ j : Fin 14, B_digit 11 j < 5 := by decide +kernel

private theorem B_bound_12 : ∀ j : Fin 14, B_digit 12 j < 5 := by decide +kernel

private theorem B_bound_13 : ∀ j : Fin 14, B_digit 13 j < 5 := by decide +kernel

theorem B_bound : ∀ i j : Fin 14, B_digit i j < 5 := by
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

private theorem B_row_00 : pack 256 (B_digit 0)=B_rowCode 0 := by decide +kernel

private theorem B_row_01 : pack 256 (B_digit 1)=B_rowCode 1 := by decide +kernel

private theorem B_row_02 : pack 256 (B_digit 2)=B_rowCode 2 := by decide +kernel

private theorem B_row_03 : pack 256 (B_digit 3)=B_rowCode 3 := by decide +kernel

private theorem B_row_04 : pack 256 (B_digit 4)=B_rowCode 4 := by decide +kernel

private theorem B_row_05 : pack 256 (B_digit 5)=B_rowCode 5 := by decide +kernel

private theorem B_row_06 : pack 256 (B_digit 6)=B_rowCode 6 := by decide +kernel

private theorem B_row_07 : pack 256 (B_digit 7)=B_rowCode 7 := by decide +kernel

private theorem B_row_08 : pack 256 (B_digit 8)=B_rowCode 8 := by decide +kernel

private theorem B_row_09 : pack 256 (B_digit 9)=B_rowCode 9 := by decide +kernel

private theorem B_row_10 : pack 256 (B_digit 10)=B_rowCode 10 := by decide +kernel

private theorem B_row_11 : pack 256 (B_digit 11)=B_rowCode 11 := by decide +kernel

private theorem B_row_12 : pack 256 (B_digit 12)=B_rowCode 12 := by decide +kernel

private theorem B_row_13 : pack 256 (B_digit 13)=B_rowCode 13 := by decide +kernel

theorem B_row_binding : ∀ i : Fin 14, pack 256 (B_digit i)=B_rowCode i := by
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

private theorem B_column_00 : reversePack 256 (fun j : Fin 14 => B_digit j 0)=B_columnCode 0 := by decide +kernel

private theorem B_column_01 : reversePack 256 (fun j : Fin 14 => B_digit j 1)=B_columnCode 1 := by decide +kernel

private theorem B_column_02 : reversePack 256 (fun j : Fin 14 => B_digit j 2)=B_columnCode 2 := by decide +kernel

private theorem B_column_03 : reversePack 256 (fun j : Fin 14 => B_digit j 3)=B_columnCode 3 := by decide +kernel

private theorem B_column_04 : reversePack 256 (fun j : Fin 14 => B_digit j 4)=B_columnCode 4 := by decide +kernel

private theorem B_column_05 : reversePack 256 (fun j : Fin 14 => B_digit j 5)=B_columnCode 5 := by decide +kernel

private theorem B_column_06 : reversePack 256 (fun j : Fin 14 => B_digit j 6)=B_columnCode 6 := by decide +kernel

private theorem B_column_07 : reversePack 256 (fun j : Fin 14 => B_digit j 7)=B_columnCode 7 := by decide +kernel

private theorem B_column_08 : reversePack 256 (fun j : Fin 14 => B_digit j 8)=B_columnCode 8 := by decide +kernel

private theorem B_column_09 : reversePack 256 (fun j : Fin 14 => B_digit j 9)=B_columnCode 9 := by decide +kernel

private theorem B_column_10 : reversePack 256 (fun j : Fin 14 => B_digit j 10)=B_columnCode 10 := by decide +kernel

private theorem B_column_11 : reversePack 256 (fun j : Fin 14 => B_digit j 11)=B_columnCode 11 := by decide +kernel

private theorem B_column_12 : reversePack 256 (fun j : Fin 14 => B_digit j 12)=B_columnCode 12 := by decide +kernel

private theorem B_column_13 : reversePack 256 (fun j : Fin 14 => B_digit j 13)=B_columnCode 13 := by decide +kernel

theorem B_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => B_digit j i)=B_columnCode i := by
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

def B_data : PackedData 14 5 256 where
  raw := B_digit
  digit_lt := B_bound
  rowCode := B_rowCode
  columnCode := B_columnCode
  row_binding := B_row_binding
  column_binding := B_column_binding

def rowsB : List (List ℕ) := [[0,0,1,0,0,0,0,0,0,0,0,0,0,0],[1,2,3,0,0,0,0,0,0,0,0,0,0,0],[4,4,3,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,1,0,0,0,0,0,0,0,0,0],[0,3,3,4,4,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,1,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,1,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,1,0,0,0,0],[0,0,0,0,0,1,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,1,0,0,0],[0,0,0,0,0,0,0,1,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,1,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,1],[0,0,0,0,0,0,0,0,0,0,0,1,0,0]]

def matrixB : Matrix (Fin 14) (Fin 14) (ZMod 5) := Matrix.of (fun i j => (((rowsB.getD i.val []).getD j.val 0 : ℕ) : ZMod 5))

private theorem B_source_00 : ∀ j : Fin 14, (rowsB.getD 0 []).getD j.val 0=B_digit 0 j := by decide +kernel

private theorem B_source_01 : ∀ j : Fin 14, (rowsB.getD 1 []).getD j.val 0=B_digit 1 j := by decide +kernel

private theorem B_source_02 : ∀ j : Fin 14, (rowsB.getD 2 []).getD j.val 0=B_digit 2 j := by decide +kernel

private theorem B_source_03 : ∀ j : Fin 14, (rowsB.getD 3 []).getD j.val 0=B_digit 3 j := by decide +kernel

private theorem B_source_04 : ∀ j : Fin 14, (rowsB.getD 4 []).getD j.val 0=B_digit 4 j := by decide +kernel

private theorem B_source_05 : ∀ j : Fin 14, (rowsB.getD 5 []).getD j.val 0=B_digit 5 j := by decide +kernel

private theorem B_source_06 : ∀ j : Fin 14, (rowsB.getD 6 []).getD j.val 0=B_digit 6 j := by decide +kernel

private theorem B_source_07 : ∀ j : Fin 14, (rowsB.getD 7 []).getD j.val 0=B_digit 7 j := by decide +kernel

private theorem B_source_08 : ∀ j : Fin 14, (rowsB.getD 8 []).getD j.val 0=B_digit 8 j := by decide +kernel

private theorem B_source_09 : ∀ j : Fin 14, (rowsB.getD 9 []).getD j.val 0=B_digit 9 j := by decide +kernel

private theorem B_source_10 : ∀ j : Fin 14, (rowsB.getD 10 []).getD j.val 0=B_digit 10 j := by decide +kernel

private theorem B_source_11 : ∀ j : Fin 14, (rowsB.getD 11 []).getD j.val 0=B_digit 11 j := by decide +kernel

private theorem B_source_12 : ∀ j : Fin 14, (rowsB.getD 12 []).getD j.val 0=B_digit 12 j := by decide +kernel

private theorem B_source_13 : ∀ j : Fin 14, (rowsB.getD 13 []).getD j.val 0=B_digit 13 j := by decide +kernel

theorem B_source_digits : ∀ i j : Fin 14, (rowsB.getD i.val []).getD j.val 0=B_digit i j := by
  intro i j
  fin_cases i
  · exact B_source_00 j
  · exact B_source_01 j
  · exact B_source_02 j
  · exact B_source_03 j
  · exact B_source_04 j
  · exact B_source_05 j
  · exact B_source_06 j
  · exact B_source_07 j
  · exact B_source_08 j
  · exact B_source_09 j
  · exact B_source_10 j
  · exact B_source_11 j
  · exact B_source_12 j
  · exact B_source_13 j

theorem B_source_binding : matrixB=B_data.matrix 5 := by
  ext i j
  exact congrArg (fun x : ℕ => (x : ZMod 5)) (B_source_digits i j)

def I_lowColumnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 1
  | 1 => 8
  | 2 => 64
  | 3 => 512
  | 4 => 4096
  | 5 => 32768
  | 6 => 262144
  | 7 => 2097152
  | 8 => 16777216
  | 9 => 134217728
  | 10 => 1073741824
  | 11 => 8589934592
  | 12 => 68719476736
  | 13 => 549755813888
  | _ => 0

def I_rowCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 1
  | 1 => 256
  | 2 => 65536
  | 3 => 16777216
  | 4 => 4294967296
  | 5 => 1099511627776
  | 6 => 281474976710656
  | 7 => 72057594037927936
  | 8 => 18446744073709551616
  | 9 => 4722366482869645213696
  | 10 => 1208925819614629174706176
  | 11 => 309485009821345068724781056
  | 12 => 79228162514264337593543950336
  | 13 => 20282409603651670423947251286016
  | _ => 0

def I_columnCode (i : Fin 14) : ℕ :=
  match i.val with
  | 0 => 20282409603651670423947251286016
  | 1 => 79228162514264337593543950336
  | 2 => 309485009821345068724781056
  | 3 => 1208925819614629174706176
  | 4 => 4722366482869645213696
  | 5 => 18446744073709551616
  | 6 => 72057594037927936
  | 7 => 281474976710656
  | 8 => 1099511627776
  | 9 => 4294967296
  | 10 => 16777216
  | 11 => 65536
  | 12 => 256
  | 13 => 1
  | _ => 0

def I_digit (i j : Fin 14) : ℕ := packedDigit 3 (I_lowColumnCode j) i.val

private theorem I_bound_00 : ∀ j : Fin 14, I_digit 0 j < 5 := by decide +kernel

private theorem I_bound_01 : ∀ j : Fin 14, I_digit 1 j < 5 := by decide +kernel

private theorem I_bound_02 : ∀ j : Fin 14, I_digit 2 j < 5 := by decide +kernel

private theorem I_bound_03 : ∀ j : Fin 14, I_digit 3 j < 5 := by decide +kernel

private theorem I_bound_04 : ∀ j : Fin 14, I_digit 4 j < 5 := by decide +kernel

private theorem I_bound_05 : ∀ j : Fin 14, I_digit 5 j < 5 := by decide +kernel

private theorem I_bound_06 : ∀ j : Fin 14, I_digit 6 j < 5 := by decide +kernel

private theorem I_bound_07 : ∀ j : Fin 14, I_digit 7 j < 5 := by decide +kernel

private theorem I_bound_08 : ∀ j : Fin 14, I_digit 8 j < 5 := by decide +kernel

private theorem I_bound_09 : ∀ j : Fin 14, I_digit 9 j < 5 := by decide +kernel

private theorem I_bound_10 : ∀ j : Fin 14, I_digit 10 j < 5 := by decide +kernel

private theorem I_bound_11 : ∀ j : Fin 14, I_digit 11 j < 5 := by decide +kernel

private theorem I_bound_12 : ∀ j : Fin 14, I_digit 12 j < 5 := by decide +kernel

private theorem I_bound_13 : ∀ j : Fin 14, I_digit 13 j < 5 := by decide +kernel

theorem I_bound : ∀ i j : Fin 14, I_digit i j < 5 := by
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

private theorem I_row_00 : pack 256 (I_digit 0)=I_rowCode 0 := by decide +kernel

private theorem I_row_01 : pack 256 (I_digit 1)=I_rowCode 1 := by decide +kernel

private theorem I_row_02 : pack 256 (I_digit 2)=I_rowCode 2 := by decide +kernel

private theorem I_row_03 : pack 256 (I_digit 3)=I_rowCode 3 := by decide +kernel

private theorem I_row_04 : pack 256 (I_digit 4)=I_rowCode 4 := by decide +kernel

private theorem I_row_05 : pack 256 (I_digit 5)=I_rowCode 5 := by decide +kernel

private theorem I_row_06 : pack 256 (I_digit 6)=I_rowCode 6 := by decide +kernel

private theorem I_row_07 : pack 256 (I_digit 7)=I_rowCode 7 := by decide +kernel

private theorem I_row_08 : pack 256 (I_digit 8)=I_rowCode 8 := by decide +kernel

private theorem I_row_09 : pack 256 (I_digit 9)=I_rowCode 9 := by decide +kernel

private theorem I_row_10 : pack 256 (I_digit 10)=I_rowCode 10 := by decide +kernel

private theorem I_row_11 : pack 256 (I_digit 11)=I_rowCode 11 := by decide +kernel

private theorem I_row_12 : pack 256 (I_digit 12)=I_rowCode 12 := by decide +kernel

private theorem I_row_13 : pack 256 (I_digit 13)=I_rowCode 13 := by decide +kernel

theorem I_row_binding : ∀ i : Fin 14, pack 256 (I_digit i)=I_rowCode i := by
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

private theorem I_column_00 : reversePack 256 (fun j : Fin 14 => I_digit j 0)=I_columnCode 0 := by decide +kernel

private theorem I_column_01 : reversePack 256 (fun j : Fin 14 => I_digit j 1)=I_columnCode 1 := by decide +kernel

private theorem I_column_02 : reversePack 256 (fun j : Fin 14 => I_digit j 2)=I_columnCode 2 := by decide +kernel

private theorem I_column_03 : reversePack 256 (fun j : Fin 14 => I_digit j 3)=I_columnCode 3 := by decide +kernel

private theorem I_column_04 : reversePack 256 (fun j : Fin 14 => I_digit j 4)=I_columnCode 4 := by decide +kernel

private theorem I_column_05 : reversePack 256 (fun j : Fin 14 => I_digit j 5)=I_columnCode 5 := by decide +kernel

private theorem I_column_06 : reversePack 256 (fun j : Fin 14 => I_digit j 6)=I_columnCode 6 := by decide +kernel

private theorem I_column_07 : reversePack 256 (fun j : Fin 14 => I_digit j 7)=I_columnCode 7 := by decide +kernel

private theorem I_column_08 : reversePack 256 (fun j : Fin 14 => I_digit j 8)=I_columnCode 8 := by decide +kernel

private theorem I_column_09 : reversePack 256 (fun j : Fin 14 => I_digit j 9)=I_columnCode 9 := by decide +kernel

private theorem I_column_10 : reversePack 256 (fun j : Fin 14 => I_digit j 10)=I_columnCode 10 := by decide +kernel

private theorem I_column_11 : reversePack 256 (fun j : Fin 14 => I_digit j 11)=I_columnCode 11 := by decide +kernel

private theorem I_column_12 : reversePack 256 (fun j : Fin 14 => I_digit j 12)=I_columnCode 12 := by decide +kernel

private theorem I_column_13 : reversePack 256 (fun j : Fin 14 => I_digit j 13)=I_columnCode 13 := by decide +kernel

theorem I_column_binding : ∀ i : Fin 14, reversePack 256 (fun j : Fin 14 => I_digit j i)=I_columnCode i := by
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

def I_data : PackedData 14 5 256 where
  raw := I_digit
  digit_lt := I_bound
  rowCode := I_rowCode
  columnCode := I_columnCode
  row_binding := I_row_binding
  column_binding := I_column_binding

private theorem I_one_00 : ∀ j : Fin 14, I_digit 0 j=(1 : Matrix (Fin 14) (Fin 14) ℕ) 0 j := by decide +kernel

private theorem I_one_01 : ∀ j : Fin 14, I_digit 1 j=(1 : Matrix (Fin 14) (Fin 14) ℕ) 1 j := by decide +kernel

private theorem I_one_02 : ∀ j : Fin 14, I_digit 2 j=(1 : Matrix (Fin 14) (Fin 14) ℕ) 2 j := by decide +kernel

private theorem I_one_03 : ∀ j : Fin 14, I_digit 3 j=(1 : Matrix (Fin 14) (Fin 14) ℕ) 3 j := by decide +kernel

private theorem I_one_04 : ∀ j : Fin 14, I_digit 4 j=(1 : Matrix (Fin 14) (Fin 14) ℕ) 4 j := by decide +kernel

private theorem I_one_05 : ∀ j : Fin 14, I_digit 5 j=(1 : Matrix (Fin 14) (Fin 14) ℕ) 5 j := by decide +kernel

private theorem I_one_06 : ∀ j : Fin 14, I_digit 6 j=(1 : Matrix (Fin 14) (Fin 14) ℕ) 6 j := by decide +kernel

private theorem I_one_07 : ∀ j : Fin 14, I_digit 7 j=(1 : Matrix (Fin 14) (Fin 14) ℕ) 7 j := by decide +kernel

private theorem I_one_08 : ∀ j : Fin 14, I_digit 8 j=(1 : Matrix (Fin 14) (Fin 14) ℕ) 8 j := by decide +kernel

private theorem I_one_09 : ∀ j : Fin 14, I_digit 9 j=(1 : Matrix (Fin 14) (Fin 14) ℕ) 9 j := by decide +kernel

private theorem I_one_10 : ∀ j : Fin 14, I_digit 10 j=(1 : Matrix (Fin 14) (Fin 14) ℕ) 10 j := by decide +kernel

private theorem I_one_11 : ∀ j : Fin 14, I_digit 11 j=(1 : Matrix (Fin 14) (Fin 14) ℕ) 11 j := by decide +kernel

private theorem I_one_12 : ∀ j : Fin 14, I_digit 12 j=(1 : Matrix (Fin 14) (Fin 14) ℕ) 12 j := by decide +kernel

private theorem I_one_13 : ∀ j : Fin 14, I_digit 13 j=(1 : Matrix (Fin 14) (Fin 14) ℕ) 13 j := by decide +kernel

theorem identity_binding : I_data.matrix 5=1 := by
  have hraw : I_digit=(1 : Matrix (Fin 14) (Fin 14) ℕ) := by
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
  change castMatrix 5 14 I_digit=1
  rw [hraw,castMatrix_one]

end SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedBaseCaches
