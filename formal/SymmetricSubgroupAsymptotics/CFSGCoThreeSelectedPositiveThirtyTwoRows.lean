import SymmetricSubgroupAsymptotics.MatrixModelSelectedPositiveWordPrimePeriod
import SymmetricSubgroupAsymptotics.External.CFSG.Models.MatrixGroups.Co3
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedPositiveThirtyTwoRows
open MatrixNaturalRowDotReflection
open CFSG.Models.MatrixGroups.Co3

def firstRowCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 3597713
  | 1 => 3505252
  | 2 => 1155976
  | 3 => 2973176
  | 4 => 711429
  | 5 => 2617603
  | 6 => 308937
  | 7 => 2232327
  | 8 => 3307525
  | 9 => 504129
  | 10 => 2185142
  | 11 => 3316793
  | 12 => 26942
  | 13 => 276805
  | 14 => 3593366
  | 15 => 2730938
  | 16 => 1642907
  | 17 => 3427473
  | 18 => 3507473
  | 19 => 973154
  | 20 => 2073683
  | 21 => 3245210
  | _ => 0

def secondRowCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 2130090
  | 1 => 1655067
  | 2 => 609303
  | 3 => 420067
  | 4 => 2092759
  | 5 => 320367
  | 6 => 3011011
  | 7 => 1658391
  | 8 => 3013763
  | 9 => 528157
  | 10 => 723265
  | 11 => 1821757
  | 12 => 609055
  | 13 => 3334014
  | 14 => 236645
  | 15 => 377144
  | 16 => 2194067
  | 17 => 476088
  | 18 => 2436511
  | 19 => 2545821
  | 20 => 1670160
  | 21 => 932007
  | _ => 0

private theorem first_row_00 : ∀ j : Fin 22,
    rawDigit rows1 0 j.val=packedDigit 1 (firstRowCode 0) j.val := by
  decide +kernel

private theorem first_row_01 : ∀ j : Fin 22,
    rawDigit rows1 1 j.val=packedDigit 1 (firstRowCode 1) j.val := by
  decide +kernel

private theorem first_row_02 : ∀ j : Fin 22,
    rawDigit rows1 2 j.val=packedDigit 1 (firstRowCode 2) j.val := by
  decide +kernel

private theorem first_row_03 : ∀ j : Fin 22,
    rawDigit rows1 3 j.val=packedDigit 1 (firstRowCode 3) j.val := by
  decide +kernel

private theorem first_row_04 : ∀ j : Fin 22,
    rawDigit rows1 4 j.val=packedDigit 1 (firstRowCode 4) j.val := by
  decide +kernel

private theorem first_row_05 : ∀ j : Fin 22,
    rawDigit rows1 5 j.val=packedDigit 1 (firstRowCode 5) j.val := by
  decide +kernel

private theorem first_row_06 : ∀ j : Fin 22,
    rawDigit rows1 6 j.val=packedDigit 1 (firstRowCode 6) j.val := by
  decide +kernel

private theorem first_row_07 : ∀ j : Fin 22,
    rawDigit rows1 7 j.val=packedDigit 1 (firstRowCode 7) j.val := by
  decide +kernel

private theorem first_row_08 : ∀ j : Fin 22,
    rawDigit rows1 8 j.val=packedDigit 1 (firstRowCode 8) j.val := by
  decide +kernel

private theorem first_row_09 : ∀ j : Fin 22,
    rawDigit rows1 9 j.val=packedDigit 1 (firstRowCode 9) j.val := by
  decide +kernel

private theorem first_row_10 : ∀ j : Fin 22,
    rawDigit rows1 10 j.val=packedDigit 1 (firstRowCode 10) j.val := by
  decide +kernel

private theorem first_row_11 : ∀ j : Fin 22,
    rawDigit rows1 11 j.val=packedDigit 1 (firstRowCode 11) j.val := by
  decide +kernel

private theorem first_row_12 : ∀ j : Fin 22,
    rawDigit rows1 12 j.val=packedDigit 1 (firstRowCode 12) j.val := by
  decide +kernel

private theorem first_row_13 : ∀ j : Fin 22,
    rawDigit rows1 13 j.val=packedDigit 1 (firstRowCode 13) j.val := by
  decide +kernel

private theorem first_row_14 : ∀ j : Fin 22,
    rawDigit rows1 14 j.val=packedDigit 1 (firstRowCode 14) j.val := by
  decide +kernel

private theorem first_row_15 : ∀ j : Fin 22,
    rawDigit rows1 15 j.val=packedDigit 1 (firstRowCode 15) j.val := by
  decide +kernel

private theorem first_row_16 : ∀ j : Fin 22,
    rawDigit rows1 16 j.val=packedDigit 1 (firstRowCode 16) j.val := by
  decide +kernel

private theorem first_row_17 : ∀ j : Fin 22,
    rawDigit rows1 17 j.val=packedDigit 1 (firstRowCode 17) j.val := by
  decide +kernel

private theorem first_row_18 : ∀ j : Fin 22,
    rawDigit rows1 18 j.val=packedDigit 1 (firstRowCode 18) j.val := by
  decide +kernel

private theorem first_row_19 : ∀ j : Fin 22,
    rawDigit rows1 19 j.val=packedDigit 1 (firstRowCode 19) j.val := by
  decide +kernel

private theorem first_row_20 : ∀ j : Fin 22,
    rawDigit rows1 20 j.val=packedDigit 1 (firstRowCode 20) j.val := by
  decide +kernel

private theorem first_row_21 : ∀ j : Fin 22,
    rawDigit rows1 21 j.val=packedDigit 1 (firstRowCode 21) j.val := by
  decide +kernel

theorem first_row_binding (i j : Fin 22) :
    rawDigit rows1 i.val j.val=packedDigit 1 (firstRowCode i.val) j.val := by
  fin_cases i
  · exact first_row_00 j
  · exact first_row_01 j
  · exact first_row_02 j
  · exact first_row_03 j
  · exact first_row_04 j
  · exact first_row_05 j
  · exact first_row_06 j
  · exact first_row_07 j
  · exact first_row_08 j
  · exact first_row_09 j
  · exact first_row_10 j
  · exact first_row_11 j
  · exact first_row_12 j
  · exact first_row_13 j
  · exact first_row_14 j
  · exact first_row_15 j
  · exact first_row_16 j
  · exact first_row_17 j
  · exact first_row_18 j
  · exact first_row_19 j
  · exact first_row_20 j
  · exact first_row_21 j

private theorem second_row_00 : ∀ j : Fin 22,
    rawDigit rows2 0 j.val=packedDigit 1 (secondRowCode 0) j.val := by
  decide +kernel

private theorem second_row_01 : ∀ j : Fin 22,
    rawDigit rows2 1 j.val=packedDigit 1 (secondRowCode 1) j.val := by
  decide +kernel

private theorem second_row_02 : ∀ j : Fin 22,
    rawDigit rows2 2 j.val=packedDigit 1 (secondRowCode 2) j.val := by
  decide +kernel

private theorem second_row_03 : ∀ j : Fin 22,
    rawDigit rows2 3 j.val=packedDigit 1 (secondRowCode 3) j.val := by
  decide +kernel

private theorem second_row_04 : ∀ j : Fin 22,
    rawDigit rows2 4 j.val=packedDigit 1 (secondRowCode 4) j.val := by
  decide +kernel

private theorem second_row_05 : ∀ j : Fin 22,
    rawDigit rows2 5 j.val=packedDigit 1 (secondRowCode 5) j.val := by
  decide +kernel

private theorem second_row_06 : ∀ j : Fin 22,
    rawDigit rows2 6 j.val=packedDigit 1 (secondRowCode 6) j.val := by
  decide +kernel

private theorem second_row_07 : ∀ j : Fin 22,
    rawDigit rows2 7 j.val=packedDigit 1 (secondRowCode 7) j.val := by
  decide +kernel

private theorem second_row_08 : ∀ j : Fin 22,
    rawDigit rows2 8 j.val=packedDigit 1 (secondRowCode 8) j.val := by
  decide +kernel

private theorem second_row_09 : ∀ j : Fin 22,
    rawDigit rows2 9 j.val=packedDigit 1 (secondRowCode 9) j.val := by
  decide +kernel

private theorem second_row_10 : ∀ j : Fin 22,
    rawDigit rows2 10 j.val=packedDigit 1 (secondRowCode 10) j.val := by
  decide +kernel

private theorem second_row_11 : ∀ j : Fin 22,
    rawDigit rows2 11 j.val=packedDigit 1 (secondRowCode 11) j.val := by
  decide +kernel

private theorem second_row_12 : ∀ j : Fin 22,
    rawDigit rows2 12 j.val=packedDigit 1 (secondRowCode 12) j.val := by
  decide +kernel

private theorem second_row_13 : ∀ j : Fin 22,
    rawDigit rows2 13 j.val=packedDigit 1 (secondRowCode 13) j.val := by
  decide +kernel

private theorem second_row_14 : ∀ j : Fin 22,
    rawDigit rows2 14 j.val=packedDigit 1 (secondRowCode 14) j.val := by
  decide +kernel

private theorem second_row_15 : ∀ j : Fin 22,
    rawDigit rows2 15 j.val=packedDigit 1 (secondRowCode 15) j.val := by
  decide +kernel

private theorem second_row_16 : ∀ j : Fin 22,
    rawDigit rows2 16 j.val=packedDigit 1 (secondRowCode 16) j.val := by
  decide +kernel

private theorem second_row_17 : ∀ j : Fin 22,
    rawDigit rows2 17 j.val=packedDigit 1 (secondRowCode 17) j.val := by
  decide +kernel

private theorem second_row_18 : ∀ j : Fin 22,
    rawDigit rows2 18 j.val=packedDigit 1 (secondRowCode 18) j.val := by
  decide +kernel

private theorem second_row_19 : ∀ j : Fin 22,
    rawDigit rows2 19 j.val=packedDigit 1 (secondRowCode 19) j.val := by
  decide +kernel

private theorem second_row_20 : ∀ j : Fin 22,
    rawDigit rows2 20 j.val=packedDigit 1 (secondRowCode 20) j.val := by
  decide +kernel

private theorem second_row_21 : ∀ j : Fin 22,
    rawDigit rows2 21 j.val=packedDigit 1 (secondRowCode 21) j.val := by
  decide +kernel

theorem second_row_binding (i j : Fin 22) :
    rawDigit rows2 i.val j.val=packedDigit 1 (secondRowCode i.val) j.val := by
  fin_cases i
  · exact second_row_00 j
  · exact second_row_01 j
  · exact second_row_02 j
  · exact second_row_03 j
  · exact second_row_04 j
  · exact second_row_05 j
  · exact second_row_06 j
  · exact second_row_07 j
  · exact second_row_08 j
  · exact second_row_09 j
  · exact second_row_10 j
  · exact second_row_11 j
  · exact second_row_12 j
  · exact second_row_13 j
  · exact second_row_14 j
  · exact second_row_15 j
  · exact second_row_16 j
  · exact second_row_17 j
  · exact second_row_18 j
  · exact second_row_19 j
  · exact second_row_20 j
  · exact second_row_21 j

abbrev V := Fin 22 → ZMod 2
def vectorCode (code : ℕ) (i : Fin 22) : ZMod 2 := packedDigit 1 code i.val

def boundaryCode (k : ℕ) : ℕ :=
  match k with
  | 0 => 1
  | 1 => 3288828
  | 2 => 1433506
  | 3 => 1181189
  | 4 => 1739298
  | 5 => 3603380
  | 6 => 2262377
  | 7 => 297474
  | 8 => 2371201
  | 9 => 1106579
  | 10 => 3942210
  | 11 => 550008
  | 12 => 1310818
  | 13 => 2306492
  | 14 => 4043114
  | 15 => 4165745
  | 16 => 2623552
  | 17 => 1134594
  | 18 => 1617170
  | 19 => 1716973
  | 20 => 3115514
  | 21 => 1317381
  | 22 => 672264
  | 23 => 1
  | _ => 0

def vectors (i : Fin 24) : V := vectorCode (boundaryCode i.val)

def actualWord : List Bool := [false,true,true,false,true,true,true,true,false,true,false,false,false,true,false,true,true,false,false,false,false,false,false,false,true,true,false,true,false,true,false,true]

def wordEnd : Module.End (ZMod 2) V :=
  MatrixModelSelectedPositiveWordPrimePeriod.wordEnd 2 22 rows1 rows2 actualWord

end SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedPositiveThirtyTwoRows
