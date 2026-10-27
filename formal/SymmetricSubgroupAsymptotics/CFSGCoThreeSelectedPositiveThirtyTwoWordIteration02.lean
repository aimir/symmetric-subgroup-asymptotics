import SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedPositiveThirtyTwoRows
import SymmetricSubgroupAsymptotics.ListPositiveWordTrajectory

/-! One fixed32-letter word application on its saved vector. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedPositiveThirtyTwoWordIteration02
open MatrixNaturalRowDotReflection MatrixModelSelectedProductPrimePeriod
open CFSG.Models.MatrixGroups.Co3
open CFSGCoThreeSelectedPositiveThirtyTwoRows

private theorem packed_step_0 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 1433506 22 % 2=
      packedDigit 1 5673 z.val % 2 := by decide +kernel

private theorem actual_step_0 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 1433506=vectorCode 5673 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 1433506 5673
    first_row_binding packed_step_0

private theorem packed_step_1 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 5673 22 % 2=
      packedDigit 1 3093904 z.val % 2 := by decide +kernel

private theorem actual_step_1 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 5673=vectorCode 3093904 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 5673 3093904
    second_row_binding packed_step_1

private theorem packed_step_2 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 3093904 22 % 2=
      packedDigit 1 3857640 z.val % 2 := by decide +kernel

private theorem actual_step_2 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 3093904=vectorCode 3857640 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 3093904 3857640
    first_row_binding packed_step_2

private theorem packed_step_3 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 3857640 22 % 2=
      packedDigit 1 485617 z.val % 2 := by decide +kernel

private theorem actual_step_3 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 3857640=vectorCode 485617 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 3857640 485617
    second_row_binding packed_step_3

private theorem packed_step_4 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 485617 22 % 2=
      packedDigit 1 3177799 z.val % 2 := by decide +kernel

private theorem actual_step_4 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 485617=vectorCode 3177799 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 485617 3177799
    first_row_binding packed_step_4

private theorem packed_step_5 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 3177799 22 % 2=
      packedDigit 1 66226 z.val % 2 := by decide +kernel

private theorem actual_step_5 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 3177799=vectorCode 66226 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 3177799 66226
    second_row_binding packed_step_5

private theorem packed_step_6 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 66226 22 % 2=
      packedDigit 1 1069716 z.val % 2 := by decide +kernel

private theorem actual_step_6 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 66226=vectorCode 1069716 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 66226 1069716
    first_row_binding packed_step_6

private theorem packed_step_7 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 1069716 22 % 2=
      packedDigit 1 2136644 z.val % 2 := by decide +kernel

private theorem actual_step_7 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 1069716=vectorCode 2136644 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 1069716 2136644
    first_row_binding packed_step_7

private theorem packed_step_8 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 2136644 22 % 2=
      packedDigit 1 3078800 z.val % 2 := by decide +kernel

private theorem actual_step_8 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 2136644=vectorCode 3078800 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 2136644 3078800
    second_row_binding packed_step_8

private theorem packed_step_9 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 3078800 22 % 2=
      packedDigit 1 2626979 z.val % 2 := by decide +kernel

private theorem actual_step_9 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 3078800=vectorCode 2626979 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 3078800 2626979
    second_row_binding packed_step_9

private theorem packed_step_10 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 2626979 22 % 2=
      packedDigit 1 1246544 z.val % 2 := by decide +kernel

private theorem actual_step_10 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 2626979=vectorCode 1246544 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 2626979 1246544
    second_row_binding packed_step_10

private theorem packed_step_11 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 1246544 22 % 2=
      packedDigit 1 2136644 z.val % 2 := by decide +kernel

private theorem actual_step_11 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 1246544=vectorCode 2136644 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 1246544 2136644
    second_row_binding packed_step_11

private theorem packed_step_12 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 2136644 22 % 2=
      packedDigit 1 3078800 z.val % 2 := by decide +kernel

private theorem actual_step_12 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 2136644=vectorCode 3078800 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 2136644 3078800
    second_row_binding packed_step_12

private theorem packed_step_13 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 3078800 22 % 2=
      packedDigit 1 2626979 z.val % 2 := by decide +kernel

private theorem actual_step_13 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 3078800=vectorCode 2626979 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 3078800 2626979
    second_row_binding packed_step_13

private theorem packed_step_14 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 2626979 22 % 2=
      packedDigit 1 1246544 z.val % 2 := by decide +kernel

private theorem actual_step_14 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 2626979=vectorCode 1246544 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 2626979 1246544
    second_row_binding packed_step_14

private theorem packed_step_15 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 1246544 22 % 2=
      packedDigit 1 950445 z.val % 2 := by decide +kernel

private theorem actual_step_15 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 1246544=vectorCode 950445 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 1246544 950445
    first_row_binding packed_step_15

private theorem packed_step_16 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 950445 22 % 2=
      packedDigit 1 4128223 z.val % 2 := by decide +kernel

private theorem actual_step_16 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 950445=vectorCode 4128223 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 950445 4128223
    first_row_binding packed_step_16

private theorem packed_step_17 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 4128223 22 % 2=
      packedDigit 1 202905 z.val % 2 := by decide +kernel

private theorem actual_step_17 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 4128223=vectorCode 202905 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 4128223 202905
    second_row_binding packed_step_17

private theorem packed_step_18 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 202905 22 % 2=
      packedDigit 1 831622 z.val % 2 := by decide +kernel

private theorem actual_step_18 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 202905=vectorCode 831622 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 202905 831622
    first_row_binding packed_step_18

private theorem packed_step_19 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 831622 22 % 2=
      packedDigit 1 3956213 z.val % 2 := by decide +kernel

private theorem actual_step_19 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 831622=vectorCode 3956213 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 831622 3956213
    second_row_binding packed_step_19

private theorem packed_step_20 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 3956213 22 % 2=
      packedDigit 1 1965949 z.val % 2 := by decide +kernel

private theorem actual_step_20 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 3956213=vectorCode 1965949 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 3956213 1965949
    second_row_binding packed_step_20

private theorem packed_step_21 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 1965949 22 % 2=
      packedDigit 1 1597993 z.val % 2 := by decide +kernel

private theorem actual_step_21 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 1965949=vectorCode 1597993 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 1965949 1597993
    second_row_binding packed_step_21

private theorem packed_step_22 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 1597993 22 % 2=
      packedDigit 1 689312 z.val % 2 := by decide +kernel

private theorem actual_step_22 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 1597993=vectorCode 689312 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 1597993 689312
    first_row_binding packed_step_22

private theorem packed_step_23 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 689312 22 % 2=
      packedDigit 1 727131 z.val % 2 := by decide +kernel

private theorem actual_step_23 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 689312=vectorCode 727131 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 689312 727131
    second_row_binding packed_step_23

private theorem packed_step_24 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 727131 22 % 2=
      packedDigit 1 1507897 z.val % 2 := by decide +kernel

private theorem actual_step_24 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 727131=vectorCode 1507897 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 727131 1507897
    first_row_binding packed_step_24

private theorem packed_step_25 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 1507897 22 % 2=
      packedDigit 1 889113 z.val % 2 := by decide +kernel

private theorem actual_step_25 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 1507897=vectorCode 889113 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 1507897 889113
    first_row_binding packed_step_25

private theorem packed_step_26 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 889113 22 % 2=
      packedDigit 1 727131 z.val % 2 := by decide +kernel

private theorem actual_step_26 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 889113=vectorCode 727131 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 889113 727131
    first_row_binding packed_step_26

private theorem packed_step_27 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 727131 22 % 2=
      packedDigit 1 1507897 z.val % 2 := by decide +kernel

private theorem actual_step_27 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 727131=vectorCode 1507897 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 727131 1507897
    first_row_binding packed_step_27

private theorem packed_step_28 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 1507897 22 % 2=
      packedDigit 1 2006518 z.val % 2 := by decide +kernel

private theorem actual_step_28 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 1507897=vectorCode 2006518 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 1507897 2006518
    second_row_binding packed_step_28

private theorem packed_step_29 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 2006518 22 % 2=
      packedDigit 1 1114384 z.val % 2 := by decide +kernel

private theorem actual_step_29 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 2006518=vectorCode 1114384 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 2006518 1114384
    first_row_binding packed_step_29

private theorem packed_step_30 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 1114384 22 % 2=
      packedDigit 1 3712285 z.val % 2 := by decide +kernel

private theorem actual_step_30 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 1114384=vectorCode 3712285 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 1114384 3712285
    first_row_binding packed_step_30

private theorem packed_step_31 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 3712285 22 % 2=
      packedDigit 1 1181189 z.val % 2 := by decide +kernel

private theorem actual_step_31 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 3712285=vectorCode 1181189 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 3712285 1181189
    second_row_binding packed_step_31

theorem consecutive : wordEnd (vectors 2)=vectors 3 := by
  change (actualWord.map (MatrixModelSelectedPositiveWordPrimePeriod.letterEnd
    2 22 rows1 rows2)).prod (vectors 2)=vectors 3
  apply ListPositiveWordTrajectory.prod_apply_eq_of_steps
    (MatrixModelSelectedPositiveWordPrimePeriod.letterEnd 2 22 rows1 rows2)
    actualWord (vectors 2) (vectors 3)
  have hword : actualWord.reverse=[true,false,true,false,true,false,true,true,false,false,false,false,false,false,false,true,true,false,true,false,false,false,true,false,true,true,true,true,false,true,true,false] := by decide +kernel
  rw [hword]
  exact (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 5673) actual_step_0
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 3093904) actual_step_1
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 3857640) actual_step_2
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 485617) actual_step_3
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 3177799) actual_step_4
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 66226) actual_step_5
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 1069716) actual_step_6
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 2136644) actual_step_7
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 3078800) actual_step_8
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 2626979) actual_step_9
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 1246544) actual_step_10
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 2136644) actual_step_11
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 3078800) actual_step_12
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 2626979) actual_step_13
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 1246544) actual_step_14
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 950445) actual_step_15
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 4128223) actual_step_16
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 202905) actual_step_17
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 831622) actual_step_18
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 3956213) actual_step_19
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 1965949) actual_step_20
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 1597993) actual_step_21
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 689312) actual_step_22
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 727131) actual_step_23
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 1507897) actual_step_24
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 889113) actual_step_25
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 727131) actual_step_26
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 1507897) actual_step_27
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 2006518) actual_step_28
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 1114384) actual_step_29
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 3712285) actual_step_30
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 1181189) actual_step_31
    (ListPositiveWordTrajectory.Steps.nil (vectorCode 1181189))))))))))))))))))))))))))))))))))

end SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedPositiveThirtyTwoWordIteration02
