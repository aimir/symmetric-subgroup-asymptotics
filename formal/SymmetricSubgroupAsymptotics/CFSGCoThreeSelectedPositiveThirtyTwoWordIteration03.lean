import SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedPositiveThirtyTwoRows
import SymmetricSubgroupAsymptotics.ListPositiveWordTrajectory

/-! One fixed32-letter word application on its saved vector. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedPositiveThirtyTwoWordIteration03
open MatrixNaturalRowDotReflection MatrixModelSelectedProductPrimePeriod
open CFSG.Models.MatrixGroups.Co3
open CFSGCoThreeSelectedPositiveThirtyTwoRows

private theorem packed_step_0 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 1181189 22 % 2=
      packedDigit 1 955594 z.val % 2 := by decide +kernel

private theorem actual_step_0 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 1181189=vectorCode 955594 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 1181189 955594
    first_row_binding packed_step_0

private theorem packed_step_1 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 955594 22 % 2=
      packedDigit 1 1441774 z.val % 2 := by decide +kernel

private theorem actual_step_1 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 955594=vectorCode 1441774 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 955594 1441774
    second_row_binding packed_step_1

private theorem packed_step_2 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 1441774 22 % 2=
      packedDigit 1 2714330 z.val % 2 := by decide +kernel

private theorem actual_step_2 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 1441774=vectorCode 2714330 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 1441774 2714330
    first_row_binding packed_step_2

private theorem packed_step_3 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 2714330 22 % 2=
      packedDigit 1 2179712 z.val % 2 := by decide +kernel

private theorem actual_step_3 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 2714330=vectorCode 2179712 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 2714330 2179712
    second_row_binding packed_step_3

private theorem packed_step_4 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 2179712 22 % 2=
      packedDigit 1 3825319 z.val % 2 := by decide +kernel

private theorem actual_step_4 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 2179712=vectorCode 3825319 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 2179712 3825319
    first_row_binding packed_step_4

private theorem packed_step_5 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 3825319 22 % 2=
      packedDigit 1 2521566 z.val % 2 := by decide +kernel

private theorem actual_step_5 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 3825319=vectorCode 2521566 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 3825319 2521566
    second_row_binding packed_step_5

private theorem packed_step_6 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 2521566 22 % 2=
      packedDigit 1 2122112 z.val % 2 := by decide +kernel

private theorem actual_step_6 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 2521566=vectorCode 2122112 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 2521566 2122112
    first_row_binding packed_step_6

private theorem packed_step_7 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 2122112 22 % 2=
      packedDigit 1 1202567 z.val % 2 := by decide +kernel

private theorem actual_step_7 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 2122112=vectorCode 1202567 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 2122112 1202567
    first_row_binding packed_step_7

private theorem packed_step_8 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 1202567 22 % 2=
      packedDigit 1 2637862 z.val % 2 := by decide +kernel

private theorem actual_step_8 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 1202567=vectorCode 2637862 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 1202567 2637862
    second_row_binding packed_step_8

private theorem packed_step_9 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 2637862 22 % 2=
      packedDigit 1 861195 z.val % 2 := by decide +kernel

private theorem actual_step_9 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 2637862=vectorCode 861195 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 2637862 861195
    second_row_binding packed_step_9

private theorem packed_step_10 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 861195 22 % 2=
      packedDigit 1 3079606 z.val % 2 := by decide +kernel

private theorem actual_step_10 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 861195=vectorCode 3079606 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 861195 3079606
    second_row_binding packed_step_10

private theorem packed_step_11 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 3079606 22 % 2=
      packedDigit 1 1202567 z.val % 2 := by decide +kernel

private theorem actual_step_11 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 3079606=vectorCode 1202567 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 3079606 1202567
    second_row_binding packed_step_11

private theorem packed_step_12 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 1202567 22 % 2=
      packedDigit 1 2637862 z.val % 2 := by decide +kernel

private theorem actual_step_12 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 1202567=vectorCode 2637862 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 1202567 2637862
    second_row_binding packed_step_12

private theorem packed_step_13 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 2637862 22 % 2=
      packedDigit 1 861195 z.val % 2 := by decide +kernel

private theorem actual_step_13 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 2637862=vectorCode 861195 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 2637862 861195
    second_row_binding packed_step_13

private theorem packed_step_14 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 861195 22 % 2=
      packedDigit 1 3079606 z.val % 2 := by decide +kernel

private theorem actual_step_14 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 861195=vectorCode 3079606 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 861195 3079606
    second_row_binding packed_step_14

private theorem packed_step_15 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 3079606 22 % 2=
      packedDigit 1 147882 z.val % 2 := by decide +kernel

private theorem actual_step_15 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 3079606=vectorCode 147882 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 3079606 147882
    first_row_binding packed_step_15

private theorem packed_step_16 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 147882 22 % 2=
      packedDigit 1 2931740 z.val % 2 := by decide +kernel

private theorem actual_step_16 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 147882=vectorCode 2931740 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 147882 2931740
    first_row_binding packed_step_16

private theorem packed_step_17 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 2931740 22 % 2=
      packedDigit 1 219311 z.val % 2 := by decide +kernel

private theorem actual_step_17 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 2931740=vectorCode 219311 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 2931740 219311
    second_row_binding packed_step_17

private theorem packed_step_18 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 219311 22 % 2=
      packedDigit 1 1164 z.val % 2 := by decide +kernel

private theorem actual_step_18 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 219311=vectorCode 1164 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 219311 1164
    first_row_binding packed_step_18

private theorem packed_step_19 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 1164 22 % 2=
      packedDigit 1 1682010 z.val % 2 := by decide +kernel

private theorem actual_step_19 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 1164=vectorCode 1682010 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 1164 1682010
    second_row_binding packed_step_19

private theorem packed_step_20 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 1682010 22 % 2=
      packedDigit 1 6789 z.val % 2 := by decide +kernel

private theorem actual_step_20 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 1682010=vectorCode 6789 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 1682010 6789
    second_row_binding packed_step_20

private theorem packed_step_21 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 6789 22 % 2=
      packedDigit 1 2689151 z.val % 2 := by decide +kernel

private theorem actual_step_21 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 6789=vectorCode 2689151 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 6789 2689151
    second_row_binding packed_step_21

private theorem packed_step_22 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 2689151 22 % 2=
      packedDigit 1 2622017 z.val % 2 := by decide +kernel

private theorem actual_step_22 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 2689151=vectorCode 2622017 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 2689151 2622017
    first_row_binding packed_step_22

private theorem packed_step_23 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 2622017 22 % 2=
      packedDigit 1 1259425 z.val % 2 := by decide +kernel

private theorem actual_step_23 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 2622017=vectorCode 1259425 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 2622017 1259425
    second_row_binding packed_step_23

private theorem packed_step_24 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 1259425 22 % 2=
      packedDigit 1 284049 z.val % 2 := by decide +kernel

private theorem actual_step_24 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 1259425=vectorCode 284049 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 1259425 284049
    first_row_binding packed_step_24

private theorem packed_step_25 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 284049 22 % 2=
      packedDigit 1 2462057 z.val % 2 := by decide +kernel

private theorem actual_step_25 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 284049=vectorCode 2462057 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 284049 2462057
    first_row_binding packed_step_25

private theorem packed_step_26 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 2462057 22 % 2=
      packedDigit 1 1259425 z.val % 2 := by decide +kernel

private theorem actual_step_26 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 2462057=vectorCode 1259425 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 2462057 1259425
    first_row_binding packed_step_26

private theorem packed_step_27 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 1259425 22 % 2=
      packedDigit 1 284049 z.val % 2 := by decide +kernel

private theorem actual_step_27 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 1259425=vectorCode 284049 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 1259425 284049
    first_row_binding packed_step_27

private theorem packed_step_28 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 284049 22 % 2=
      packedDigit 1 221185 z.val % 2 := by decide +kernel

private theorem actual_step_28 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 284049=vectorCode 221185 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 284049 221185
    second_row_binding packed_step_28

private theorem packed_step_29 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 221185 22 % 2=
      packedDigit 1 2097202 z.val % 2 := by decide +kernel

private theorem actual_step_29 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 221185=vectorCode 2097202 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 221185 2097202
    first_row_binding packed_step_29

private theorem packed_step_30 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 2097202 22 % 2=
      packedDigit 1 2119944 z.val % 2 := by decide +kernel

private theorem actual_step_30 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 2097202=vectorCode 2119944 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 2097202 2119944
    first_row_binding packed_step_30

private theorem packed_step_31 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 2119944 22 % 2=
      packedDigit 1 1739298 z.val % 2 := by decide +kernel

private theorem actual_step_31 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 2119944=vectorCode 1739298 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 2119944 1739298
    second_row_binding packed_step_31

theorem consecutive : wordEnd (vectors 3)=vectors 4 := by
  change (actualWord.map (MatrixModelSelectedPositiveWordPrimePeriod.letterEnd
    2 22 rows1 rows2)).prod (vectors 3)=vectors 4
  apply ListPositiveWordTrajectory.prod_apply_eq_of_steps
    (MatrixModelSelectedPositiveWordPrimePeriod.letterEnd 2 22 rows1 rows2)
    actualWord (vectors 3) (vectors 4)
  have hword : actualWord.reverse=[true,false,true,false,true,false,true,true,false,false,false,false,false,false,false,true,true,false,true,false,false,false,true,false,true,true,true,true,false,true,true,false] := by decide +kernel
  rw [hword]
  exact (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 955594) actual_step_0
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 1441774) actual_step_1
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 2714330) actual_step_2
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 2179712) actual_step_3
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 3825319) actual_step_4
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 2521566) actual_step_5
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 2122112) actual_step_6
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 1202567) actual_step_7
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 2637862) actual_step_8
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 861195) actual_step_9
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 3079606) actual_step_10
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 1202567) actual_step_11
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 2637862) actual_step_12
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 861195) actual_step_13
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 3079606) actual_step_14
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 147882) actual_step_15
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 2931740) actual_step_16
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 219311) actual_step_17
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 1164) actual_step_18
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 1682010) actual_step_19
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 6789) actual_step_20
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 2689151) actual_step_21
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 2622017) actual_step_22
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 1259425) actual_step_23
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 284049) actual_step_24
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 2462057) actual_step_25
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 1259425) actual_step_26
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 284049) actual_step_27
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 221185) actual_step_28
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 2097202) actual_step_29
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 2119944) actual_step_30
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 1739298) actual_step_31
    (ListPositiveWordTrajectory.Steps.nil (vectorCode 1739298))))))))))))))))))))))))))))))))))

end SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedPositiveThirtyTwoWordIteration03
