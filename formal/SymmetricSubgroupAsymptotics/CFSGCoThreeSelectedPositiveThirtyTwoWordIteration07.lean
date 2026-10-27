import SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedPositiveThirtyTwoRows
import SymmetricSubgroupAsymptotics.ListPositiveWordTrajectory

/-! One fixed32-letter word application on its saved vector. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedPositiveThirtyTwoWordIteration07
open MatrixNaturalRowDotReflection MatrixModelSelectedProductPrimePeriod
open CFSG.Models.MatrixGroups.Co3
open CFSGCoThreeSelectedPositiveThirtyTwoRows

private theorem packed_step_0 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 297474 22 % 2=
      packedDigit 1 1130992 z.val % 2 := by decide +kernel

private theorem actual_step_0 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 297474=vectorCode 1130992 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 297474 1130992
    first_row_binding packed_step_0

private theorem packed_step_1 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 1130992 22 % 2=
      packedDigit 1 576838 z.val % 2 := by decide +kernel

private theorem actual_step_1 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 1130992=vectorCode 576838 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 1130992 576838
    second_row_binding packed_step_1

private theorem packed_step_2 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 576838 22 % 2=
      packedDigit 1 4185922 z.val % 2 := by decide +kernel

private theorem actual_step_2 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 576838=vectorCode 4185922 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 576838 4185922
    first_row_binding packed_step_2

private theorem packed_step_3 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 4185922 22 % 2=
      packedDigit 1 1954337 z.val % 2 := by decide +kernel

private theorem actual_step_3 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 4185922=vectorCode 1954337 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 4185922 1954337
    second_row_binding packed_step_3

private theorem packed_step_4 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 1954337 22 % 2=
      packedDigit 1 2485825 z.val % 2 := by decide +kernel

private theorem actual_step_4 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 1954337=vectorCode 2485825 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 1954337 2485825
    first_row_binding packed_step_4

private theorem packed_step_5 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 2485825 22 % 2=
      packedDigit 1 1388838 z.val % 2 := by decide +kernel

private theorem actual_step_5 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 2485825=vectorCode 1388838 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 2485825 1388838
    second_row_binding packed_step_5

private theorem packed_step_6 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 1388838 22 % 2=
      packedDigit 1 3799770 z.val % 2 := by decide +kernel

private theorem actual_step_6 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 1388838=vectorCode 3799770 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 1388838 3799770
    first_row_binding packed_step_6

private theorem packed_step_7 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 3799770 22 % 2=
      packedDigit 1 821989 z.val % 2 := by decide +kernel

private theorem actual_step_7 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 3799770=vectorCode 821989 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 3799770 821989
    first_row_binding packed_step_7

private theorem packed_step_8 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 821989 22 % 2=
      packedDigit 1 2396849 z.val % 2 := by decide +kernel

private theorem actual_step_8 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 821989=vectorCode 2396849 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 821989 2396849
    second_row_binding packed_step_8

private theorem packed_step_9 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 2396849 22 % 2=
      packedDigit 1 3020448 z.val % 2 := by decide +kernel

private theorem actual_step_9 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 2396849=vectorCode 3020448 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 2396849 3020448
    second_row_binding packed_step_9

private theorem packed_step_10 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 3020448 22 % 2=
      packedDigit 1 1704675 z.val % 2 := by decide +kernel

private theorem actual_step_10 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 3020448=vectorCode 1704675 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 3020448 1704675
    second_row_binding packed_step_10

private theorem packed_step_11 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 1704675 22 % 2=
      packedDigit 1 821989 z.val % 2 := by decide +kernel

private theorem actual_step_11 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 1704675=vectorCode 821989 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 1704675 821989
    second_row_binding packed_step_11

private theorem packed_step_12 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 821989 22 % 2=
      packedDigit 1 2396849 z.val % 2 := by decide +kernel

private theorem actual_step_12 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 821989=vectorCode 2396849 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 821989 2396849
    second_row_binding packed_step_12

private theorem packed_step_13 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 2396849 22 % 2=
      packedDigit 1 3020448 z.val % 2 := by decide +kernel

private theorem actual_step_13 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 2396849=vectorCode 3020448 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 2396849 3020448
    second_row_binding packed_step_13

private theorem packed_step_14 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 3020448 22 % 2=
      packedDigit 1 1704675 z.val % 2 := by decide +kernel

private theorem actual_step_14 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 3020448=vectorCode 1704675 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 3020448 1704675
    second_row_binding packed_step_14

private theorem packed_step_15 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 1704675 22 % 2=
      packedDigit 1 2851750 z.val % 2 := by decide +kernel

private theorem actual_step_15 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 1704675=vectorCode 2851750 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 1704675 2851750
    first_row_binding packed_step_15

private theorem packed_step_16 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 2851750 22 % 2=
      packedDigit 1 3244357 z.val % 2 := by decide +kernel

private theorem actual_step_16 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 2851750=vectorCode 3244357 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 2851750 3244357
    first_row_binding packed_step_16

private theorem packed_step_17 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 3244357 22 % 2=
      packedDigit 1 379428 z.val % 2 := by decide +kernel

private theorem actual_step_17 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 3244357=vectorCode 379428 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 3244357 379428
    second_row_binding packed_step_17

private theorem packed_step_18 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 379428 22 % 2=
      packedDigit 1 2076637 z.val % 2 := by decide +kernel

private theorem actual_step_18 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 379428=vectorCode 2076637 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 379428 2076637
    first_row_binding packed_step_18

private theorem packed_step_19 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 2076637 22 % 2=
      packedDigit 1 1916927 z.val % 2 := by decide +kernel

private theorem actual_step_19 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 2076637=vectorCode 1916927 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 2076637 1916927
    second_row_binding packed_step_19

private theorem packed_step_20 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 1916927 22 % 2=
      packedDigit 1 66048 z.val % 2 := by decide +kernel

private theorem actual_step_20 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 1916927=vectorCode 66048 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 1916927 66048
    second_row_binding packed_step_20

private theorem packed_step_21 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 66048 22 % 2=
      packedDigit 1 1372006 z.val % 2 := by decide +kernel

private theorem actual_step_21 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 66048=vectorCode 1372006 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 66048 1372006
    second_row_binding packed_step_21

private theorem packed_step_22 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 1372006 22 % 2=
      packedDigit 1 1564431 z.val % 2 := by decide +kernel

private theorem actual_step_22 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 1372006=vectorCode 1564431 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 1372006 1564431
    first_row_binding packed_step_22

private theorem packed_step_23 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 1564431 22 % 2=
      packedDigit 1 3086247 z.val % 2 := by decide +kernel

private theorem actual_step_23 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 1564431=vectorCode 3086247 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 1564431 3086247
    second_row_binding packed_step_23

private theorem packed_step_24 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 3086247 22 % 2=
      packedDigit 1 3875099 z.val % 2 := by decide +kernel

private theorem actual_step_24 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 3086247=vectorCode 3875099 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 3086247 3875099
    first_row_binding packed_step_24

private theorem packed_step_25 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 3875099 22 % 2=
      packedDigit 1 30565 z.val % 2 := by decide +kernel

private theorem actual_step_25 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 3875099=vectorCode 30565 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 3875099 30565
    first_row_binding packed_step_25

private theorem packed_step_26 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 30565 22 % 2=
      packedDigit 1 3086247 z.val % 2 := by decide +kernel

private theorem actual_step_26 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 30565=vectorCode 3086247 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 30565 3086247
    first_row_binding packed_step_26

private theorem packed_step_27 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 3086247 22 % 2=
      packedDigit 1 3875099 z.val % 2 := by decide +kernel

private theorem actual_step_27 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 3086247=vectorCode 3875099 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 3086247 3875099
    first_row_binding packed_step_27

private theorem packed_step_28 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 3875099 22 % 2=
      packedDigit 1 3833445 z.val % 2 := by decide +kernel

private theorem actual_step_28 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 3875099=vectorCode 3833445 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 3875099 3833445
    second_row_binding packed_step_28

private theorem packed_step_29 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 3833445 22 % 2=
      packedDigit 1 3692421 z.val % 2 := by decide +kernel

private theorem actual_step_29 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 3833445=vectorCode 3692421 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 3833445 3692421
    first_row_binding packed_step_29

private theorem packed_step_30 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 3692421 22 % 2=
      packedDigit 1 318073 z.val % 2 := by decide +kernel

private theorem actual_step_30 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 3692421=vectorCode 318073 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 3692421 318073
    first_row_binding packed_step_30

private theorem packed_step_31 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 318073 22 % 2=
      packedDigit 1 2371201 z.val % 2 := by decide +kernel

private theorem actual_step_31 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 318073=vectorCode 2371201 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 318073 2371201
    second_row_binding packed_step_31

theorem consecutive : wordEnd (vectors 7)=vectors 8 := by
  change (actualWord.map (MatrixModelSelectedPositiveWordPrimePeriod.letterEnd
    2 22 rows1 rows2)).prod (vectors 7)=vectors 8
  apply ListPositiveWordTrajectory.prod_apply_eq_of_steps
    (MatrixModelSelectedPositiveWordPrimePeriod.letterEnd 2 22 rows1 rows2)
    actualWord (vectors 7) (vectors 8)
  have hword : actualWord.reverse=[true,false,true,false,true,false,true,true,false,false,false,false,false,false,false,true,true,false,true,false,false,false,true,false,true,true,true,true,false,true,true,false] := by decide +kernel
  rw [hword]
  exact (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 1130992) actual_step_0
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 576838) actual_step_1
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 4185922) actual_step_2
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 1954337) actual_step_3
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 2485825) actual_step_4
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 1388838) actual_step_5
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 3799770) actual_step_6
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 821989) actual_step_7
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 2396849) actual_step_8
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 3020448) actual_step_9
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 1704675) actual_step_10
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 821989) actual_step_11
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 2396849) actual_step_12
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 3020448) actual_step_13
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 1704675) actual_step_14
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 2851750) actual_step_15
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 3244357) actual_step_16
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 379428) actual_step_17
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 2076637) actual_step_18
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 1916927) actual_step_19
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 66048) actual_step_20
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 1372006) actual_step_21
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 1564431) actual_step_22
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 3086247) actual_step_23
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 3875099) actual_step_24
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 30565) actual_step_25
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 3086247) actual_step_26
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 3875099) actual_step_27
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 3833445) actual_step_28
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 3692421) actual_step_29
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 318073) actual_step_30
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 2371201) actual_step_31
    (ListPositiveWordTrajectory.Steps.nil (vectorCode 2371201))))))))))))))))))))))))))))))))))

end SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedPositiveThirtyTwoWordIteration07
