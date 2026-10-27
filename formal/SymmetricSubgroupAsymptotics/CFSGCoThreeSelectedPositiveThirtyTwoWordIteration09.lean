import SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedPositiveThirtyTwoRows
import SymmetricSubgroupAsymptotics.ListPositiveWordTrajectory

/-! One fixed32-letter word application on its saved vector. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedPositiveThirtyTwoWordIteration09
open MatrixNaturalRowDotReflection MatrixModelSelectedProductPrimePeriod
open CFSG.Models.MatrixGroups.Co3
open CFSGCoThreeSelectedPositiveThirtyTwoRows

private theorem packed_step_0 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 1106579 22 % 2=
      packedDigit 1 2819695 z.val % 2 := by decide +kernel

private theorem actual_step_0 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 1106579=vectorCode 2819695 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 1106579 2819695
    first_row_binding packed_step_0

private theorem packed_step_1 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 2819695 22 % 2=
      packedDigit 1 2094266 z.val % 2 := by decide +kernel

private theorem actual_step_1 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 2819695=vectorCode 2094266 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 2819695 2094266
    second_row_binding packed_step_1

private theorem packed_step_2 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 2094266 22 % 2=
      packedDigit 1 41425 z.val % 2 := by decide +kernel

private theorem actual_step_2 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 2094266=vectorCode 41425 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 2094266 41425
    first_row_binding packed_step_2

private theorem packed_step_3 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 41425 22 % 2=
      packedDigit 1 2547234 z.val % 2 := by decide +kernel

private theorem actual_step_3 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 41425=vectorCode 2547234 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 41425 2547234
    second_row_binding packed_step_3

private theorem packed_step_4 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 2547234 22 % 2=
      packedDigit 1 1191274 z.val % 2 := by decide +kernel

private theorem actual_step_4 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 2547234=vectorCode 1191274 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 2547234 1191274
    first_row_binding packed_step_4

private theorem packed_step_5 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 1191274 22 % 2=
      packedDigit 1 2744341 z.val % 2 := by decide +kernel

private theorem actual_step_5 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 1191274=vectorCode 2744341 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 1191274 2744341
    second_row_binding packed_step_5

private theorem packed_step_6 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 2744341 22 % 2=
      packedDigit 1 812510 z.val % 2 := by decide +kernel

private theorem actual_step_6 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 2744341=vectorCode 812510 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 2744341 812510
    first_row_binding packed_step_6

private theorem packed_step_7 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 812510 22 % 2=
      packedDigit 1 3341609 z.val % 2 := by decide +kernel

private theorem actual_step_7 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 812510=vectorCode 3341609 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 812510 3341609
    first_row_binding packed_step_7

private theorem packed_step_8 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 3341609 22 % 2=
      packedDigit 1 457442 z.val % 2 := by decide +kernel

private theorem actual_step_8 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 3341609=vectorCode 457442 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 3341609 457442
    second_row_binding packed_step_8

private theorem packed_step_9 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 457442 22 % 2=
      packedDigit 1 863244 z.val % 2 := by decide +kernel

private theorem actual_step_9 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 457442=vectorCode 863244 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 457442 863244
    second_row_binding packed_step_9

private theorem packed_step_10 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 863244 22 % 2=
      packedDigit 1 3643039 z.val % 2 := by decide +kernel

private theorem actual_step_10 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 863244=vectorCode 3643039 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 863244 3643039
    second_row_binding packed_step_10

private theorem packed_step_11 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 3643039 22 % 2=
      packedDigit 1 3341609 z.val % 2 := by decide +kernel

private theorem actual_step_11 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 3643039=vectorCode 3341609 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 3643039 3341609
    second_row_binding packed_step_11

private theorem packed_step_12 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 3341609 22 % 2=
      packedDigit 1 457442 z.val % 2 := by decide +kernel

private theorem actual_step_12 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 3341609=vectorCode 457442 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 3341609 457442
    second_row_binding packed_step_12

private theorem packed_step_13 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 457442 22 % 2=
      packedDigit 1 863244 z.val % 2 := by decide +kernel

private theorem actual_step_13 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 457442=vectorCode 863244 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 457442 863244
    second_row_binding packed_step_13

private theorem packed_step_14 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 863244 22 % 2=
      packedDigit 1 3643039 z.val % 2 := by decide +kernel

private theorem actual_step_14 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 863244=vectorCode 3643039 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 863244 3643039
    second_row_binding packed_step_14

private theorem packed_step_15 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 3643039 22 % 2=
      packedDigit 1 3820547 z.val % 2 := by decide +kernel

private theorem actual_step_15 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 3643039=vectorCode 3820547 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 3643039 3820547
    first_row_binding packed_step_15

private theorem packed_step_16 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 3820547 22 % 2=
      packedDigit 1 528446 z.val % 2 := by decide +kernel

private theorem actual_step_16 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 3820547=vectorCode 528446 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 3820547 528446
    first_row_binding packed_step_16

private theorem packed_step_17 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 528446 22 % 2=
      packedDigit 1 3398977 z.val % 2 := by decide +kernel

private theorem actual_step_17 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 528446=vectorCode 3398977 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 528446 3398977
    second_row_binding packed_step_17

private theorem packed_step_18 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 3398977 22 % 2=
      packedDigit 1 4059984 z.val % 2 := by decide +kernel

private theorem actual_step_18 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 3398977=vectorCode 4059984 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 3398977 4059984
    first_row_binding packed_step_18

private theorem packed_step_19 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 4059984 22 % 2=
      packedDigit 1 1122336 z.val % 2 := by decide +kernel

private theorem actual_step_19 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 4059984=vectorCode 1122336 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 4059984 1122336
    second_row_binding packed_step_19

private theorem packed_step_20 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 1122336 22 % 2=
      packedDigit 1 1055765 z.val % 2 := by decide +kernel

private theorem actual_step_20 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 1122336=vectorCode 1055765 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 1122336 1055765
    second_row_binding packed_step_20

private theorem packed_step_21 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 1055765 22 % 2=
      packedDigit 1 2015750 z.val % 2 := by decide +kernel

private theorem actual_step_21 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 1055765=vectorCode 2015750 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 1055765 2015750
    second_row_binding packed_step_21

private theorem packed_step_22 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 2015750 22 % 2=
      packedDigit 1 2579181 z.val % 2 := by decide +kernel

private theorem actual_step_22 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 2015750=vectorCode 2579181 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 2015750 2579181
    first_row_binding packed_step_22

private theorem packed_step_23 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 2579181 22 % 2=
      packedDigit 1 38404 z.val % 2 := by decide +kernel

private theorem actual_step_23 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 2579181=vectorCode 38404 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 2579181 38404
    second_row_binding packed_step_23

private theorem packed_step_24 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 38404 22 % 2=
      packedDigit 1 202754 z.val % 2 := by decide +kernel

private theorem actual_step_24 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 38404=vectorCode 202754 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 38404 202754
    first_row_binding packed_step_24

private theorem packed_step_25 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 202754 22 % 2=
      packedDigit 1 1560543 z.val % 2 := by decide +kernel

private theorem actual_step_25 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 202754=vectorCode 1560543 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 202754 1560543
    first_row_binding packed_step_25

private theorem packed_step_26 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 1560543 22 % 2=
      packedDigit 1 38404 z.val % 2 := by decide +kernel

private theorem actual_step_26 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 1560543=vectorCode 38404 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 1560543 38404
    first_row_binding packed_step_26

private theorem packed_step_27 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 38404 22 % 2=
      packedDigit 1 202754 z.val % 2 := by decide +kernel

private theorem actual_step_27 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 38404=vectorCode 202754 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 38404 202754
    first_row_binding packed_step_27

private theorem packed_step_28 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 202754 22 % 2=
      packedDigit 1 1875693 z.val % 2 := by decide +kernel

private theorem actual_step_28 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 202754=vectorCode 1875693 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 202754 1875693
    second_row_binding packed_step_28

private theorem packed_step_29 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 1875693 22 % 2=
      packedDigit 1 3982300 z.val % 2 := by decide +kernel

private theorem actual_step_29 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 1875693=vectorCode 3982300 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 1875693 3982300
    first_row_binding packed_step_29

private theorem packed_step_30 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 3982300 22 % 2=
      packedDigit 1 7208 z.val % 2 := by decide +kernel

private theorem actual_step_30 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 3982300=vectorCode 7208 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 3982300 7208
    first_row_binding packed_step_30

private theorem packed_step_31 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 7208 22 % 2=
      packedDigit 1 3942210 z.val % 2 := by decide +kernel

private theorem actual_step_31 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 7208=vectorCode 3942210 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 7208 3942210
    second_row_binding packed_step_31

theorem consecutive : wordEnd (vectors 9)=vectors 10 := by
  change (actualWord.map (MatrixModelSelectedPositiveWordPrimePeriod.letterEnd
    2 22 rows1 rows2)).prod (vectors 9)=vectors 10
  apply ListPositiveWordTrajectory.prod_apply_eq_of_steps
    (MatrixModelSelectedPositiveWordPrimePeriod.letterEnd 2 22 rows1 rows2)
    actualWord (vectors 9) (vectors 10)
  have hword : actualWord.reverse=[true,false,true,false,true,false,true,true,false,false,false,false,false,false,false,true,true,false,true,false,false,false,true,false,true,true,true,true,false,true,true,false] := by decide +kernel
  rw [hword]
  exact (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 2819695) actual_step_0
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 2094266) actual_step_1
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 41425) actual_step_2
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 2547234) actual_step_3
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 1191274) actual_step_4
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 2744341) actual_step_5
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 812510) actual_step_6
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 3341609) actual_step_7
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 457442) actual_step_8
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 863244) actual_step_9
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 3643039) actual_step_10
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 3341609) actual_step_11
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 457442) actual_step_12
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 863244) actual_step_13
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 3643039) actual_step_14
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 3820547) actual_step_15
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 528446) actual_step_16
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 3398977) actual_step_17
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 4059984) actual_step_18
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 1122336) actual_step_19
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 1055765) actual_step_20
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 2015750) actual_step_21
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 2579181) actual_step_22
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 38404) actual_step_23
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 202754) actual_step_24
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 1560543) actual_step_25
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 38404) actual_step_26
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 202754) actual_step_27
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 1875693) actual_step_28
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 3982300) actual_step_29
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 7208) actual_step_30
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 3942210) actual_step_31
    (ListPositiveWordTrajectory.Steps.nil (vectorCode 3942210))))))))))))))))))))))))))))))))))

end SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedPositiveThirtyTwoWordIteration09
