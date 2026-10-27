import SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedPositiveThirtyTwoRows
import SymmetricSubgroupAsymptotics.ListPositiveWordTrajectory
import SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedPositiveThirtyTwoFirstEightPilot

/-! One fixed32-letter word application on its saved vector. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedPositiveThirtyTwoWordIteration00
open MatrixNaturalRowDotReflection MatrixModelSelectedProductPrimePeriod
open CFSG.Models.MatrixGroups.Co3
open CFSGCoThreeSelectedPositiveThirtyTwoRows

private theorem packed_step_8 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 4031899 22 % 2=
      packedDigit 1 3674561 z.val % 2 := by decide +kernel

private theorem actual_step_8 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 4031899=vectorCode 3674561 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 4031899 3674561
    second_row_binding packed_step_8

private theorem packed_step_9 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 3674561 22 % 2=
      packedDigit 1 1113080 z.val % 2 := by decide +kernel

private theorem actual_step_9 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 3674561=vectorCode 1113080 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 3674561 1113080
    second_row_binding packed_step_9

private theorem packed_step_10 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 1113080 22 % 2=
      packedDigit 1 2846422 z.val % 2 := by decide +kernel

private theorem actual_step_10 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 1113080=vectorCode 2846422 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 1113080 2846422
    second_row_binding packed_step_10

private theorem packed_step_11 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 2846422 22 % 2=
      packedDigit 1 4031899 z.val % 2 := by decide +kernel

private theorem actual_step_11 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 2846422=vectorCode 4031899 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 2846422 4031899
    second_row_binding packed_step_11

private theorem packed_step_12 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 4031899 22 % 2=
      packedDigit 1 3674561 z.val % 2 := by decide +kernel

private theorem actual_step_12 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 4031899=vectorCode 3674561 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 4031899 3674561
    second_row_binding packed_step_12

private theorem packed_step_13 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 3674561 22 % 2=
      packedDigit 1 1113080 z.val % 2 := by decide +kernel

private theorem actual_step_13 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 3674561=vectorCode 1113080 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 3674561 1113080
    second_row_binding packed_step_13

private theorem packed_step_14 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 1113080 22 % 2=
      packedDigit 1 2846422 z.val % 2 := by decide +kernel

private theorem actual_step_14 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 1113080=vectorCode 2846422 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 1113080 2846422
    second_row_binding packed_step_14

private theorem packed_step_15 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 2846422 22 % 2=
      packedDigit 1 101449 z.val % 2 := by decide +kernel

private theorem actual_step_15 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 2846422=vectorCode 101449 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 2846422 101449
    first_row_binding packed_step_15

private theorem packed_step_16 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 101449 22 % 2=
      packedDigit 1 1779965 z.val % 2 := by decide +kernel

private theorem actual_step_16 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 101449=vectorCode 1779965 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 101449 1779965
    first_row_binding packed_step_16

private theorem packed_step_17 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 1779965 22 % 2=
      packedDigit 1 544921 z.val % 2 := by decide +kernel

private theorem actual_step_17 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 1779965=vectorCode 544921 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 1779965 544921
    second_row_binding packed_step_17

private theorem packed_step_18 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 544921 22 % 2=
      packedDigit 1 3674400 z.val % 2 := by decide +kernel

private theorem actual_step_18 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 544921=vectorCode 3674400 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 544921 3674400
    first_row_binding packed_step_18

private theorem packed_step_19 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 3674400 22 % 2=
      packedDigit 1 3156238 z.val % 2 := by decide +kernel

private theorem actual_step_19 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 3674400=vectorCode 3156238 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 3674400 3156238
    second_row_binding packed_step_19

private theorem packed_step_20 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 3156238 22 % 2=
      packedDigit 1 1323069 z.val % 2 := by decide +kernel

private theorem actual_step_20 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 3156238=vectorCode 1323069 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 3156238 1323069
    second_row_binding packed_step_20

private theorem packed_step_21 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 1323069 22 % 2=
      packedDigit 1 1028 z.val % 2 := by decide +kernel

private theorem actual_step_21 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 1323069=vectorCode 1028 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 1323069 1028
    second_row_binding packed_step_21

private theorem packed_step_22 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 1028 22 % 2=
      packedDigit 1 3553753 z.val % 2 := by decide +kernel

private theorem actual_step_22 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 1028=vectorCode 3553753 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 1028 3553753
    first_row_binding packed_step_22

private theorem packed_step_23 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 3553753 22 % 2=
      packedDigit 1 4028191 z.val % 2 := by decide +kernel

private theorem actual_step_23 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 3553753=vectorCode 4028191 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 3553753 4028191
    second_row_binding packed_step_23

private theorem packed_step_24 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 4028191 22 % 2=
      packedDigit 1 3398131 z.val % 2 := by decide +kernel

private theorem actual_step_24 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 4028191=vectorCode 3398131 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 4028191 3398131
    first_row_binding packed_step_24

private theorem packed_step_25 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 3398131 22 % 2=
      packedDigit 1 3076085 z.val % 2 := by decide +kernel

private theorem actual_step_25 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 3398131=vectorCode 3076085 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 3398131 3076085
    first_row_binding packed_step_25

private theorem packed_step_26 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 3076085 22 % 2=
      packedDigit 1 4028191 z.val % 2 := by decide +kernel

private theorem actual_step_26 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 3076085=vectorCode 4028191 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 3076085 4028191
    first_row_binding packed_step_26

private theorem packed_step_27 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 4028191 22 % 2=
      packedDigit 1 3398131 z.val % 2 := by decide +kernel

private theorem actual_step_27 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 4028191=vectorCode 3398131 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 4028191 3398131
    first_row_binding packed_step_27

private theorem packed_step_28 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 3398131 22 % 2=
      packedDigit 1 2824627 z.val % 2 := by decide +kernel

private theorem actual_step_28 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 3398131=vectorCode 2824627 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 3398131 2824627
    second_row_binding packed_step_28

private theorem packed_step_29 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 2824627 22 % 2=
      packedDigit 1 3054574 z.val % 2 := by decide +kernel

private theorem actual_step_29 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 2824627=vectorCode 3054574 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 2824627 3054574
    first_row_binding packed_step_29

private theorem packed_step_30 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 3054574 22 % 2=
      packedDigit 1 2099686 z.val % 2 := by decide +kernel

private theorem actual_step_30 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 3054574=vectorCode 2099686 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 3054574 2099686
    first_row_binding packed_step_30

private theorem packed_step_31 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 2099686 22 % 2=
      packedDigit 1 3288828 z.val % 2 := by decide +kernel

private theorem actual_step_31 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 2099686=vectorCode 3288828 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 2099686 3288828
    second_row_binding packed_step_31

theorem consecutive : wordEnd (vectors 0)=vectors 1 := by
  change (actualWord.map (MatrixModelSelectedPositiveWordPrimePeriod.letterEnd
    2 22 rows1 rows2)).prod (vectors 0)=vectors 1
  apply ListPositiveWordTrajectory.prod_apply_eq_of_steps
    (MatrixModelSelectedPositiveWordPrimePeriod.letterEnd 2 22 rows1 rows2)
    actualWord (vectors 0) (vectors 1)
  have hword : actualWord.reverse=[true,false,true,false,true,false,true,true,false,false,false,false,false,false,false,true,true,false,true,false,false,false,true,false,true,true,true,true,false,true,true,false] := by decide +kernel
  rw [hword]
  exact (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 1518577) CFSGCoThreeSelectedPositiveThirtyTwoFirstEightPilot.actual_step_0
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 3246706) CFSGCoThreeSelectedPositiveThirtyTwoFirstEightPilot.actual_step_1
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 803664) CFSGCoThreeSelectedPositiveThirtyTwoFirstEightPilot.actual_step_2
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 2063724) CFSGCoThreeSelectedPositiveThirtyTwoFirstEightPilot.actual_step_3
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 982975) CFSGCoThreeSelectedPositiveThirtyTwoFirstEightPilot.actual_step_4
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 4173739) CFSGCoThreeSelectedPositiveThirtyTwoFirstEightPilot.actual_step_5
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 141872) CFSGCoThreeSelectedPositiveThirtyTwoFirstEightPilot.actual_step_6
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 4031899) CFSGCoThreeSelectedPositiveThirtyTwoFirstEightPilot.actual_step_7
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 3674561) actual_step_8
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 1113080) actual_step_9
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 2846422) actual_step_10
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 4031899) actual_step_11
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 3674561) actual_step_12
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 1113080) actual_step_13
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 2846422) actual_step_14
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 101449) actual_step_15
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 1779965) actual_step_16
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 544921) actual_step_17
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 3674400) actual_step_18
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 3156238) actual_step_19
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 1323069) actual_step_20
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 1028) actual_step_21
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 3553753) actual_step_22
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 4028191) actual_step_23
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 3398131) actual_step_24
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 3076085) actual_step_25
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 4028191) actual_step_26
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 3398131) actual_step_27
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 2824627) actual_step_28
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 3054574) actual_step_29
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 2099686) actual_step_30
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 3288828) actual_step_31
    (ListPositiveWordTrajectory.Steps.nil (vectorCode 3288828))))))))))))))))))))))))))))))))))

end SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedPositiveThirtyTwoWordIteration00
