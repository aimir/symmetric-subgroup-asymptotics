import SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedPositiveThirtyTwoRows
import SymmetricSubgroupAsymptotics.ListPositiveWordTrajectory

/-! One fixed32-letter word application on its saved vector. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedPositiveThirtyTwoWordIteration22
open MatrixNaturalRowDotReflection MatrixModelSelectedProductPrimePeriod
open CFSG.Models.MatrixGroups.Co3
open CFSGCoThreeSelectedPositiveThirtyTwoRows

private theorem packed_step_0 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 672264 22 % 2=
      packedDigit 1 2785930 z.val % 2 := by decide +kernel

private theorem actual_step_0 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 672264=vectorCode 2785930 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 672264 2785930
    first_row_binding packed_step_0

private theorem packed_step_1 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 2785930 22 % 2=
      packedDigit 1 1573835 z.val % 2 := by decide +kernel

private theorem actual_step_1 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 2785930=vectorCode 1573835 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 2785930 1573835
    second_row_binding packed_step_1

private theorem packed_step_2 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 1573835 22 % 2=
      packedDigit 1 1538668 z.val % 2 := by decide +kernel

private theorem actual_step_2 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 1573835=vectorCode 1538668 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 1573835 1538668
    first_row_binding packed_step_2

private theorem packed_step_3 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 1538668 22 % 2=
      packedDigit 1 2801672 z.val % 2 := by decide +kernel

private theorem actual_step_3 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 1538668=vectorCode 2801672 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 1538668 2801672
    second_row_binding packed_step_3

private theorem packed_step_4 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 2801672 22 % 2=
      packedDigit 1 3145984 z.val % 2 := by decide +kernel

private theorem actual_step_4 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 2801672=vectorCode 3145984 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 2801672 3145984
    first_row_binding packed_step_4

private theorem packed_step_5 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 3145984 22 % 2=
      packedDigit 1 1818545 z.val % 2 := by decide +kernel

private theorem actual_step_5 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 3145984=vectorCode 1818545 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 3145984 1818545
    second_row_binding packed_step_5

private theorem packed_step_6 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 1818545 22 % 2=
      packedDigit 1 1866479 z.val % 2 := by decide +kernel

private theorem actual_step_6 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 1818545=vectorCode 1866479 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 1818545 1866479
    first_row_binding packed_step_6

private theorem packed_step_7 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 1866479 22 % 2=
      packedDigit 1 1406750 z.val % 2 := by decide +kernel

private theorem actual_step_7 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 1866479=vectorCode 1406750 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 1866479 1406750
    first_row_binding packed_step_7

private theorem packed_step_8 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 1406750 22 % 2=
      packedDigit 1 3606850 z.val % 2 := by decide +kernel

private theorem actual_step_8 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 1406750=vectorCode 3606850 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 1406750 3606850
    second_row_binding packed_step_8

private theorem packed_step_9 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 3606850 22 % 2=
      packedDigit 1 1090844 z.val % 2 := by decide +kernel

private theorem actual_step_9 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 3606850=vectorCode 1090844 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 3606850 1090844
    second_row_binding packed_step_9

private theorem packed_step_10 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 1090844 22 % 2=
      packedDigit 1 157548 z.val % 2 := by decide +kernel

private theorem actual_step_10 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 1090844=vectorCode 157548 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 1090844 157548
    second_row_binding packed_step_10

private theorem packed_step_11 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 157548 22 % 2=
      packedDigit 1 1406750 z.val % 2 := by decide +kernel

private theorem actual_step_11 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 157548=vectorCode 1406750 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 157548 1406750
    second_row_binding packed_step_11

private theorem packed_step_12 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 1406750 22 % 2=
      packedDigit 1 3606850 z.val % 2 := by decide +kernel

private theorem actual_step_12 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 1406750=vectorCode 3606850 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 1406750 3606850
    second_row_binding packed_step_12

private theorem packed_step_13 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 3606850 22 % 2=
      packedDigit 1 1090844 z.val % 2 := by decide +kernel

private theorem actual_step_13 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 3606850=vectorCode 1090844 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 3606850 1090844
    second_row_binding packed_step_13

private theorem packed_step_14 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 1090844 22 % 2=
      packedDigit 1 157548 z.val % 2 := by decide +kernel

private theorem actual_step_14 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 1090844=vectorCode 157548 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 1090844 157548
    second_row_binding packed_step_14

private theorem packed_step_15 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 157548 22 % 2=
      packedDigit 1 557137 z.val % 2 := by decide +kernel

private theorem actual_step_15 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 157548=vectorCode 557137 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 157548 557137
    first_row_binding packed_step_15

private theorem packed_step_16 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 557137 22 % 2=
      packedDigit 1 1941471 z.val % 2 := by decide +kernel

private theorem actual_step_16 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 557137=vectorCode 1941471 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 557137 1941471
    first_row_binding packed_step_16

private theorem packed_step_17 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 1941471 22 % 2=
      packedDigit 1 1966624 z.val % 2 := by decide +kernel

private theorem actual_step_17 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 1941471=vectorCode 1966624 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 1941471 1966624
    second_row_binding packed_step_17

private theorem packed_step_18 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 1966624 22 % 2=
      packedDigit 1 2160795 z.val % 2 := by decide +kernel

private theorem actual_step_18 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 1966624=vectorCode 2160795 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 1966624 2160795
    first_row_binding packed_step_18

private theorem packed_step_19 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 2160795 22 % 2=
      packedDigit 1 1638791 z.val % 2 := by decide +kernel

private theorem actual_step_19 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 2160795=vectorCode 1638791 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 2160795 1638791
    second_row_binding packed_step_19

private theorem packed_step_20 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 1638791 22 % 2=
      packedDigit 1 3819804 z.val % 2 := by decide +kernel

private theorem actual_step_20 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 1638791=vectorCode 3819804 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 1638791 3819804
    second_row_binding packed_step_20

private theorem packed_step_21 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 3819804 22 % 2=
      packedDigit 1 1732636 z.val % 2 := by decide +kernel

private theorem actual_step_21 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 3819804=vectorCode 1732636 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 3819804 1732636
    second_row_binding packed_step_21

private theorem packed_step_22 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 1732636 22 % 2=
      packedDigit 1 3357407 z.val % 2 := by decide +kernel

private theorem actual_step_22 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 1732636=vectorCode 3357407 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 1732636 3357407
    first_row_binding packed_step_22

private theorem packed_step_23 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 3357407 22 % 2=
      packedDigit 1 582696 z.val % 2 := by decide +kernel

private theorem actual_step_23 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 3357407=vectorCode 582696 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 3357407 582696
    second_row_binding packed_step_23

private theorem packed_step_24 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 582696 22 % 2=
      packedDigit 1 2155580 z.val % 2 := by decide +kernel

private theorem actual_step_24 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 582696=vectorCode 2155580 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 582696 2155580
    first_row_binding packed_step_24

private theorem packed_step_25 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 2155580 22 % 2=
      packedDigit 1 2621460 z.val % 2 := by decide +kernel

private theorem actual_step_25 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 2155580=vectorCode 2621460 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 2155580 2621460
    first_row_binding packed_step_25

private theorem packed_step_26 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 2621460 22 % 2=
      packedDigit 1 582696 z.val % 2 := by decide +kernel

private theorem actual_step_26 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 2621460=vectorCode 582696 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 2621460 582696
    first_row_binding packed_step_26

private theorem packed_step_27 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 582696 22 % 2=
      packedDigit 1 2155580 z.val % 2 := by decide +kernel

private theorem actual_step_27 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 582696=vectorCode 2155580 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 582696 2155580
    first_row_binding packed_step_27

private theorem packed_step_28 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 2155580 22 % 2=
      packedDigit 1 2132234 z.val % 2 := by decide +kernel

private theorem actual_step_28 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 2155580=vectorCode 2132234 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 2155580 2132234
    second_row_binding packed_step_28

private theorem packed_step_29 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 2132234 22 % 2=
      packedDigit 1 345109 z.val % 2 := by decide +kernel

private theorem actual_step_29 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 2132234=vectorCode 345109 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 2132234 345109
    first_row_binding packed_step_29

private theorem packed_step_30 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 345109 22 % 2=
      packedDigit 1 3637087 z.val % 2 := by decide +kernel

private theorem actual_step_30 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 345109=vectorCode 3637087 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 345109 3637087
    first_row_binding packed_step_30

private theorem packed_step_31 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 3637087 22 % 2=
      packedDigit 1 1 z.val % 2 := by decide +kernel

private theorem actual_step_31 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 3637087=vectorCode 1 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 3637087 1
    second_row_binding packed_step_31

theorem consecutive : wordEnd (vectors 22)=vectors 23 := by
  change (actualWord.map (MatrixModelSelectedPositiveWordPrimePeriod.letterEnd
    2 22 rows1 rows2)).prod (vectors 22)=vectors 23
  apply ListPositiveWordTrajectory.prod_apply_eq_of_steps
    (MatrixModelSelectedPositiveWordPrimePeriod.letterEnd 2 22 rows1 rows2)
    actualWord (vectors 22) (vectors 23)
  have hword : actualWord.reverse=[true,false,true,false,true,false,true,true,false,false,false,false,false,false,false,true,true,false,true,false,false,false,true,false,true,true,true,true,false,true,true,false] := by decide +kernel
  rw [hword]
  exact (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 2785930) actual_step_0
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 1573835) actual_step_1
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 1538668) actual_step_2
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 2801672) actual_step_3
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 3145984) actual_step_4
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 1818545) actual_step_5
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 1866479) actual_step_6
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 1406750) actual_step_7
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 3606850) actual_step_8
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 1090844) actual_step_9
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 157548) actual_step_10
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 1406750) actual_step_11
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 3606850) actual_step_12
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 1090844) actual_step_13
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 157548) actual_step_14
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 557137) actual_step_15
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 1941471) actual_step_16
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 1966624) actual_step_17
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 2160795) actual_step_18
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 1638791) actual_step_19
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 3819804) actual_step_20
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 1732636) actual_step_21
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 3357407) actual_step_22
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 582696) actual_step_23
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 2155580) actual_step_24
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 2621460) actual_step_25
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 582696) actual_step_26
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 2155580) actual_step_27
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 2132234) actual_step_28
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 345109) actual_step_29
    (ListPositiveWordTrajectory.Steps.cons (s := true)
    (v' := vectorCode 3637087) actual_step_30
    (ListPositiveWordTrajectory.Steps.cons (s := false)
    (v' := vectorCode 1) actual_step_31
    (ListPositiveWordTrajectory.Steps.nil (vectorCode 1))))))))))))))))))))))))))))))))))

end SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedPositiveThirtyTwoWordIteration22
