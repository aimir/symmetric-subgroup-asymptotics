import SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedPositiveThirtyTwoRows

/-! Exactly the first8 saved original matrix transitions, not a period theorem. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedPositiveThirtyTwoFirstEightPilot
open MatrixNaturalRowDotReflection MatrixModelSelectedProductPrimePeriod
open CFSG.Models.MatrixGroups.Co3
open CFSGCoThreeSelectedPositiveThirtyTwoRows

private theorem packed_step_0 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 1 22 % 2=
      packedDigit 1 1518577 z.val % 2 := by decide +kernel

theorem actual_step_0 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 1=vectorCode 1518577 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 1 1518577
    first_row_binding packed_step_0

private theorem packed_step_1 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 1518577 22 % 2=
      packedDigit 1 3246706 z.val % 2 := by decide +kernel

theorem actual_step_1 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 1518577=vectorCode 3246706 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 1518577 3246706
    second_row_binding packed_step_1

private theorem packed_step_2 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 3246706 22 % 2=
      packedDigit 1 803664 z.val % 2 := by decide +kernel

theorem actual_step_2 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 3246706=vectorCode 803664 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 3246706 803664
    first_row_binding packed_step_2

private theorem packed_step_3 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 803664 22 % 2=
      packedDigit 1 2063724 z.val % 2 := by decide +kernel

theorem actual_step_3 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 803664=vectorCode 2063724 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 803664 2063724
    second_row_binding packed_step_3

private theorem packed_step_4 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 2063724 22 % 2=
      packedDigit 1 982975 z.val % 2 := by decide +kernel

theorem actual_step_4 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 2063724=vectorCode 982975 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 2063724 982975
    first_row_binding packed_step_4

private theorem packed_step_5 : ∀ z : Fin 22,
    packedDot 1 (secondRowCode z.val) 982975 22 % 2=
      packedDigit 1 4173739 z.val % 2 := by decide +kernel

theorem actual_step_5 : CFSG.Models.MatrixData.matrix 2 22 rows2 *ᵥ
    vectorCode 982975=vectorCode 4173739 :=
  packed_vector_step 2 22 1 rows2 secondRowCode 982975 4173739
    second_row_binding packed_step_5

private theorem packed_step_6 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 4173739 22 % 2=
      packedDigit 1 141872 z.val % 2 := by decide +kernel

theorem actual_step_6 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 4173739=vectorCode 141872 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 4173739 141872
    first_row_binding packed_step_6

private theorem packed_step_7 : ∀ z : Fin 22,
    packedDot 1 (firstRowCode z.val) 141872 22 % 2=
      packedDigit 1 4031899 z.val % 2 := by decide +kernel

theorem actual_step_7 : CFSG.Models.MatrixData.matrix 2 22 rows1 *ᵥ
    vectorCode 141872=vectorCode 4031899 :=
  packed_vector_step 2 22 1 rows1 firstRowCode 141872 4031899
    first_row_binding packed_step_7

end SymmetricSubgroupAsymptotics.CFSGCoThreeSelectedPositiveThirtyTwoFirstEightPilot
