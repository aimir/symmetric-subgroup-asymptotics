import SymmetricSubgroupAsymptotics.CFSGGTwoExceptionalCoefficientPilot

/-! Constant prime-ring certificates for one signed original simple root
on the actual fourteen-vector basis. Each certificate is a separate small
kernel reduction over F3. The cubic exchange retains all divided powers,
including the zero middle coefficients. No simplicity assumption occurs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGGTwoExceptionalNegativeShortCoefficients
open CFSGGTwoOriginalMatrixCoordinates CFSGGTwoExceptionalCoefficients

private theorem coefficient_0_1 :
    column (ZMod 3) (sourceOperator (ZMod 3) true 0 1
      (matrixVectors (ZMod 3) (Sum.inl (false,0))))=
    targetOperator (ZMod 3) true 0 1
      (column (ZMod 3) (matrixVectors (ZMod 3) (Sum.inl (false,0)))) := by
  decide +kernel

private theorem coefficient_0_2 :
    column (ZMod 3) (sourceOperator (ZMod 3) true 0 2
      (matrixVectors (ZMod 3) (Sum.inl (false,0))))=
    targetOperator (ZMod 3) true 0 2
      (column (ZMod 3) (matrixVectors (ZMod 3) (Sum.inl (false,0)))) := by
  decide +kernel

private theorem coefficient_0_3 :
    column (ZMod 3) (sourceOperator (ZMod 3) true 0 3
      (matrixVectors (ZMod 3) (Sum.inl (false,0))))=
    targetOperator (ZMod 3) true 0 3
      (column (ZMod 3) (matrixVectors (ZMod 3) (Sum.inl (false,0)))) := by
  decide +kernel

private theorem coefficient_1_1 :
    column (ZMod 3) (sourceOperator (ZMod 3) true 0 1
      (matrixVectors (ZMod 3) (Sum.inl (false,1))))=
    targetOperator (ZMod 3) true 0 1
      (column (ZMod 3) (matrixVectors (ZMod 3) (Sum.inl (false,1)))) := by
  decide +kernel

private theorem coefficient_1_2 :
    column (ZMod 3) (sourceOperator (ZMod 3) true 0 2
      (matrixVectors (ZMod 3) (Sum.inl (false,1))))=
    targetOperator (ZMod 3) true 0 2
      (column (ZMod 3) (matrixVectors (ZMod 3) (Sum.inl (false,1)))) := by
  decide +kernel

private theorem coefficient_1_3 :
    column (ZMod 3) (sourceOperator (ZMod 3) true 0 3
      (matrixVectors (ZMod 3) (Sum.inl (false,1))))=
    targetOperator (ZMod 3) true 0 3
      (column (ZMod 3) (matrixVectors (ZMod 3) (Sum.inl (false,1)))) := by
  decide +kernel

private theorem coefficient_2_1 :
    column (ZMod 3) (sourceOperator (ZMod 3) true 0 1
      (matrixVectors (ZMod 3) (Sum.inl (false,2))))=
    targetOperator (ZMod 3) true 0 1
      (column (ZMod 3) (matrixVectors (ZMod 3) (Sum.inl (false,2)))) := by
  decide +kernel

private theorem coefficient_2_2 :
    column (ZMod 3) (sourceOperator (ZMod 3) true 0 2
      (matrixVectors (ZMod 3) (Sum.inl (false,2))))=
    targetOperator (ZMod 3) true 0 2
      (column (ZMod 3) (matrixVectors (ZMod 3) (Sum.inl (false,2)))) := by
  decide +kernel

private theorem coefficient_2_3 :
    column (ZMod 3) (sourceOperator (ZMod 3) true 0 3
      (matrixVectors (ZMod 3) (Sum.inl (false,2))))=
    targetOperator (ZMod 3) true 0 3
      (column (ZMod 3) (matrixVectors (ZMod 3) (Sum.inl (false,2)))) := by
  decide +kernel

private theorem coefficient_3_1 :
    column (ZMod 3) (sourceOperator (ZMod 3) true 0 1
      (matrixVectors (ZMod 3) (Sum.inl (false,3))))=
    targetOperator (ZMod 3) true 0 1
      (column (ZMod 3) (matrixVectors (ZMod 3) (Sum.inl (false,3)))) := by
  decide +kernel

private theorem coefficient_3_2 :
    column (ZMod 3) (sourceOperator (ZMod 3) true 0 2
      (matrixVectors (ZMod 3) (Sum.inl (false,3))))=
    targetOperator (ZMod 3) true 0 2
      (column (ZMod 3) (matrixVectors (ZMod 3) (Sum.inl (false,3)))) := by
  decide +kernel

private theorem coefficient_3_3 :
    column (ZMod 3) (sourceOperator (ZMod 3) true 0 3
      (matrixVectors (ZMod 3) (Sum.inl (false,3))))=
    targetOperator (ZMod 3) true 0 3
      (column (ZMod 3) (matrixVectors (ZMod 3) (Sum.inl (false,3)))) := by
  decide +kernel

private theorem coefficient_4_1 :
    column (ZMod 3) (sourceOperator (ZMod 3) true 0 1
      (matrixVectors (ZMod 3) (Sum.inl (false,4))))=
    targetOperator (ZMod 3) true 0 1
      (column (ZMod 3) (matrixVectors (ZMod 3) (Sum.inl (false,4)))) := by
  decide +kernel

private theorem coefficient_4_2 :
    column (ZMod 3) (sourceOperator (ZMod 3) true 0 2
      (matrixVectors (ZMod 3) (Sum.inl (false,4))))=
    targetOperator (ZMod 3) true 0 2
      (column (ZMod 3) (matrixVectors (ZMod 3) (Sum.inl (false,4)))) := by
  decide +kernel

private theorem coefficient_4_3 :
    column (ZMod 3) (sourceOperator (ZMod 3) true 0 3
      (matrixVectors (ZMod 3) (Sum.inl (false,4))))=
    targetOperator (ZMod 3) true 0 3
      (column (ZMod 3) (matrixVectors (ZMod 3) (Sum.inl (false,4)))) := by
  decide +kernel

private theorem coefficient_5_1 :
    column (ZMod 3) (sourceOperator (ZMod 3) true 0 1
      (matrixVectors (ZMod 3) (Sum.inl (false,5))))=
    targetOperator (ZMod 3) true 0 1
      (column (ZMod 3) (matrixVectors (ZMod 3) (Sum.inl (false,5)))) := by
  decide +kernel

private theorem coefficient_5_2 :
    column (ZMod 3) (sourceOperator (ZMod 3) true 0 2
      (matrixVectors (ZMod 3) (Sum.inl (false,5))))=
    targetOperator (ZMod 3) true 0 2
      (column (ZMod 3) (matrixVectors (ZMod 3) (Sum.inl (false,5)))) := by
  decide +kernel

private theorem coefficient_5_3 :
    column (ZMod 3) (sourceOperator (ZMod 3) true 0 3
      (matrixVectors (ZMod 3) (Sum.inl (false,5))))=
    targetOperator (ZMod 3) true 0 3
      (column (ZMod 3) (matrixVectors (ZMod 3) (Sum.inl (false,5)))) := by
  decide +kernel

private theorem coefficient_6_1 :
    column (ZMod 3) (sourceOperator (ZMod 3) true 0 1
      (matrixVectors (ZMod 3) (Sum.inl (true,0))))=
    targetOperator (ZMod 3) true 0 1
      (column (ZMod 3) (matrixVectors (ZMod 3) (Sum.inl (true,0)))) := by
  decide +kernel

private theorem coefficient_6_2 :
    column (ZMod 3) (sourceOperator (ZMod 3) true 0 2
      (matrixVectors (ZMod 3) (Sum.inl (true,0))))=
    targetOperator (ZMod 3) true 0 2
      (column (ZMod 3) (matrixVectors (ZMod 3) (Sum.inl (true,0)))) := by
  decide +kernel

private theorem coefficient_6_3 :
    column (ZMod 3) (sourceOperator (ZMod 3) true 0 3
      (matrixVectors (ZMod 3) (Sum.inl (true,0))))=
    targetOperator (ZMod 3) true 0 3
      (column (ZMod 3) (matrixVectors (ZMod 3) (Sum.inl (true,0)))) := by
  decide +kernel

private theorem coefficient_7_1 :
    column (ZMod 3) (sourceOperator (ZMod 3) true 0 1
      (matrixVectors (ZMod 3) (Sum.inl (true,1))))=
    targetOperator (ZMod 3) true 0 1
      (column (ZMod 3) (matrixVectors (ZMod 3) (Sum.inl (true,1)))) := by
  decide +kernel

private theorem coefficient_7_2 :
    column (ZMod 3) (sourceOperator (ZMod 3) true 0 2
      (matrixVectors (ZMod 3) (Sum.inl (true,1))))=
    targetOperator (ZMod 3) true 0 2
      (column (ZMod 3) (matrixVectors (ZMod 3) (Sum.inl (true,1)))) := by
  decide +kernel

private theorem coefficient_7_3 :
    column (ZMod 3) (sourceOperator (ZMod 3) true 0 3
      (matrixVectors (ZMod 3) (Sum.inl (true,1))))=
    targetOperator (ZMod 3) true 0 3
      (column (ZMod 3) (matrixVectors (ZMod 3) (Sum.inl (true,1)))) := by
  decide +kernel

private theorem coefficient_8_1 :
    column (ZMod 3) (sourceOperator (ZMod 3) true 0 1
      (matrixVectors (ZMod 3) (Sum.inl (true,2))))=
    targetOperator (ZMod 3) true 0 1
      (column (ZMod 3) (matrixVectors (ZMod 3) (Sum.inl (true,2)))) := by
  decide +kernel

private theorem coefficient_8_2 :
    column (ZMod 3) (sourceOperator (ZMod 3) true 0 2
      (matrixVectors (ZMod 3) (Sum.inl (true,2))))=
    targetOperator (ZMod 3) true 0 2
      (column (ZMod 3) (matrixVectors (ZMod 3) (Sum.inl (true,2)))) := by
  decide +kernel

private theorem coefficient_8_3 :
    column (ZMod 3) (sourceOperator (ZMod 3) true 0 3
      (matrixVectors (ZMod 3) (Sum.inl (true,2))))=
    targetOperator (ZMod 3) true 0 3
      (column (ZMod 3) (matrixVectors (ZMod 3) (Sum.inl (true,2)))) := by
  decide +kernel

private theorem coefficient_9_1 :
    column (ZMod 3) (sourceOperator (ZMod 3) true 0 1
      (matrixVectors (ZMod 3) (Sum.inl (true,3))))=
    targetOperator (ZMod 3) true 0 1
      (column (ZMod 3) (matrixVectors (ZMod 3) (Sum.inl (true,3)))) := by
  decide +kernel

private theorem coefficient_9_2 :
    column (ZMod 3) (sourceOperator (ZMod 3) true 0 2
      (matrixVectors (ZMod 3) (Sum.inl (true,3))))=
    targetOperator (ZMod 3) true 0 2
      (column (ZMod 3) (matrixVectors (ZMod 3) (Sum.inl (true,3)))) := by
  decide +kernel

private theorem coefficient_9_3 :
    column (ZMod 3) (sourceOperator (ZMod 3) true 0 3
      (matrixVectors (ZMod 3) (Sum.inl (true,3))))=
    targetOperator (ZMod 3) true 0 3
      (column (ZMod 3) (matrixVectors (ZMod 3) (Sum.inl (true,3)))) := by
  decide +kernel

private theorem coefficient_10_1 :
    column (ZMod 3) (sourceOperator (ZMod 3) true 0 1
      (matrixVectors (ZMod 3) (Sum.inl (true,4))))=
    targetOperator (ZMod 3) true 0 1
      (column (ZMod 3) (matrixVectors (ZMod 3) (Sum.inl (true,4)))) := by
  decide +kernel

private theorem coefficient_10_2 :
    column (ZMod 3) (sourceOperator (ZMod 3) true 0 2
      (matrixVectors (ZMod 3) (Sum.inl (true,4))))=
    targetOperator (ZMod 3) true 0 2
      (column (ZMod 3) (matrixVectors (ZMod 3) (Sum.inl (true,4)))) := by
  decide +kernel

private theorem coefficient_10_3 :
    column (ZMod 3) (sourceOperator (ZMod 3) true 0 3
      (matrixVectors (ZMod 3) (Sum.inl (true,4))))=
    targetOperator (ZMod 3) true 0 3
      (column (ZMod 3) (matrixVectors (ZMod 3) (Sum.inl (true,4)))) := by
  decide +kernel

private theorem coefficient_11_1 :
    column (ZMod 3) (sourceOperator (ZMod 3) true 0 1
      (matrixVectors (ZMod 3) (Sum.inl (true,5))))=
    targetOperator (ZMod 3) true 0 1
      (column (ZMod 3) (matrixVectors (ZMod 3) (Sum.inl (true,5)))) := by
  decide +kernel

private theorem coefficient_11_2 :
    column (ZMod 3) (sourceOperator (ZMod 3) true 0 2
      (matrixVectors (ZMod 3) (Sum.inl (true,5))))=
    targetOperator (ZMod 3) true 0 2
      (column (ZMod 3) (matrixVectors (ZMod 3) (Sum.inl (true,5)))) := by
  decide +kernel

private theorem coefficient_11_3 :
    column (ZMod 3) (sourceOperator (ZMod 3) true 0 3
      (matrixVectors (ZMod 3) (Sum.inl (true,5))))=
    targetOperator (ZMod 3) true 0 3
      (column (ZMod 3) (matrixVectors (ZMod 3) (Sum.inl (true,5)))) := by
  decide +kernel

private theorem coefficient_12_1 :
    column (ZMod 3) (sourceOperator (ZMod 3) true 0 1
      (matrixVectors (ZMod 3) (Sum.inr 0)))=
    targetOperator (ZMod 3) true 0 1
      (column (ZMod 3) (matrixVectors (ZMod 3) (Sum.inr 0))) := by
  decide +kernel

private theorem coefficient_12_2 :
    column (ZMod 3) (sourceOperator (ZMod 3) true 0 2
      (matrixVectors (ZMod 3) (Sum.inr 0)))=
    targetOperator (ZMod 3) true 0 2
      (column (ZMod 3) (matrixVectors (ZMod 3) (Sum.inr 0))) := by
  decide +kernel

private theorem coefficient_12_3 :
    column (ZMod 3) (sourceOperator (ZMod 3) true 0 3
      (matrixVectors (ZMod 3) (Sum.inr 0)))=
    targetOperator (ZMod 3) true 0 3
      (column (ZMod 3) (matrixVectors (ZMod 3) (Sum.inr 0))) := by
  decide +kernel

private theorem coefficient_13_1 :
    column (ZMod 3) (sourceOperator (ZMod 3) true 0 1
      (matrixVectors (ZMod 3) (Sum.inr 1)))=
    targetOperator (ZMod 3) true 0 1
      (column (ZMod 3) (matrixVectors (ZMod 3) (Sum.inr 1))) := by
  decide +kernel

private theorem coefficient_13_2 :
    column (ZMod 3) (sourceOperator (ZMod 3) true 0 2
      (matrixVectors (ZMod 3) (Sum.inr 1)))=
    targetOperator (ZMod 3) true 0 2
      (column (ZMod 3) (matrixVectors (ZMod 3) (Sum.inr 1))) := by
  decide +kernel

private theorem coefficient_13_3 :
    column (ZMod 3) (sourceOperator (ZMod 3) true 0 3
      (matrixVectors (ZMod 3) (Sum.inr 1)))=
    targetOperator (ZMod 3) true 0 3
      (column (ZMod 3) (matrixVectors (ZMod 3) (Sum.inr 1))) := by
  decide +kernel

theorem prime_coefficients (k : Fin 4) (j : CFSGGTwoOriginalFourteenFamily.Index) :
    column (ZMod 3) (sourceOperator (ZMod 3) true 0 k (matrixVectors (ZMod 3) j))=
    targetOperator (ZMod 3) true 0 k (column (ZMod 3) (matrixVectors (ZMod 3) j)) := by
  rcases j with ⟨b,j⟩|j
  · cases b
    · fin_cases j
      · fin_cases k
        · rfl
        · exact coefficient_0_1
        · exact coefficient_0_2
        · exact coefficient_0_3
      · fin_cases k
        · rfl
        · exact coefficient_1_1
        · exact coefficient_1_2
        · exact coefficient_1_3
      · fin_cases k
        · rfl
        · exact coefficient_2_1
        · exact coefficient_2_2
        · exact coefficient_2_3
      · fin_cases k
        · rfl
        · exact coefficient_3_1
        · exact coefficient_3_2
        · exact coefficient_3_3
      · fin_cases k
        · rfl
        · exact coefficient_4_1
        · exact coefficient_4_2
        · exact coefficient_4_3
      · fin_cases k
        · rfl
        · exact coefficient_5_1
        · exact coefficient_5_2
        · exact coefficient_5_3
    · fin_cases j
      · fin_cases k
        · rfl
        · exact coefficient_6_1
        · exact coefficient_6_2
        · exact coefficient_6_3
      · fin_cases k
        · rfl
        · exact coefficient_7_1
        · exact coefficient_7_2
        · exact coefficient_7_3
      · fin_cases k
        · rfl
        · exact coefficient_8_1
        · exact coefficient_8_2
        · exact coefficient_8_3
      · fin_cases k
        · rfl
        · exact coefficient_9_1
        · exact coefficient_9_2
        · exact coefficient_9_3
      · fin_cases k
        · rfl
        · exact coefficient_10_1
        · exact coefficient_10_2
        · exact coefficient_10_3
      · fin_cases k
        · rfl
        · exact coefficient_11_1
        · exact coefficient_11_2
        · exact coefficient_11_3
  · fin_cases j
    · fin_cases k
      · rfl
      · exact coefficient_12_1
      · exact coefficient_12_2
      · exact coefficient_12_3
    · fin_cases k
      · rfl
      · exact coefficient_13_1
      · exact coefficient_13_2
      · exact coefficient_13_3

end SymmetricSubgroupAsymptotics.CFSGGTwoExceptionalNegativeShortCoefficients
