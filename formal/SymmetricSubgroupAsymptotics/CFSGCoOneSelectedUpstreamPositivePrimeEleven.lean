import SymmetricSubgroupAsymptotics.CFSGCoOneUpstreamPrimeElevenFirstRows
import SymmetricSubgroupAsymptotics.CFSGCoOneUpstreamPrimeElevenSecondRows
import SymmetricSubgroupAsymptotics.CFSGCoOneSelectedUpstreamPositiveWord
import SymmetricSubgroupAsymptotics.MatrixModelSelectedRowVectorReflection
import SymmetricSubgroupAsymptotics.LinearMapSelectedKrylovPeriod

/-! SAME selected original matvecs. Separate arithmetic commands; no whole-word order. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGCoOneSelectedUpstreamPositivePrimeEleven
open MatrixNaturalRowDotReflection CFSGCoOneUpstreamPrimeElevenPackedData CFSGCoOneSelectedUpstreamPositiveWord
open CFSG.Models.MatrixGroups.Co1

private theorem check_0 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 0) 24 % 2=
      packedDigit 1 (stageCode 1) i.val % 2 := by decide +kernel

private theorem step_0 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 0=stageVector 1 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 0) (stageCode 1)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_0 i)

private theorem check_1 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 1) 24 % 2=
      packedDigit 1 (stageCode 2) i.val % 2 := by decide +kernel

private theorem step_1 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 1=stageVector 2 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 1) (stageCode 2)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_1 i)

private theorem check_2 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 2) 24 % 2=
      packedDigit 1 (stageCode 3) i.val % 2 := by decide +kernel

private theorem step_2 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 2=stageVector 3 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 2) (stageCode 3)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_2 i)

private theorem check_3 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 3) 24 % 2=
      packedDigit 1 (stageCode 4) i.val % 2 := by decide +kernel

private theorem step_3 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 3=stageVector 4 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 3) (stageCode 4)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_3 i)

private theorem check_4 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 4) 24 % 2=
      packedDigit 1 (stageCode 5) i.val % 2 := by decide +kernel

private theorem step_4 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 4=stageVector 5 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 4) (stageCode 5)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_4 i)

private theorem check_5 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 5) 24 % 2=
      packedDigit 1 (stageCode 6) i.val % 2 := by decide +kernel

private theorem step_5 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 5=stageVector 6 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 5) (stageCode 6)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_5 i)

private theorem check_6 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 6) 24 % 2=
      packedDigit 1 (stageCode 7) i.val % 2 := by decide +kernel

private theorem step_6 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 6=stageVector 7 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 6) (stageCode 7)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_6 i)

private theorem check_7 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 7) 24 % 2=
      packedDigit 1 (stageCode 8) i.val % 2 := by decide +kernel

private theorem step_7 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 7=stageVector 8 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 7) (stageCode 8)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_7 i)

private theorem check_8 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 8) 24 % 2=
      packedDigit 1 (stageCode 9) i.val % 2 := by decide +kernel

private theorem step_8 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 8=stageVector 9 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 8) (stageCode 9)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_8 i)

private theorem check_9 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 9) 24 % 2=
      packedDigit 1 (stageCode 10) i.val % 2 := by decide +kernel

private theorem step_9 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 9=stageVector 10 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 9) (stageCode 10)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_9 i)

private theorem check_10 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 10) 24 % 2=
      packedDigit 1 (stageCode 11) i.val % 2 := by decide +kernel

private theorem step_10 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 10=stageVector 11 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 10) (stageCode 11)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_10 i)

private theorem check_11 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 11) 24 % 2=
      packedDigit 1 (stageCode 12) i.val % 2 := by decide +kernel

private theorem step_11 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 11=stageVector 12 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 11) (stageCode 12)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_11 i)

private theorem check_12 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 12) 24 % 2=
      packedDigit 1 (stageCode 13) i.val % 2 := by decide +kernel

private theorem step_12 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 12=stageVector 13 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 12) (stageCode 13)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_12 i)

private theorem check_13 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 13) 24 % 2=
      packedDigit 1 (stageCode 14) i.val % 2 := by decide +kernel

private theorem step_13 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 13=stageVector 14 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 13) (stageCode 14)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_13 i)

private theorem check_14 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 14) 24 % 2=
      packedDigit 1 (stageCode 15) i.val % 2 := by decide +kernel

private theorem step_14 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 14=stageVector 15 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 14) (stageCode 15)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_14 i)

private theorem check_15 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 15) 24 % 2=
      packedDigit 1 (stageCode 16) i.val % 2 := by decide +kernel

private theorem step_15 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 15=stageVector 16 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 15) (stageCode 16)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_15 i)

private theorem check_16 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 16) 24 % 2=
      packedDigit 1 (stageCode 17) i.val % 2 := by decide +kernel

private theorem step_16 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 16=stageVector 17 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 16) (stageCode 17)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_16 i)

private theorem check_17 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 17) 24 % 2=
      packedDigit 1 (stageCode 18) i.val % 2 := by decide +kernel

private theorem step_17 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 17=stageVector 18 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 17) (stageCode 18)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_17 i)

private theorem check_18 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 18) 24 % 2=
      packedDigit 1 (stageCode 19) i.val % 2 := by decide +kernel

private theorem step_18 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 18=stageVector 19 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 18) (stageCode 19)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_18 i)

private theorem check_19 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 19) 24 % 2=
      packedDigit 1 (stageCode 20) i.val % 2 := by decide +kernel

private theorem step_19 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 19=stageVector 20 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 19) (stageCode 20)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_19 i)

private theorem check_20 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 20) 24 % 2=
      packedDigit 1 (stageCode 21) i.val % 2 := by decide +kernel

private theorem step_20 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 20=stageVector 21 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 20) (stageCode 21)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_20 i)

private theorem check_21 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 21) 24 % 2=
      packedDigit 1 (stageCode 22) i.val % 2 := by decide +kernel

private theorem step_21 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 21=stageVector 22 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 21) (stageCode 22)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_21 i)

private theorem check_22 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 22) 24 % 2=
      packedDigit 1 (stageCode 23) i.val % 2 := by decide +kernel

private theorem step_22 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 22=stageVector 23 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 22) (stageCode 23)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_22 i)

private theorem check_23 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 23) 24 % 2=
      packedDigit 1 (stageCode 24) i.val % 2 := by decide +kernel

private theorem step_23 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 23=stageVector 24 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 23) (stageCode 24)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_23 i)

private theorem check_24 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 24) 24 % 2=
      packedDigit 1 (stageCode 25) i.val % 2 := by decide +kernel

private theorem step_24 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 24=stageVector 25 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 24) (stageCode 25)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_24 i)

private theorem check_25 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 25) 24 % 2=
      packedDigit 1 (stageCode 26) i.val % 2 := by decide +kernel

private theorem step_25 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 25=stageVector 26 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 25) (stageCode 26)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_25 i)

private theorem check_26 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 26) 24 % 2=
      packedDigit 1 (stageCode 27) i.val % 2 := by decide +kernel

private theorem step_26 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 26=stageVector 27 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 26) (stageCode 27)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_26 i)

private theorem check_27 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 27) 24 % 2=
      packedDigit 1 (stageCode 28) i.val % 2 := by decide +kernel

private theorem step_27 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 27=stageVector 28 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 27) (stageCode 28)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_27 i)

private theorem check_28 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 28) 24 % 2=
      packedDigit 1 (stageCode 29) i.val % 2 := by decide +kernel

private theorem step_28 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 28=stageVector 29 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 28) (stageCode 29)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_28 i)

private theorem check_29 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 29) 24 % 2=
      packedDigit 1 (stageCode 30) i.val % 2 := by decide +kernel

private theorem step_29 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 29=stageVector 30 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 29) (stageCode 30)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_29 i)

private theorem check_30 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 30) 24 % 2=
      packedDigit 1 (stageCode 31) i.val % 2 := by decide +kernel

private theorem step_30 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 30=stageVector 31 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 30) (stageCode 31)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_30 i)

private theorem check_31 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 31) 24 % 2=
      packedDigit 1 (stageCode 32) i.val % 2 := by decide +kernel

private theorem step_31 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 31=stageVector 32 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 31) (stageCode 32)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_31 i)

private theorem check_32 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 32) 24 % 2=
      packedDigit 1 (stageCode 33) i.val % 2 := by decide +kernel

private theorem step_32 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 32=stageVector 33 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 32) (stageCode 33)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_32 i)

private theorem check_33 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 33) 24 % 2=
      packedDigit 1 (stageCode 34) i.val % 2 := by decide +kernel

private theorem step_33 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 33=stageVector 34 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 33) (stageCode 34)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_33 i)

private theorem check_34 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 34) 24 % 2=
      packedDigit 1 (stageCode 35) i.val % 2 := by decide +kernel

private theorem step_34 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 34=stageVector 35 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 34) (stageCode 35)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_34 i)

private theorem check_35 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 35) 24 % 2=
      packedDigit 1 (stageCode 36) i.val % 2 := by decide +kernel

private theorem step_35 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 35=stageVector 36 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 35) (stageCode 36)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_35 i)

private theorem check_36 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 36) 24 % 2=
      packedDigit 1 (stageCode 37) i.val % 2 := by decide +kernel

private theorem step_36 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 36=stageVector 37 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 36) (stageCode 37)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_36 i)

private theorem check_37 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 37) 24 % 2=
      packedDigit 1 (stageCode 38) i.val % 2 := by decide +kernel

private theorem step_37 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 37=stageVector 38 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 37) (stageCode 38)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_37 i)

private theorem check_38 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 38) 24 % 2=
      packedDigit 1 (stageCode 39) i.val % 2 := by decide +kernel

private theorem step_38 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 38=stageVector 39 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 38) (stageCode 39)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_38 i)

private theorem check_39 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 39) 24 % 2=
      packedDigit 1 (stageCode 40) i.val % 2 := by decide +kernel

private theorem step_39 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 39=stageVector 40 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 39) (stageCode 40)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_39 i)

private theorem check_40 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 40) 24 % 2=
      packedDigit 1 (stageCode 41) i.val % 2 := by decide +kernel

private theorem step_40 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 40=stageVector 41 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 40) (stageCode 41)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_40 i)

private theorem check_41 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 41) 24 % 2=
      packedDigit 1 (stageCode 42) i.val % 2 := by decide +kernel

private theorem step_41 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 41=stageVector 42 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 41) (stageCode 42)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_41 i)

private theorem check_42 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 42) 24 % 2=
      packedDigit 1 (stageCode 43) i.val % 2 := by decide +kernel

private theorem step_42 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 42=stageVector 43 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 42) (stageCode 43)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_42 i)

private theorem check_43 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 43) 24 % 2=
      packedDigit 1 (stageCode 44) i.val % 2 := by decide +kernel

private theorem step_43 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 43=stageVector 44 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 43) (stageCode 44)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_43 i)

private theorem check_44 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 44) 24 % 2=
      packedDigit 1 (stageCode 45) i.val % 2 := by decide +kernel

private theorem step_44 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 44=stageVector 45 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 44) (stageCode 45)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_44 i)

private theorem check_45 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 45) 24 % 2=
      packedDigit 1 (stageCode 46) i.val % 2 := by decide +kernel

private theorem step_45 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 45=stageVector 46 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 45) (stageCode 46)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_45 i)

private theorem check_46 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 46) 24 % 2=
      packedDigit 1 (stageCode 47) i.val % 2 := by decide +kernel

private theorem step_46 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 46=stageVector 47 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 46) (stageCode 47)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_46 i)

private theorem check_47 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 47) 24 % 2=
      packedDigit 1 (stageCode 48) i.val % 2 := by decide +kernel

private theorem step_47 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 47=stageVector 48 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 47) (stageCode 48)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_47 i)

private theorem check_48 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 48) 24 % 2=
      packedDigit 1 (stageCode 49) i.val % 2 := by decide +kernel

private theorem step_48 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 48=stageVector 49 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 48) (stageCode 49)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_48 i)

private theorem check_49 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 49) 24 % 2=
      packedDigit 1 (stageCode 50) i.val % 2 := by decide +kernel

private theorem step_49 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 49=stageVector 50 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 49) (stageCode 50)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_49 i)

private theorem check_50 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 50) 24 % 2=
      packedDigit 1 (stageCode 51) i.val % 2 := by decide +kernel

private theorem step_50 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 50=stageVector 51 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 50) (stageCode 51)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_50 i)

private theorem check_51 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 51) 24 % 2=
      packedDigit 1 (stageCode 52) i.val % 2 := by decide +kernel

private theorem step_51 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 51=stageVector 52 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 51) (stageCode 52)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_51 i)

private theorem check_52 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 52) 24 % 2=
      packedDigit 1 (stageCode 53) i.val % 2 := by decide +kernel

private theorem step_52 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 52=stageVector 53 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 52) (stageCode 53)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_52 i)

private theorem check_53 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 53) 24 % 2=
      packedDigit 1 (stageCode 54) i.val % 2 := by decide +kernel

private theorem step_53 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 53=stageVector 54 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 53) (stageCode 54)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_53 i)

private theorem check_54 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 54) 24 % 2=
      packedDigit 1 (stageCode 55) i.val % 2 := by decide +kernel

private theorem step_54 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 54=stageVector 55 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 54) (stageCode 55)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_54 i)

private theorem check_55 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 55) 24 % 2=
      packedDigit 1 (stageCode 56) i.val % 2 := by decide +kernel

private theorem step_55 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 55=stageVector 56 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 55) (stageCode 56)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_55 i)

private theorem check_56 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 56) 24 % 2=
      packedDigit 1 (stageCode 57) i.val % 2 := by decide +kernel

private theorem step_56 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 56=stageVector 57 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 56) (stageCode 57)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_56 i)

private theorem check_57 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 57) 24 % 2=
      packedDigit 1 (stageCode 58) i.val % 2 := by decide +kernel

private theorem step_57 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 57=stageVector 58 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 57) (stageCode 58)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_57 i)

private theorem check_58 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 58) 24 % 2=
      packedDigit 1 (stageCode 59) i.val % 2 := by decide +kernel

private theorem step_58 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 58=stageVector 59 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 58) (stageCode 59)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_58 i)

private theorem check_59 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 59) 24 % 2=
      packedDigit 1 (stageCode 60) i.val % 2 := by decide +kernel

private theorem step_59 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 59=stageVector 60 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 59) (stageCode 60)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_59 i)

private theorem check_60 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 60) 24 % 2=
      packedDigit 1 (stageCode 61) i.val % 2 := by decide +kernel

private theorem step_60 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 60=stageVector 61 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 60) (stageCode 61)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_60 i)

private theorem check_61 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 61) 24 % 2=
      packedDigit 1 (stageCode 62) i.val % 2 := by decide +kernel

private theorem step_61 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 61=stageVector 62 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 61) (stageCode 62)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_61 i)

private theorem check_62 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 62) 24 % 2=
      packedDigit 1 (stageCode 63) i.val % 2 := by decide +kernel

private theorem step_62 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 62=stageVector 63 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 62) (stageCode 63)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_62 i)

private theorem check_63 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 63) 24 % 2=
      packedDigit 1 (stageCode 64) i.val % 2 := by decide +kernel

private theorem step_63 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 63=stageVector 64 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 63) (stageCode 64)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_63 i)

private theorem check_64 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 64) 24 % 2=
      packedDigit 1 (stageCode 65) i.val % 2 := by decide +kernel

private theorem step_64 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 64=stageVector 65 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 64) (stageCode 65)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_64 i)

private theorem check_65 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 65) 24 % 2=
      packedDigit 1 (stageCode 66) i.val % 2 := by decide +kernel

private theorem step_65 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 65=stageVector 66 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 65) (stageCode 66)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_65 i)

private theorem check_66 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 66) 24 % 2=
      packedDigit 1 (stageCode 67) i.val % 2 := by decide +kernel

private theorem step_66 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 66=stageVector 67 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 66) (stageCode 67)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_66 i)

private theorem check_67 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 67) 24 % 2=
      packedDigit 1 (stageCode 68) i.val % 2 := by decide +kernel

private theorem step_67 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 67=stageVector 68 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 67) (stageCode 68)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_67 i)

private theorem check_68 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 68) 24 % 2=
      packedDigit 1 (stageCode 69) i.val % 2 := by decide +kernel

private theorem step_68 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 68=stageVector 69 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 68) (stageCode 69)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_68 i)

private theorem check_69 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 69) 24 % 2=
      packedDigit 1 (stageCode 70) i.val % 2 := by decide +kernel

private theorem step_69 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 69=stageVector 70 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 69) (stageCode 70)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_69 i)

private theorem check_70 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 70) 24 % 2=
      packedDigit 1 (stageCode 71) i.val % 2 := by decide +kernel

private theorem step_70 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 70=stageVector 71 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 70) (stageCode 71)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_70 i)

private theorem check_71 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 71) 24 % 2=
      packedDigit 1 (stageCode 72) i.val % 2 := by decide +kernel

private theorem step_71 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 71=stageVector 72 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 71) (stageCode 72)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_71 i)

private theorem check_72 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 72) 24 % 2=
      packedDigit 1 (stageCode 73) i.val % 2 := by decide +kernel

private theorem step_72 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 72=stageVector 73 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 72) (stageCode 73)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_72 i)

private theorem check_73 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 73) 24 % 2=
      packedDigit 1 (stageCode 74) i.val % 2 := by decide +kernel

private theorem step_73 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 73=stageVector 74 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 73) (stageCode 74)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_73 i)

private theorem check_74 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 74) 24 % 2=
      packedDigit 1 (stageCode 75) i.val % 2 := by decide +kernel

private theorem step_74 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 74=stageVector 75 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 74) (stageCode 75)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_74 i)

private theorem check_75 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 75) 24 % 2=
      packedDigit 1 (stageCode 76) i.val % 2 := by decide +kernel

private theorem step_75 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 75=stageVector 76 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 75) (stageCode 76)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_75 i)

private theorem check_76 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 76) 24 % 2=
      packedDigit 1 (stageCode 77) i.val % 2 := by decide +kernel

private theorem step_76 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 76=stageVector 77 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 76) (stageCode 77)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_76 i)

private theorem check_77 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 77) 24 % 2=
      packedDigit 1 (stageCode 78) i.val % 2 := by decide +kernel

private theorem step_77 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 77=stageVector 78 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 77) (stageCode 78)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_77 i)

private theorem check_78 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 78) 24 % 2=
      packedDigit 1 (stageCode 79) i.val % 2 := by decide +kernel

private theorem step_78 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 78=stageVector 79 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 78) (stageCode 79)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_78 i)

private theorem check_79 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 79) 24 % 2=
      packedDigit 1 (stageCode 80) i.val % 2 := by decide +kernel

private theorem step_79 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 79=stageVector 80 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 79) (stageCode 80)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_79 i)

private theorem check_80 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 80) 24 % 2=
      packedDigit 1 (stageCode 81) i.val % 2 := by decide +kernel

private theorem step_80 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 80=stageVector 81 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 80) (stageCode 81)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_80 i)

private theorem check_81 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 81) 24 % 2=
      packedDigit 1 (stageCode 82) i.val % 2 := by decide +kernel

private theorem step_81 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 81=stageVector 82 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 81) (stageCode 82)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_81 i)

private theorem check_82 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 82) 24 % 2=
      packedDigit 1 (stageCode 83) i.val % 2 := by decide +kernel

private theorem step_82 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 82=stageVector 83 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 82) (stageCode 83)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_82 i)

private theorem check_83 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 83) 24 % 2=
      packedDigit 1 (stageCode 84) i.val % 2 := by decide +kernel

private theorem step_83 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 83=stageVector 84 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 83) (stageCode 84)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_83 i)

private theorem check_84 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 84) 24 % 2=
      packedDigit 1 (stageCode 85) i.val % 2 := by decide +kernel

private theorem step_84 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 84=stageVector 85 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 84) (stageCode 85)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_84 i)

private theorem check_85 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 85) 24 % 2=
      packedDigit 1 (stageCode 86) i.val % 2 := by decide +kernel

private theorem step_85 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 85=stageVector 86 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 85) (stageCode 86)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_85 i)

private theorem check_86 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 86) 24 % 2=
      packedDigit 1 (stageCode 87) i.val % 2 := by decide +kernel

private theorem step_86 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 86=stageVector 87 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 86) (stageCode 87)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_86 i)

private theorem check_87 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 87) 24 % 2=
      packedDigit 1 (stageCode 88) i.val % 2 := by decide +kernel

private theorem step_87 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 87=stageVector 88 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 87) (stageCode 88)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_87 i)

private theorem check_88 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 88) 24 % 2=
      packedDigit 1 (stageCode 89) i.val % 2 := by decide +kernel

private theorem step_88 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 88=stageVector 89 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 88) (stageCode 89)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_88 i)

private theorem check_89 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 89) 24 % 2=
      packedDigit 1 (stageCode 90) i.val % 2 := by decide +kernel

private theorem step_89 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 89=stageVector 90 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 89) (stageCode 90)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_89 i)

private theorem check_90 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 90) 24 % 2=
      packedDigit 1 (stageCode 91) i.val % 2 := by decide +kernel

private theorem step_90 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 90=stageVector 91 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 90) (stageCode 91)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_90 i)

private theorem check_91 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 91) 24 % 2=
      packedDigit 1 (stageCode 92) i.val % 2 := by decide +kernel

private theorem step_91 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 91=stageVector 92 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 91) (stageCode 92)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_91 i)

private theorem check_92 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 92) 24 % 2=
      packedDigit 1 (stageCode 93) i.val % 2 := by decide +kernel

private theorem step_92 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 92=stageVector 93 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 92) (stageCode 93)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_92 i)

private theorem check_93 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 93) 24 % 2=
      packedDigit 1 (stageCode 94) i.val % 2 := by decide +kernel

private theorem step_93 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 93=stageVector 94 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 93) (stageCode 94)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_93 i)

private theorem check_94 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 94) 24 % 2=
      packedDigit 1 (stageCode 95) i.val % 2 := by decide +kernel

private theorem step_94 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 94=stageVector 95 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 94) (stageCode 95)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_94 i)

private theorem check_95 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 95) 24 % 2=
      packedDigit 1 (stageCode 96) i.val % 2 := by decide +kernel

private theorem step_95 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 95=stageVector 96 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 95) (stageCode 96)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_95 i)

private theorem check_96 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 96) 24 % 2=
      packedDigit 1 (stageCode 97) i.val % 2 := by decide +kernel

private theorem step_96 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 96=stageVector 97 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 96) (stageCode 97)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_96 i)

private theorem check_97 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 97) 24 % 2=
      packedDigit 1 (stageCode 98) i.val % 2 := by decide +kernel

private theorem step_97 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 97=stageVector 98 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 97) (stageCode 98)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_97 i)

private theorem check_98 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 98) 24 % 2=
      packedDigit 1 (stageCode 99) i.val % 2 := by decide +kernel

private theorem step_98 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 98=stageVector 99 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 98) (stageCode 99)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_98 i)

private theorem check_99 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 99) 24 % 2=
      packedDigit 1 (stageCode 100) i.val % 2 := by decide +kernel

private theorem step_99 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 99=stageVector 100 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 99) (stageCode 100)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_99 i)

private theorem check_100 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 100) 24 % 2=
      packedDigit 1 (stageCode 101) i.val % 2 := by decide +kernel

private theorem step_100 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 100=stageVector 101 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 100) (stageCode 101)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_100 i)

private theorem check_101 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 101) 24 % 2=
      packedDigit 1 (stageCode 102) i.val % 2 := by decide +kernel

private theorem step_101 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 101=stageVector 102 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 101) (stageCode 102)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_101 i)

private theorem check_102 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 102) 24 % 2=
      packedDigit 1 (stageCode 103) i.val % 2 := by decide +kernel

private theorem step_102 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 102=stageVector 103 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 102) (stageCode 103)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_102 i)

private theorem check_103 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 103) 24 % 2=
      packedDigit 1 (stageCode 104) i.val % 2 := by decide +kernel

private theorem step_103 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 103=stageVector 104 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 103) (stageCode 104)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_103 i)

private theorem check_104 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 104) 24 % 2=
      packedDigit 1 (stageCode 105) i.val % 2 := by decide +kernel

private theorem step_104 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 104=stageVector 105 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 104) (stageCode 105)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_104 i)

private theorem check_105 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 105) 24 % 2=
      packedDigit 1 (stageCode 106) i.val % 2 := by decide +kernel

private theorem step_105 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 105=stageVector 106 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 105) (stageCode 106)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_105 i)

private theorem check_106 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 106) 24 % 2=
      packedDigit 1 (stageCode 107) i.val % 2 := by decide +kernel

private theorem step_106 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 106=stageVector 107 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 106) (stageCode 107)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_106 i)

private theorem check_107 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 107) 24 % 2=
      packedDigit 1 (stageCode 108) i.val % 2 := by decide +kernel

private theorem step_107 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 107=stageVector 108 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 107) (stageCode 108)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_107 i)

private theorem check_108 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 108) 24 % 2=
      packedDigit 1 (stageCode 109) i.val % 2 := by decide +kernel

private theorem step_108 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 108=stageVector 109 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 108) (stageCode 109)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_108 i)

private theorem check_109 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 109) 24 % 2=
      packedDigit 1 (stageCode 110) i.val % 2 := by decide +kernel

private theorem step_109 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 109=stageVector 110 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 109) (stageCode 110)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_109 i)

private theorem check_110 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 110) 24 % 2=
      packedDigit 1 (stageCode 111) i.val % 2 := by decide +kernel

private theorem step_110 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 110=stageVector 111 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 110) (stageCode 111)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_110 i)

private theorem check_111 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 111) 24 % 2=
      packedDigit 1 (stageCode 112) i.val % 2 := by decide +kernel

private theorem step_111 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 111=stageVector 112 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 111) (stageCode 112)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_111 i)

private theorem check_112 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 112) 24 % 2=
      packedDigit 1 (stageCode 113) i.val % 2 := by decide +kernel

private theorem step_112 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 112=stageVector 113 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 112) (stageCode 113)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_112 i)

private theorem check_113 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 113) 24 % 2=
      packedDigit 1 (stageCode 114) i.val % 2 := by decide +kernel

private theorem step_113 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 113=stageVector 114 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 113) (stageCode 114)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_113 i)

private theorem check_114 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 114) 24 % 2=
      packedDigit 1 (stageCode 115) i.val % 2 := by decide +kernel

private theorem step_114 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 114=stageVector 115 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 114) (stageCode 115)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_114 i)

private theorem check_115 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 115) 24 % 2=
      packedDigit 1 (stageCode 116) i.val % 2 := by decide +kernel

private theorem step_115 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 115=stageVector 116 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 115) (stageCode 116)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_115 i)

private theorem check_116 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 116) 24 % 2=
      packedDigit 1 (stageCode 117) i.val % 2 := by decide +kernel

private theorem step_116 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 116=stageVector 117 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 116) (stageCode 117)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_116 i)

private theorem check_117 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 117) 24 % 2=
      packedDigit 1 (stageCode 118) i.val % 2 := by decide +kernel

private theorem step_117 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 117=stageVector 118 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 117) (stageCode 118)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_117 i)

private theorem check_118 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 118) 24 % 2=
      packedDigit 1 (stageCode 119) i.val % 2 := by decide +kernel

private theorem step_118 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 118=stageVector 119 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 118) (stageCode 119)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_118 i)

private theorem check_119 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 119) 24 % 2=
      packedDigit 1 (stageCode 120) i.val % 2 := by decide +kernel

private theorem step_119 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 119=stageVector 120 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 119) (stageCode 120)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_119 i)

private theorem check_120 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 120) 24 % 2=
      packedDigit 1 (stageCode 121) i.val % 2 := by decide +kernel

private theorem step_120 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 120=stageVector 121 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 120) (stageCode 121)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_120 i)

private theorem check_121 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 121) 24 % 2=
      packedDigit 1 (stageCode 122) i.val % 2 := by decide +kernel

private theorem step_121 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 121=stageVector 122 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 121) (stageCode 122)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_121 i)

private theorem check_122 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 122) 24 % 2=
      packedDigit 1 (stageCode 123) i.val % 2 := by decide +kernel

private theorem step_122 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 122=stageVector 123 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 122) (stageCode 123)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_122 i)

private theorem check_123 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 123) 24 % 2=
      packedDigit 1 (stageCode 124) i.val % 2 := by decide +kernel

private theorem step_123 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 123=stageVector 124 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 123) (stageCode 124)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_123 i)

private theorem check_124 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 124) 24 % 2=
      packedDigit 1 (stageCode 125) i.val % 2 := by decide +kernel

private theorem step_124 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 124=stageVector 125 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 124) (stageCode 125)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_124 i)

private theorem check_125 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 125) 24 % 2=
      packedDigit 1 (stageCode 126) i.val % 2 := by decide +kernel

private theorem step_125 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 125=stageVector 126 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 125) (stageCode 126)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_125 i)

private theorem check_126 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 126) 24 % 2=
      packedDigit 1 (stageCode 127) i.val % 2 := by decide +kernel

private theorem step_126 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 126=stageVector 127 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 126) (stageCode 127)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_126 i)

private theorem check_127 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 127) 24 % 2=
      packedDigit 1 (stageCode 128) i.val % 2 := by decide +kernel

private theorem step_127 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 127=stageVector 128 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 127) (stageCode 128)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_127 i)

private theorem check_128 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 128) 24 % 2=
      packedDigit 1 (stageCode 129) i.val % 2 := by decide +kernel

private theorem step_128 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 128=stageVector 129 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 128) (stageCode 129)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_128 i)

private theorem check_129 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 129) 24 % 2=
      packedDigit 1 (stageCode 130) i.val % 2 := by decide +kernel

private theorem step_129 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 129=stageVector 130 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 129) (stageCode 130)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_129 i)

private theorem check_130 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 130) 24 % 2=
      packedDigit 1 (stageCode 131) i.val % 2 := by decide +kernel

private theorem step_130 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 130=stageVector 131 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 130) (stageCode 131)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_130 i)

private theorem check_131 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 131) 24 % 2=
      packedDigit 1 (stageCode 132) i.val % 2 := by decide +kernel

private theorem step_131 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 131=stageVector 132 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 131) (stageCode 132)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_131 i)

private theorem check_132 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 132) 24 % 2=
      packedDigit 1 (stageCode 133) i.val % 2 := by decide +kernel

private theorem step_132 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 132=stageVector 133 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 132) (stageCode 133)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_132 i)

private theorem check_133 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 133) 24 % 2=
      packedDigit 1 (stageCode 134) i.val % 2 := by decide +kernel

private theorem step_133 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 133=stageVector 134 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 133) (stageCode 134)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_133 i)

private theorem check_134 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 134) 24 % 2=
      packedDigit 1 (stageCode 135) i.val % 2 := by decide +kernel

private theorem step_134 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 134=stageVector 135 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 134) (stageCode 135)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_134 i)

private theorem check_135 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 135) 24 % 2=
      packedDigit 1 (stageCode 136) i.val % 2 := by decide +kernel

private theorem step_135 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 135=stageVector 136 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 135) (stageCode 136)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_135 i)

private theorem check_136 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 136) 24 % 2=
      packedDigit 1 (stageCode 137) i.val % 2 := by decide +kernel

private theorem step_136 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 136=stageVector 137 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 136) (stageCode 137)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_136 i)

private theorem check_137 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 137) 24 % 2=
      packedDigit 1 (stageCode 138) i.val % 2 := by decide +kernel

private theorem step_137 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 137=stageVector 138 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 137) (stageCode 138)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_137 i)

private theorem check_138 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 138) 24 % 2=
      packedDigit 1 (stageCode 139) i.val % 2 := by decide +kernel

private theorem step_138 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 138=stageVector 139 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 138) (stageCode 139)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_138 i)

private theorem check_139 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 139) 24 % 2=
      packedDigit 1 (stageCode 140) i.val % 2 := by decide +kernel

private theorem step_139 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 139=stageVector 140 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 139) (stageCode 140)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_139 i)

private theorem check_140 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 140) 24 % 2=
      packedDigit 1 (stageCode 141) i.val % 2 := by decide +kernel

private theorem step_140 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 140=stageVector 141 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 140) (stageCode 141)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_140 i)

private theorem check_141 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 141) 24 % 2=
      packedDigit 1 (stageCode 142) i.val % 2 := by decide +kernel

private theorem step_141 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 141=stageVector 142 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 141) (stageCode 142)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_141 i)

private theorem check_142 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 142) 24 % 2=
      packedDigit 1 (stageCode 143) i.val % 2 := by decide +kernel

private theorem step_142 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 142=stageVector 143 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 142) (stageCode 143)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_142 i)

private theorem check_143 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 143) 24 % 2=
      packedDigit 1 (stageCode 144) i.val % 2 := by decide +kernel

private theorem step_143 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 143=stageVector 144 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 143) (stageCode 144)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_143 i)

private theorem check_144 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 144) 24 % 2=
      packedDigit 1 (stageCode 145) i.val % 2 := by decide +kernel

private theorem step_144 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 144=stageVector 145 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 144) (stageCode 145)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_144 i)

private theorem check_145 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 145) 24 % 2=
      packedDigit 1 (stageCode 146) i.val % 2 := by decide +kernel

private theorem step_145 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 145=stageVector 146 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 145) (stageCode 146)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_145 i)

private theorem check_146 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 146) 24 % 2=
      packedDigit 1 (stageCode 147) i.val % 2 := by decide +kernel

private theorem step_146 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 146=stageVector 147 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 146) (stageCode 147)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_146 i)

private theorem check_147 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 147) 24 % 2=
      packedDigit 1 (stageCode 148) i.val % 2 := by decide +kernel

private theorem step_147 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 147=stageVector 148 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 147) (stageCode 148)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_147 i)

private theorem check_148 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 148) 24 % 2=
      packedDigit 1 (stageCode 149) i.val % 2 := by decide +kernel

private theorem step_148 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 148=stageVector 149 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 148) (stageCode 149)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_148 i)

private theorem check_149 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 149) 24 % 2=
      packedDigit 1 (stageCode 150) i.val % 2 := by decide +kernel

private theorem step_149 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 149=stageVector 150 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 149) (stageCode 150)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_149 i)

private theorem check_150 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 150) 24 % 2=
      packedDigit 1 (stageCode 151) i.val % 2 := by decide +kernel

private theorem step_150 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 150=stageVector 151 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 150) (stageCode 151)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_150 i)

private theorem check_151 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 151) 24 % 2=
      packedDigit 1 (stageCode 152) i.val % 2 := by decide +kernel

private theorem step_151 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 151=stageVector 152 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 151) (stageCode 152)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_151 i)

private theorem check_152 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 152) 24 % 2=
      packedDigit 1 (stageCode 153) i.val % 2 := by decide +kernel

private theorem step_152 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 152=stageVector 153 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 152) (stageCode 153)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_152 i)

private theorem check_153 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 153) 24 % 2=
      packedDigit 1 (stageCode 154) i.val % 2 := by decide +kernel

private theorem step_153 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 153=stageVector 154 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 153) (stageCode 154)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_153 i)

private theorem check_154 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 154) 24 % 2=
      packedDigit 1 (stageCode 155) i.val % 2 := by decide +kernel

private theorem step_154 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 154=stageVector 155 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 154) (stageCode 155)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_154 i)

private theorem check_155 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 155) 24 % 2=
      packedDigit 1 (stageCode 156) i.val % 2 := by decide +kernel

private theorem step_155 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 155=stageVector 156 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 155) (stageCode 156)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_155 i)

private theorem check_156 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 156) 24 % 2=
      packedDigit 1 (stageCode 157) i.val % 2 := by decide +kernel

private theorem step_156 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 156=stageVector 157 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 156) (stageCode 157)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_156 i)

private theorem check_157 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 157) 24 % 2=
      packedDigit 1 (stageCode 158) i.val % 2 := by decide +kernel

private theorem step_157 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 157=stageVector 158 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 157) (stageCode 158)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_157 i)

private theorem check_158 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 158) 24 % 2=
      packedDigit 1 (stageCode 159) i.val % 2 := by decide +kernel

private theorem step_158 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 158=stageVector 159 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 158) (stageCode 159)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_158 i)

private theorem check_159 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 159) 24 % 2=
      packedDigit 1 (stageCode 160) i.val % 2 := by decide +kernel

private theorem step_159 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 159=stageVector 160 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 159) (stageCode 160)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_159 i)

private theorem check_160 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 160) 24 % 2=
      packedDigit 1 (stageCode 161) i.val % 2 := by decide +kernel

private theorem step_160 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 160=stageVector 161 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 160) (stageCode 161)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_160 i)

private theorem check_161 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 161) 24 % 2=
      packedDigit 1 (stageCode 162) i.val % 2 := by decide +kernel

private theorem step_161 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 161=stageVector 162 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 161) (stageCode 162)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_161 i)

private theorem check_162 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 162) 24 % 2=
      packedDigit 1 (stageCode 163) i.val % 2 := by decide +kernel

private theorem step_162 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 162=stageVector 163 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 162) (stageCode 163)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_162 i)

private theorem check_163 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 163) 24 % 2=
      packedDigit 1 (stageCode 164) i.val % 2 := by decide +kernel

private theorem step_163 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 163=stageVector 164 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 163) (stageCode 164)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_163 i)

private theorem check_164 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 164) 24 % 2=
      packedDigit 1 (stageCode 165) i.val % 2 := by decide +kernel

private theorem step_164 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 164=stageVector 165 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 164) (stageCode 165)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_164 i)

private theorem check_165 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 165) 24 % 2=
      packedDigit 1 (stageCode 166) i.val % 2 := by decide +kernel

private theorem step_165 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 165=stageVector 166 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 165) (stageCode 166)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_165 i)

private theorem check_166 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 166) 24 % 2=
      packedDigit 1 (stageCode 167) i.val % 2 := by decide +kernel

private theorem step_166 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 166=stageVector 167 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 166) (stageCode 167)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_166 i)

private theorem check_167 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 167) 24 % 2=
      packedDigit 1 (stageCode 168) i.val % 2 := by decide +kernel

private theorem step_167 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 167=stageVector 168 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 167) (stageCode 168)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_167 i)

private theorem check_168 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 168) 24 % 2=
      packedDigit 1 (stageCode 169) i.val % 2 := by decide +kernel

private theorem step_168 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 168=stageVector 169 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 168) (stageCode 169)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_168 i)

private theorem check_169 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 169) 24 % 2=
      packedDigit 1 (stageCode 170) i.val % 2 := by decide +kernel

private theorem step_169 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 169=stageVector 170 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 169) (stageCode 170)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_169 i)

private theorem check_170 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 170) 24 % 2=
      packedDigit 1 (stageCode 171) i.val % 2 := by decide +kernel

private theorem step_170 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 170=stageVector 171 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 170) (stageCode 171)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_170 i)

private theorem check_171 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 171) 24 % 2=
      packedDigit 1 (stageCode 172) i.val % 2 := by decide +kernel

private theorem step_171 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 171=stageVector 172 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 171) (stageCode 172)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_171 i)

private theorem check_172 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 172) 24 % 2=
      packedDigit 1 (stageCode 173) i.val % 2 := by decide +kernel

private theorem step_172 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 172=stageVector 173 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 172) (stageCode 173)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_172 i)

private theorem check_173 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 173) 24 % 2=
      packedDigit 1 (stageCode 174) i.val % 2 := by decide +kernel

private theorem step_173 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 173=stageVector 174 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 173) (stageCode 174)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_173 i)

private theorem check_174 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 174) 24 % 2=
      packedDigit 1 (stageCode 175) i.val % 2 := by decide +kernel

private theorem step_174 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 174=stageVector 175 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 174) (stageCode 175)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_174 i)

private theorem check_175 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 175) 24 % 2=
      packedDigit 1 (stageCode 176) i.val % 2 := by decide +kernel

private theorem step_175 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 175=stageVector 176 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 175) (stageCode 176)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_175 i)

private theorem check_176 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 176) 24 % 2=
      packedDigit 1 (stageCode 177) i.val % 2 := by decide +kernel

private theorem step_176 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 176=stageVector 177 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 176) (stageCode 177)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_176 i)

private theorem check_177 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 177) 24 % 2=
      packedDigit 1 (stageCode 178) i.val % 2 := by decide +kernel

private theorem step_177 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 177=stageVector 178 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 177) (stageCode 178)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_177 i)

private theorem check_178 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 178) 24 % 2=
      packedDigit 1 (stageCode 179) i.val % 2 := by decide +kernel

private theorem step_178 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 178=stageVector 179 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 178) (stageCode 179)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_178 i)

private theorem check_179 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 179) 24 % 2=
      packedDigit 1 (stageCode 180) i.val % 2 := by decide +kernel

private theorem step_179 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 179=stageVector 180 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 179) (stageCode 180)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_179 i)

private theorem check_180 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 180) 24 % 2=
      packedDigit 1 (stageCode 181) i.val % 2 := by decide +kernel

private theorem step_180 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 180=stageVector 181 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 180) (stageCode 181)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_180 i)

private theorem check_181 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 181) 24 % 2=
      packedDigit 1 (stageCode 182) i.val % 2 := by decide +kernel

private theorem step_181 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 181=stageVector 182 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 181) (stageCode 182)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_181 i)

private theorem check_182 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 182) 24 % 2=
      packedDigit 1 (stageCode 183) i.val % 2 := by decide +kernel

private theorem step_182 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 182=stageVector 183 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 182) (stageCode 183)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_182 i)

private theorem check_183 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 183) 24 % 2=
      packedDigit 1 (stageCode 184) i.val % 2 := by decide +kernel

private theorem step_183 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 183=stageVector 184 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 183) (stageCode 184)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_183 i)

private theorem check_184 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 184) 24 % 2=
      packedDigit 1 (stageCode 185) i.val % 2 := by decide +kernel

private theorem step_184 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 184=stageVector 185 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 184) (stageCode 185)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_184 i)

private theorem check_185 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 185) 24 % 2=
      packedDigit 1 (stageCode 186) i.val % 2 := by decide +kernel

private theorem step_185 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 185=stageVector 186 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 185) (stageCode 186)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_185 i)

private theorem check_186 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 186) 24 % 2=
      packedDigit 1 (stageCode 187) i.val % 2 := by decide +kernel

private theorem step_186 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 186=stageVector 187 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 186) (stageCode 187)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_186 i)

private theorem check_187 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 187) 24 % 2=
      packedDigit 1 (stageCode 188) i.val % 2 := by decide +kernel

private theorem step_187 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 187=stageVector 188 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 187) (stageCode 188)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_187 i)

private theorem check_188 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 188) 24 % 2=
      packedDigit 1 (stageCode 189) i.val % 2 := by decide +kernel

private theorem step_188 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 188=stageVector 189 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 188) (stageCode 189)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_188 i)

private theorem check_189 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 189) 24 % 2=
      packedDigit 1 (stageCode 190) i.val % 2 := by decide +kernel

private theorem step_189 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 189=stageVector 190 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 189) (stageCode 190)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_189 i)

private theorem check_190 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 190) 24 % 2=
      packedDigit 1 (stageCode 191) i.val % 2 := by decide +kernel

private theorem step_190 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 190=stageVector 191 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 190) (stageCode 191)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_190 i)

private theorem check_191 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 191) 24 % 2=
      packedDigit 1 (stageCode 192) i.val % 2 := by decide +kernel

private theorem step_191 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 191=stageVector 192 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 191) (stageCode 192)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_191 i)

private theorem check_192 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 192) 24 % 2=
      packedDigit 1 (stageCode 193) i.val % 2 := by decide +kernel

private theorem step_192 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 192=stageVector 193 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 192) (stageCode 193)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_192 i)

private theorem check_193 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 193) 24 % 2=
      packedDigit 1 (stageCode 194) i.val % 2 := by decide +kernel

private theorem step_193 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 193=stageVector 194 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 193) (stageCode 194)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_193 i)

private theorem check_194 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 194) 24 % 2=
      packedDigit 1 (stageCode 195) i.val % 2 := by decide +kernel

private theorem step_194 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 194=stageVector 195 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 194) (stageCode 195)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_194 i)

private theorem check_195 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 195) 24 % 2=
      packedDigit 1 (stageCode 196) i.val % 2 := by decide +kernel

private theorem step_195 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 195=stageVector 196 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 195) (stageCode 196)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_195 i)

private theorem check_196 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 196) 24 % 2=
      packedDigit 1 (stageCode 197) i.val % 2 := by decide +kernel

private theorem step_196 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 196=stageVector 197 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 196) (stageCode 197)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_196 i)

private theorem check_197 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 197) 24 % 2=
      packedDigit 1 (stageCode 198) i.val % 2 := by decide +kernel

private theorem step_197 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 197=stageVector 198 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 197) (stageCode 198)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_197 i)

private theorem check_198 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 198) 24 % 2=
      packedDigit 1 (stageCode 199) i.val % 2 := by decide +kernel

private theorem step_198 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 198=stageVector 199 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 198) (stageCode 199)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_198 i)

private theorem check_199 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 199) 24 % 2=
      packedDigit 1 (stageCode 200) i.val % 2 := by decide +kernel

private theorem step_199 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 199=stageVector 200 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 199) (stageCode 200)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_199 i)

private theorem check_200 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 200) 24 % 2=
      packedDigit 1 (stageCode 201) i.val % 2 := by decide +kernel

private theorem step_200 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 200=stageVector 201 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 200) (stageCode 201)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_200 i)

private theorem check_201 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 201) 24 % 2=
      packedDigit 1 (stageCode 202) i.val % 2 := by decide +kernel

private theorem step_201 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 201=stageVector 202 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 201) (stageCode 202)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_201 i)

private theorem check_202 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 202) 24 % 2=
      packedDigit 1 (stageCode 203) i.val % 2 := by decide +kernel

private theorem step_202 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 202=stageVector 203 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 202) (stageCode 203)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_202 i)

private theorem check_203 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 203) 24 % 2=
      packedDigit 1 (stageCode 204) i.val % 2 := by decide +kernel

private theorem step_203 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 203=stageVector 204 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 203) (stageCode 204)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_203 i)

private theorem check_204 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 204) 24 % 2=
      packedDigit 1 (stageCode 205) i.val % 2 := by decide +kernel

private theorem step_204 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 204=stageVector 205 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 204) (stageCode 205)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_204 i)

private theorem check_205 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 205) 24 % 2=
      packedDigit 1 (stageCode 206) i.val % 2 := by decide +kernel

private theorem step_205 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 205=stageVector 206 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 205) (stageCode 206)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_205 i)

private theorem check_206 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 206) 24 % 2=
      packedDigit 1 (stageCode 207) i.val % 2 := by decide +kernel

private theorem step_206 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 206=stageVector 207 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 206) (stageCode 207)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_206 i)

private theorem check_207 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 207) 24 % 2=
      packedDigit 1 (stageCode 208) i.val % 2 := by decide +kernel

private theorem step_207 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 207=stageVector 208 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 207) (stageCode 208)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_207 i)

private theorem check_208 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 208) 24 % 2=
      packedDigit 1 (stageCode 209) i.val % 2 := by decide +kernel

private theorem step_208 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 208=stageVector 209 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 208) (stageCode 209)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_208 i)

private theorem check_209 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 209) 24 % 2=
      packedDigit 1 (stageCode 210) i.val % 2 := by decide +kernel

private theorem step_209 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 209=stageVector 210 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 209) (stageCode 210)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_209 i)

private theorem check_210 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 210) 24 % 2=
      packedDigit 1 (stageCode 211) i.val % 2 := by decide +kernel

private theorem step_210 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 210=stageVector 211 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 210) (stageCode 211)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_210 i)

private theorem check_211 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 211) 24 % 2=
      packedDigit 1 (stageCode 212) i.val % 2 := by decide +kernel

private theorem step_211 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 211=stageVector 212 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 211) (stageCode 212)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_211 i)

private theorem check_212 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 212) 24 % 2=
      packedDigit 1 (stageCode 213) i.val % 2 := by decide +kernel

private theorem step_212 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 212=stageVector 213 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 212) (stageCode 213)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_212 i)

private theorem check_213 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 213) 24 % 2=
      packedDigit 1 (stageCode 214) i.val % 2 := by decide +kernel

private theorem step_213 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 213=stageVector 214 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 213) (stageCode 214)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_213 i)

private theorem check_214 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 214) 24 % 2=
      packedDigit 1 (stageCode 215) i.val % 2 := by decide +kernel

private theorem step_214 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 214=stageVector 215 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 214) (stageCode 215)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_214 i)

private theorem check_215 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 215) 24 % 2=
      packedDigit 1 (stageCode 216) i.val % 2 := by decide +kernel

private theorem step_215 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 215=stageVector 216 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 215) (stageCode 216)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_215 i)

private theorem check_216 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 216) 24 % 2=
      packedDigit 1 (stageCode 217) i.val % 2 := by decide +kernel

private theorem step_216 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 216=stageVector 217 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 216) (stageCode 217)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_216 i)

private theorem check_217 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 217) 24 % 2=
      packedDigit 1 (stageCode 218) i.val % 2 := by decide +kernel

private theorem step_217 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 217=stageVector 218 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 217) (stageCode 218)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_217 i)

private theorem check_218 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 218) 24 % 2=
      packedDigit 1 (stageCode 219) i.val % 2 := by decide +kernel

private theorem step_218 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 218=stageVector 219 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 218) (stageCode 219)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_218 i)

private theorem check_219 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 219) 24 % 2=
      packedDigit 1 (stageCode 220) i.val % 2 := by decide +kernel

private theorem step_219 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 219=stageVector 220 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 219) (stageCode 220)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_219 i)

private theorem check_220 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 220) 24 % 2=
      packedDigit 1 (stageCode 221) i.val % 2 := by decide +kernel

private theorem step_220 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 220=stageVector 221 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 220) (stageCode 221)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_220 i)

private theorem check_221 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 221) 24 % 2=
      packedDigit 1 (stageCode 222) i.val % 2 := by decide +kernel

private theorem step_221 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 221=stageVector 222 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 221) (stageCode 222)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_221 i)

private theorem check_222 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 222) 24 % 2=
      packedDigit 1 (stageCode 223) i.val % 2 := by decide +kernel

private theorem step_222 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 222=stageVector 223 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 222) (stageCode 223)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_222 i)

private theorem check_223 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 223) 24 % 2=
      packedDigit 1 (stageCode 224) i.val % 2 := by decide +kernel

private theorem step_223 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 223=stageVector 224 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 223) (stageCode 224)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_223 i)

private theorem check_224 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 224) 24 % 2=
      packedDigit 1 (stageCode 225) i.val % 2 := by decide +kernel

private theorem step_224 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 224=stageVector 225 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 224) (stageCode 225)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_224 i)

private theorem check_225 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 225) 24 % 2=
      packedDigit 1 (stageCode 226) i.val % 2 := by decide +kernel

private theorem step_225 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 225=stageVector 226 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 225) (stageCode 226)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_225 i)

private theorem check_226 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 226) 24 % 2=
      packedDigit 1 (stageCode 227) i.val % 2 := by decide +kernel

private theorem step_226 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 226=stageVector 227 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 226) (stageCode 227)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_226 i)

private theorem check_227 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 227) 24 % 2=
      packedDigit 1 (stageCode 228) i.val % 2 := by decide +kernel

private theorem step_227 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 227=stageVector 228 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 227) (stageCode 228)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_227 i)

private theorem check_228 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 228) 24 % 2=
      packedDigit 1 (stageCode 229) i.val % 2 := by decide +kernel

private theorem step_228 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 228=stageVector 229 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 228) (stageCode 229)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_228 i)

private theorem check_229 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 229) 24 % 2=
      packedDigit 1 (stageCode 230) i.val % 2 := by decide +kernel

private theorem step_229 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 229=stageVector 230 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 229) (stageCode 230)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_229 i)

private theorem check_230 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 230) 24 % 2=
      packedDigit 1 (stageCode 231) i.val % 2 := by decide +kernel

private theorem step_230 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 230=stageVector 231 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 230) (stageCode 231)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_230 i)

private theorem check_231 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 231) 24 % 2=
      packedDigit 1 (stageCode 232) i.val % 2 := by decide +kernel

private theorem step_231 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 231=stageVector 232 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 231) (stageCode 232)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_231 i)

private theorem check_232 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 232) 24 % 2=
      packedDigit 1 (stageCode 233) i.val % 2 := by decide +kernel

private theorem step_232 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 232=stageVector 233 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 232) (stageCode 233)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_232 i)

private theorem check_233 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 233) 24 % 2=
      packedDigit 1 (stageCode 234) i.val % 2 := by decide +kernel

private theorem step_233 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 233=stageVector 234 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 233) (stageCode 234)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_233 i)

private theorem check_234 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 234) 24 % 2=
      packedDigit 1 (stageCode 235) i.val % 2 := by decide +kernel

private theorem step_234 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 234=stageVector 235 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 234) (stageCode 235)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_234 i)

private theorem check_235 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 235) 24 % 2=
      packedDigit 1 (stageCode 236) i.val % 2 := by decide +kernel

private theorem step_235 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 235=stageVector 236 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 235) (stageCode 236)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_235 i)

private theorem check_236 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 236) 24 % 2=
      packedDigit 1 (stageCode 237) i.val % 2 := by decide +kernel

private theorem step_236 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 236=stageVector 237 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 236) (stageCode 237)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_236 i)

private theorem check_237 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 237) 24 % 2=
      packedDigit 1 (stageCode 238) i.val % 2 := by decide +kernel

private theorem step_237 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 237=stageVector 238 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 237) (stageCode 238)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_237 i)

private theorem check_238 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 238) 24 % 2=
      packedDigit 1 (stageCode 239) i.val % 2 := by decide +kernel

private theorem step_238 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 238=stageVector 239 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 238) (stageCode 239)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_238 i)

private theorem check_239 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 239) 24 % 2=
      packedDigit 1 (stageCode 240) i.val % 2 := by decide +kernel

private theorem step_239 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 239=stageVector 240 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 239) (stageCode 240)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_239 i)

private theorem check_240 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 240) 24 % 2=
      packedDigit 1 (stageCode 241) i.val % 2 := by decide +kernel

private theorem step_240 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 240=stageVector 241 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 240) (stageCode 241)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_240 i)

private theorem check_241 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 241) 24 % 2=
      packedDigit 1 (stageCode 242) i.val % 2 := by decide +kernel

private theorem step_241 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 241=stageVector 242 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 241) (stageCode 242)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_241 i)

private theorem check_242 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 242) 24 % 2=
      packedDigit 1 (stageCode 243) i.val % 2 := by decide +kernel

private theorem step_242 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 242=stageVector 243 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 242) (stageCode 243)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_242 i)

private theorem check_243 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 243) 24 % 2=
      packedDigit 1 (stageCode 244) i.val % 2 := by decide +kernel

private theorem step_243 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 243=stageVector 244 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 243) (stageCode 244)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_243 i)

private theorem check_244 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 244) 24 % 2=
      packedDigit 1 (stageCode 245) i.val % 2 := by decide +kernel

private theorem step_244 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 244=stageVector 245 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 244) (stageCode 245)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_244 i)

private theorem check_245 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 245) 24 % 2=
      packedDigit 1 (stageCode 246) i.val % 2 := by decide +kernel

private theorem step_245 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 245=stageVector 246 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 245) (stageCode 246)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_245 i)

private theorem check_246 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 246) 24 % 2=
      packedDigit 1 (stageCode 247) i.val % 2 := by decide +kernel

private theorem step_246 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 246=stageVector 247 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 246) (stageCode 247)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_246 i)

private theorem check_247 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 247) 24 % 2=
      packedDigit 1 (stageCode 248) i.val % 2 := by decide +kernel

private theorem step_247 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 247=stageVector 248 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 247) (stageCode 248)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_247 i)

private theorem check_248 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 248) 24 % 2=
      packedDigit 1 (stageCode 249) i.val % 2 := by decide +kernel

private theorem step_248 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 248=stageVector 249 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 248) (stageCode 249)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_248 i)

private theorem check_249 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 249) 24 % 2=
      packedDigit 1 (stageCode 250) i.val % 2 := by decide +kernel

private theorem step_249 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 249=stageVector 250 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 249) (stageCode 250)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_249 i)

private theorem check_250 : ∀ i : Fin 24,
    packedDot 1 (firstRowCode i.val) (stageCode 250) 24 % 2=
      packedDigit 1 (stageCode 251) i.val % 2 := by decide +kernel

private theorem step_250 : CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ
    stageVector 250=stageVector 251 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows1 i
    (firstRowCode i.val) (stageCode 250) (stageCode 251)
    (fun j => CFSGCoOneUpstreamPrimeElevenFirstRows.binding i j) (check_250 i)

private theorem check_251 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 251) 24 % 2=
      packedDigit 1 (stageCode 252) i.val % 2 := by decide +kernel

private theorem step_251 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 251=stageVector 252 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 251) (stageCode 252)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_251 i)

private theorem check_252 : ∀ i : Fin 24,
    packedDot 1 (secondRowCode i.val) (stageCode 252) 24 % 2=
      packedDigit 1 (stageCode 253) i.val % 2 := by decide +kernel

private theorem step_252 : CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ
    stageVector 252=stageVector 253 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 2 24 1 rows2 i
    (secondRowCode i.val) (stageCode 252) (stageCode 253)
    (fun j => CFSGCoOneUpstreamPrimeElevenSecondRows.binding i j) (check_252 i)

private theorem phase_0 (i : Fin 11) :
    CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ stageVector (23*i.val+0)=
      stageVector (23*i.val+1) := by
  fin_cases i
  · exact step_0
  · exact step_23
  · exact step_46
  · exact step_69
  · exact step_92
  · exact step_115
  · exact step_138
  · exact step_161
  · exact step_184
  · exact step_207
  · exact step_230

private theorem phase_1 (i : Fin 11) :
    CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ stageVector (23*i.val+1)=
      stageVector (23*i.val+2) := by
  fin_cases i
  · exact step_1
  · exact step_24
  · exact step_47
  · exact step_70
  · exact step_93
  · exact step_116
  · exact step_139
  · exact step_162
  · exact step_185
  · exact step_208
  · exact step_231

private theorem phase_2 (i : Fin 11) :
    CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ stageVector (23*i.val+2)=
      stageVector (23*i.val+3) := by
  fin_cases i
  · exact step_2
  · exact step_25
  · exact step_48
  · exact step_71
  · exact step_94
  · exact step_117
  · exact step_140
  · exact step_163
  · exact step_186
  · exact step_209
  · exact step_232

private theorem phase_3 (i : Fin 11) :
    CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ stageVector (23*i.val+3)=
      stageVector (23*i.val+4) := by
  fin_cases i
  · exact step_3
  · exact step_26
  · exact step_49
  · exact step_72
  · exact step_95
  · exact step_118
  · exact step_141
  · exact step_164
  · exact step_187
  · exact step_210
  · exact step_233

private theorem phase_4 (i : Fin 11) :
    CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ stageVector (23*i.val+4)=
      stageVector (23*i.val+5) := by
  fin_cases i
  · exact step_4
  · exact step_27
  · exact step_50
  · exact step_73
  · exact step_96
  · exact step_119
  · exact step_142
  · exact step_165
  · exact step_188
  · exact step_211
  · exact step_234

private theorem phase_5 (i : Fin 11) :
    CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ stageVector (23*i.val+5)=
      stageVector (23*i.val+6) := by
  fin_cases i
  · exact step_5
  · exact step_28
  · exact step_51
  · exact step_74
  · exact step_97
  · exact step_120
  · exact step_143
  · exact step_166
  · exact step_189
  · exact step_212
  · exact step_235

private theorem phase_6 (i : Fin 11) :
    CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ stageVector (23*i.val+6)=
      stageVector (23*i.val+7) := by
  fin_cases i
  · exact step_6
  · exact step_29
  · exact step_52
  · exact step_75
  · exact step_98
  · exact step_121
  · exact step_144
  · exact step_167
  · exact step_190
  · exact step_213
  · exact step_236

private theorem phase_7 (i : Fin 11) :
    CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ stageVector (23*i.val+7)=
      stageVector (23*i.val+8) := by
  fin_cases i
  · exact step_7
  · exact step_30
  · exact step_53
  · exact step_76
  · exact step_99
  · exact step_122
  · exact step_145
  · exact step_168
  · exact step_191
  · exact step_214
  · exact step_237

private theorem phase_8 (i : Fin 11) :
    CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ stageVector (23*i.val+8)=
      stageVector (23*i.val+9) := by
  fin_cases i
  · exact step_8
  · exact step_31
  · exact step_54
  · exact step_77
  · exact step_100
  · exact step_123
  · exact step_146
  · exact step_169
  · exact step_192
  · exact step_215
  · exact step_238

private theorem phase_9 (i : Fin 11) :
    CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ stageVector (23*i.val+9)=
      stageVector (23*i.val+10) := by
  fin_cases i
  · exact step_9
  · exact step_32
  · exact step_55
  · exact step_78
  · exact step_101
  · exact step_124
  · exact step_147
  · exact step_170
  · exact step_193
  · exact step_216
  · exact step_239

private theorem phase_10 (i : Fin 11) :
    CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ stageVector (23*i.val+10)=
      stageVector (23*i.val+11) := by
  fin_cases i
  · exact step_10
  · exact step_33
  · exact step_56
  · exact step_79
  · exact step_102
  · exact step_125
  · exact step_148
  · exact step_171
  · exact step_194
  · exact step_217
  · exact step_240

private theorem phase_11 (i : Fin 11) :
    CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ stageVector (23*i.val+11)=
      stageVector (23*i.val+12) := by
  fin_cases i
  · exact step_11
  · exact step_34
  · exact step_57
  · exact step_80
  · exact step_103
  · exact step_126
  · exact step_149
  · exact step_172
  · exact step_195
  · exact step_218
  · exact step_241

private theorem phase_12 (i : Fin 11) :
    CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ stageVector (23*i.val+12)=
      stageVector (23*i.val+13) := by
  fin_cases i
  · exact step_12
  · exact step_35
  · exact step_58
  · exact step_81
  · exact step_104
  · exact step_127
  · exact step_150
  · exact step_173
  · exact step_196
  · exact step_219
  · exact step_242

private theorem phase_13 (i : Fin 11) :
    CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ stageVector (23*i.val+13)=
      stageVector (23*i.val+14) := by
  fin_cases i
  · exact step_13
  · exact step_36
  · exact step_59
  · exact step_82
  · exact step_105
  · exact step_128
  · exact step_151
  · exact step_174
  · exact step_197
  · exact step_220
  · exact step_243

private theorem phase_14 (i : Fin 11) :
    CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ stageVector (23*i.val+14)=
      stageVector (23*i.val+15) := by
  fin_cases i
  · exact step_14
  · exact step_37
  · exact step_60
  · exact step_83
  · exact step_106
  · exact step_129
  · exact step_152
  · exact step_175
  · exact step_198
  · exact step_221
  · exact step_244

private theorem phase_15 (i : Fin 11) :
    CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ stageVector (23*i.val+15)=
      stageVector (23*i.val+16) := by
  fin_cases i
  · exact step_15
  · exact step_38
  · exact step_61
  · exact step_84
  · exact step_107
  · exact step_130
  · exact step_153
  · exact step_176
  · exact step_199
  · exact step_222
  · exact step_245

private theorem phase_16 (i : Fin 11) :
    CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ stageVector (23*i.val+16)=
      stageVector (23*i.val+17) := by
  fin_cases i
  · exact step_16
  · exact step_39
  · exact step_62
  · exact step_85
  · exact step_108
  · exact step_131
  · exact step_154
  · exact step_177
  · exact step_200
  · exact step_223
  · exact step_246

private theorem phase_17 (i : Fin 11) :
    CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ stageVector (23*i.val+17)=
      stageVector (23*i.val+18) := by
  fin_cases i
  · exact step_17
  · exact step_40
  · exact step_63
  · exact step_86
  · exact step_109
  · exact step_132
  · exact step_155
  · exact step_178
  · exact step_201
  · exact step_224
  · exact step_247

private theorem phase_18 (i : Fin 11) :
    CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ stageVector (23*i.val+18)=
      stageVector (23*i.val+19) := by
  fin_cases i
  · exact step_18
  · exact step_41
  · exact step_64
  · exact step_87
  · exact step_110
  · exact step_133
  · exact step_156
  · exact step_179
  · exact step_202
  · exact step_225
  · exact step_248

private theorem phase_19 (i : Fin 11) :
    CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ stageVector (23*i.val+19)=
      stageVector (23*i.val+20) := by
  fin_cases i
  · exact step_19
  · exact step_42
  · exact step_65
  · exact step_88
  · exact step_111
  · exact step_134
  · exact step_157
  · exact step_180
  · exact step_203
  · exact step_226
  · exact step_249

private theorem phase_20 (i : Fin 11) :
    CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ stageVector (23*i.val+20)=
      stageVector (23*i.val+21) := by
  fin_cases i
  · exact step_20
  · exact step_43
  · exact step_66
  · exact step_89
  · exact step_112
  · exact step_135
  · exact step_158
  · exact step_181
  · exact step_204
  · exact step_227
  · exact step_250

private theorem phase_21 (i : Fin 11) :
    CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ stageVector (23*i.val+21)=
      stageVector (23*i.val+22) := by
  fin_cases i
  · exact step_21
  · exact step_44
  · exact step_67
  · exact step_90
  · exact step_113
  · exact step_136
  · exact step_159
  · exact step_182
  · exact step_205
  · exact step_228
  · exact step_251

private theorem phase_22 (i : Fin 11) :
    CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ stageVector (23*i.val+22)=
      stageVector (23*i.val+23) := by
  fin_cases i
  · exact step_22
  · exact step_45
  · exact step_68
  · exact step_91
  · exact step_114
  · exact step_137
  · exact step_160
  · exact step_183
  · exact step_206
  · exact step_229
  · exact step_252

theorem word_step (i : Fin 11) : selectedEnd (vectors i.castSucc)=vectors i.succ := by
  rw [selectedEnd_apply]
  change (CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ (CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ (CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ (CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ (CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ (CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ (CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ (CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ (CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ (CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ (CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ (CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ (CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ (CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ (CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ (CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ (CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ (CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ (CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ (CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ (CFSG.Models.MatrixData.matrix 2 24 rows1 *ᵥ (CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ (CFSG.Models.MatrixData.matrix 2 24 rows2 *ᵥ stageVector (23*i.val+0))))))))))))))))))))))))=stageVector (23*(i.val+1))
  rw [phase_0,phase_1,phase_2,phase_3,phase_4,phase_5,phase_6,phase_7,phase_8,phase_9,phase_10,phase_11,phase_12,phase_13,phase_14,phase_15,phase_16,phase_17,phase_18,phase_19,phase_20,phase_21,phase_22]
  exact congrArg stageVector (by omega)

attribute [local irreducible] selectedEnd CFSG.Models.MatrixData.matrix
  CFSG.Models.MatrixData.generators rows1 rows2
  MatrixModelSelectedPositiveWordPrimePeriod.wordEnd

set_option maxRecDepth 4096 in
theorem selected_return : (selectedEnd^11) (vectors 0)=vectors 0 := by
  have hp : (selectedEnd ^ 11) (vectors 0) = vectors (Fin.last 11) :=
    LinearMapSelectedKrylovPeriod.pow_apply_eq_vector selectedEnd 11 vectors
      word_step (Fin.last 11)
  have he : vectors (Fin.last 11)=vectors 0 := by
    funext j
    change (packedDigit 1 (stageCode 253) j.val : ZMod 2)=
      (packedDigit 1 (stageCode 0) j.val : ZMod 2)
    rfl
  exact Eq.trans hp he

set_option maxRecDepth 4096 in
theorem selected_moved : selectedEnd (vectors 0)≠vectors 0 := by
  intro he
  have hn : vectors 1 (2 : Fin 24)≠vectors 0 (2 : Fin 24) := by decide +kernel
  exact hn (congrArg (fun v : CFSGCoOneUpstreamPrimeElevenPackedData.V => v (2 : Fin 24)) ((word_step 0).symm.trans he))

set_option maxRecDepth 4096 in
theorem eleven_dvd_card (hn : ¬IsMulCommutative Model) : 11 ∣ Nat.card Model := by
  apply MatrixModelSelectedPositiveWordPrimePeriod.prime_dvd_card 2 24 rows1 rows2 actualWord
    11 (by decide) (vectors 0)
  · rw [wordEnd_binding]
    exact selected_return
  · rw [wordEnd_binding]
    exact selected_moved
  · exact hn

end SymmetricSubgroupAsymptotics.CFSGCoOneSelectedUpstreamPositivePrimeEleven
