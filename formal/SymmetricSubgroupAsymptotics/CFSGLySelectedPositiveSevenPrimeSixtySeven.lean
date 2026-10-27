import SymmetricSubgroupAsymptotics.CFSGLyPrimeSixtySevenFirstRows
import SymmetricSubgroupAsymptotics.CFSGLyPrimeSixtySevenSecondRows
import SymmetricSubgroupAsymptotics.CFSGLySelectedPositiveSevenWord
import SymmetricSubgroupAsymptotics.MatrixModelSelectedRowVectorReflection
import SymmetricSubgroupAsymptotics.LinearMapSelectedKrylovPeriod

/-! SAME selected original matvecs. Separate arithmetic commands; no whole-word order. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGLySelectedPositiveSevenPrimeSixtySeven
open MatrixNaturalRowDotReflection CFSGLyPrimeSixtySevenPackedData CFSGLySelectedPositiveSevenWord
open CFSG.Models.MatrixGroups.Ly

private theorem check_0 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 0) 111 % 5=
      packedDigit 3 (stageCode 1) i.val % 5 := by decide +kernel

private theorem step_0 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 0=stageVector 1 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 0) (stageCode 1)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_0 i)

private theorem check_1 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 1) 111 % 5=
      packedDigit 3 (stageCode 2) i.val % 5 := by decide +kernel

private theorem step_1 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 1=stageVector 2 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 1) (stageCode 2)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_1 i)

private theorem check_2 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 2) 111 % 5=
      packedDigit 3 (stageCode 3) i.val % 5 := by decide +kernel

private theorem step_2 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 2=stageVector 3 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 2) (stageCode 3)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_2 i)

private theorem check_3 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 3) 111 % 5=
      packedDigit 3 (stageCode 4) i.val % 5 := by decide +kernel

private theorem step_3 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 3=stageVector 4 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 3) (stageCode 4)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_3 i)

private theorem check_4 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 4) 111 % 5=
      packedDigit 3 (stageCode 5) i.val % 5 := by decide +kernel

private theorem step_4 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 4=stageVector 5 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 4) (stageCode 5)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_4 i)

private theorem check_5 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 5) 111 % 5=
      packedDigit 3 (stageCode 6) i.val % 5 := by decide +kernel

private theorem step_5 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 5=stageVector 6 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 5) (stageCode 6)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_5 i)

private theorem check_6 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 6) 111 % 5=
      packedDigit 3 (stageCode 7) i.val % 5 := by decide +kernel

private theorem step_6 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 6=stageVector 7 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 6) (stageCode 7)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_6 i)

private theorem check_7 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 7) 111 % 5=
      packedDigit 3 (stageCode 8) i.val % 5 := by decide +kernel

private theorem step_7 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 7=stageVector 8 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 7) (stageCode 8)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_7 i)

private theorem check_8 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 8) 111 % 5=
      packedDigit 3 (stageCode 9) i.val % 5 := by decide +kernel

private theorem step_8 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 8=stageVector 9 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 8) (stageCode 9)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_8 i)

private theorem check_9 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 9) 111 % 5=
      packedDigit 3 (stageCode 10) i.val % 5 := by decide +kernel

private theorem step_9 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 9=stageVector 10 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 9) (stageCode 10)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_9 i)

private theorem check_10 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 10) 111 % 5=
      packedDigit 3 (stageCode 11) i.val % 5 := by decide +kernel

private theorem step_10 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 10=stageVector 11 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 10) (stageCode 11)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_10 i)

private theorem check_11 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 11) 111 % 5=
      packedDigit 3 (stageCode 12) i.val % 5 := by decide +kernel

private theorem step_11 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 11=stageVector 12 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 11) (stageCode 12)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_11 i)

private theorem check_12 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 12) 111 % 5=
      packedDigit 3 (stageCode 13) i.val % 5 := by decide +kernel

private theorem step_12 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 12=stageVector 13 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 12) (stageCode 13)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_12 i)

private theorem check_13 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 13) 111 % 5=
      packedDigit 3 (stageCode 14) i.val % 5 := by decide +kernel

private theorem step_13 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 13=stageVector 14 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 13) (stageCode 14)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_13 i)

private theorem check_14 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 14) 111 % 5=
      packedDigit 3 (stageCode 15) i.val % 5 := by decide +kernel

private theorem step_14 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 14=stageVector 15 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 14) (stageCode 15)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_14 i)

private theorem check_15 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 15) 111 % 5=
      packedDigit 3 (stageCode 16) i.val % 5 := by decide +kernel

private theorem step_15 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 15=stageVector 16 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 15) (stageCode 16)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_15 i)

private theorem check_16 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 16) 111 % 5=
      packedDigit 3 (stageCode 17) i.val % 5 := by decide +kernel

private theorem step_16 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 16=stageVector 17 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 16) (stageCode 17)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_16 i)

private theorem check_17 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 17) 111 % 5=
      packedDigit 3 (stageCode 18) i.val % 5 := by decide +kernel

private theorem step_17 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 17=stageVector 18 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 17) (stageCode 18)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_17 i)

private theorem check_18 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 18) 111 % 5=
      packedDigit 3 (stageCode 19) i.val % 5 := by decide +kernel

private theorem step_18 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 18=stageVector 19 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 18) (stageCode 19)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_18 i)

private theorem check_19 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 19) 111 % 5=
      packedDigit 3 (stageCode 20) i.val % 5 := by decide +kernel

private theorem step_19 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 19=stageVector 20 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 19) (stageCode 20)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_19 i)

private theorem check_20 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 20) 111 % 5=
      packedDigit 3 (stageCode 21) i.val % 5 := by decide +kernel

private theorem step_20 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 20=stageVector 21 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 20) (stageCode 21)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_20 i)

private theorem check_21 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 21) 111 % 5=
      packedDigit 3 (stageCode 22) i.val % 5 := by decide +kernel

private theorem step_21 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 21=stageVector 22 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 21) (stageCode 22)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_21 i)

private theorem check_22 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 22) 111 % 5=
      packedDigit 3 (stageCode 23) i.val % 5 := by decide +kernel

private theorem step_22 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 22=stageVector 23 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 22) (stageCode 23)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_22 i)

private theorem check_23 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 23) 111 % 5=
      packedDigit 3 (stageCode 24) i.val % 5 := by decide +kernel

private theorem step_23 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 23=stageVector 24 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 23) (stageCode 24)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_23 i)

private theorem check_24 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 24) 111 % 5=
      packedDigit 3 (stageCode 25) i.val % 5 := by decide +kernel

private theorem step_24 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 24=stageVector 25 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 24) (stageCode 25)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_24 i)

private theorem check_25 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 25) 111 % 5=
      packedDigit 3 (stageCode 26) i.val % 5 := by decide +kernel

private theorem step_25 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 25=stageVector 26 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 25) (stageCode 26)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_25 i)

private theorem check_26 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 26) 111 % 5=
      packedDigit 3 (stageCode 27) i.val % 5 := by decide +kernel

private theorem step_26 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 26=stageVector 27 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 26) (stageCode 27)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_26 i)

private theorem check_27 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 27) 111 % 5=
      packedDigit 3 (stageCode 28) i.val % 5 := by decide +kernel

private theorem step_27 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 27=stageVector 28 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 27) (stageCode 28)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_27 i)

private theorem check_28 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 28) 111 % 5=
      packedDigit 3 (stageCode 29) i.val % 5 := by decide +kernel

private theorem step_28 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 28=stageVector 29 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 28) (stageCode 29)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_28 i)

private theorem check_29 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 29) 111 % 5=
      packedDigit 3 (stageCode 30) i.val % 5 := by decide +kernel

private theorem step_29 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 29=stageVector 30 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 29) (stageCode 30)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_29 i)

private theorem check_30 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 30) 111 % 5=
      packedDigit 3 (stageCode 31) i.val % 5 := by decide +kernel

private theorem step_30 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 30=stageVector 31 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 30) (stageCode 31)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_30 i)

private theorem check_31 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 31) 111 % 5=
      packedDigit 3 (stageCode 32) i.val % 5 := by decide +kernel

private theorem step_31 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 31=stageVector 32 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 31) (stageCode 32)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_31 i)

private theorem check_32 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 32) 111 % 5=
      packedDigit 3 (stageCode 33) i.val % 5 := by decide +kernel

private theorem step_32 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 32=stageVector 33 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 32) (stageCode 33)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_32 i)

private theorem check_33 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 33) 111 % 5=
      packedDigit 3 (stageCode 34) i.val % 5 := by decide +kernel

private theorem step_33 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 33=stageVector 34 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 33) (stageCode 34)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_33 i)

private theorem check_34 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 34) 111 % 5=
      packedDigit 3 (stageCode 35) i.val % 5 := by decide +kernel

private theorem step_34 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 34=stageVector 35 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 34) (stageCode 35)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_34 i)

private theorem check_35 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 35) 111 % 5=
      packedDigit 3 (stageCode 36) i.val % 5 := by decide +kernel

private theorem step_35 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 35=stageVector 36 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 35) (stageCode 36)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_35 i)

private theorem check_36 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 36) 111 % 5=
      packedDigit 3 (stageCode 37) i.val % 5 := by decide +kernel

private theorem step_36 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 36=stageVector 37 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 36) (stageCode 37)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_36 i)

private theorem check_37 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 37) 111 % 5=
      packedDigit 3 (stageCode 38) i.val % 5 := by decide +kernel

private theorem step_37 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 37=stageVector 38 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 37) (stageCode 38)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_37 i)

private theorem check_38 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 38) 111 % 5=
      packedDigit 3 (stageCode 39) i.val % 5 := by decide +kernel

private theorem step_38 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 38=stageVector 39 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 38) (stageCode 39)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_38 i)

private theorem check_39 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 39) 111 % 5=
      packedDigit 3 (stageCode 40) i.val % 5 := by decide +kernel

private theorem step_39 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 39=stageVector 40 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 39) (stageCode 40)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_39 i)

private theorem check_40 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 40) 111 % 5=
      packedDigit 3 (stageCode 41) i.val % 5 := by decide +kernel

private theorem step_40 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 40=stageVector 41 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 40) (stageCode 41)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_40 i)

private theorem check_41 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 41) 111 % 5=
      packedDigit 3 (stageCode 42) i.val % 5 := by decide +kernel

private theorem step_41 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 41=stageVector 42 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 41) (stageCode 42)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_41 i)

private theorem check_42 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 42) 111 % 5=
      packedDigit 3 (stageCode 43) i.val % 5 := by decide +kernel

private theorem step_42 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 42=stageVector 43 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 42) (stageCode 43)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_42 i)

private theorem check_43 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 43) 111 % 5=
      packedDigit 3 (stageCode 44) i.val % 5 := by decide +kernel

private theorem step_43 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 43=stageVector 44 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 43) (stageCode 44)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_43 i)

private theorem check_44 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 44) 111 % 5=
      packedDigit 3 (stageCode 45) i.val % 5 := by decide +kernel

private theorem step_44 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 44=stageVector 45 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 44) (stageCode 45)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_44 i)

private theorem check_45 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 45) 111 % 5=
      packedDigit 3 (stageCode 46) i.val % 5 := by decide +kernel

private theorem step_45 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 45=stageVector 46 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 45) (stageCode 46)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_45 i)

private theorem check_46 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 46) 111 % 5=
      packedDigit 3 (stageCode 47) i.val % 5 := by decide +kernel

private theorem step_46 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 46=stageVector 47 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 46) (stageCode 47)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_46 i)

private theorem check_47 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 47) 111 % 5=
      packedDigit 3 (stageCode 48) i.val % 5 := by decide +kernel

private theorem step_47 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 47=stageVector 48 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 47) (stageCode 48)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_47 i)

private theorem check_48 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 48) 111 % 5=
      packedDigit 3 (stageCode 49) i.val % 5 := by decide +kernel

private theorem step_48 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 48=stageVector 49 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 48) (stageCode 49)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_48 i)

private theorem check_49 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 49) 111 % 5=
      packedDigit 3 (stageCode 50) i.val % 5 := by decide +kernel

private theorem step_49 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 49=stageVector 50 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 49) (stageCode 50)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_49 i)

private theorem check_50 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 50) 111 % 5=
      packedDigit 3 (stageCode 51) i.val % 5 := by decide +kernel

private theorem step_50 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 50=stageVector 51 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 50) (stageCode 51)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_50 i)

private theorem check_51 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 51) 111 % 5=
      packedDigit 3 (stageCode 52) i.val % 5 := by decide +kernel

private theorem step_51 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 51=stageVector 52 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 51) (stageCode 52)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_51 i)

private theorem check_52 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 52) 111 % 5=
      packedDigit 3 (stageCode 53) i.val % 5 := by decide +kernel

private theorem step_52 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 52=stageVector 53 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 52) (stageCode 53)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_52 i)

private theorem check_53 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 53) 111 % 5=
      packedDigit 3 (stageCode 54) i.val % 5 := by decide +kernel

private theorem step_53 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 53=stageVector 54 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 53) (stageCode 54)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_53 i)

private theorem check_54 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 54) 111 % 5=
      packedDigit 3 (stageCode 55) i.val % 5 := by decide +kernel

private theorem step_54 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 54=stageVector 55 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 54) (stageCode 55)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_54 i)

private theorem check_55 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 55) 111 % 5=
      packedDigit 3 (stageCode 56) i.val % 5 := by decide +kernel

private theorem step_55 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 55=stageVector 56 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 55) (stageCode 56)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_55 i)

private theorem check_56 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 56) 111 % 5=
      packedDigit 3 (stageCode 57) i.val % 5 := by decide +kernel

private theorem step_56 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 56=stageVector 57 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 56) (stageCode 57)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_56 i)

private theorem check_57 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 57) 111 % 5=
      packedDigit 3 (stageCode 58) i.val % 5 := by decide +kernel

private theorem step_57 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 57=stageVector 58 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 57) (stageCode 58)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_57 i)

private theorem check_58 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 58) 111 % 5=
      packedDigit 3 (stageCode 59) i.val % 5 := by decide +kernel

private theorem step_58 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 58=stageVector 59 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 58) (stageCode 59)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_58 i)

private theorem check_59 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 59) 111 % 5=
      packedDigit 3 (stageCode 60) i.val % 5 := by decide +kernel

private theorem step_59 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 59=stageVector 60 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 59) (stageCode 60)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_59 i)

private theorem check_60 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 60) 111 % 5=
      packedDigit 3 (stageCode 61) i.val % 5 := by decide +kernel

private theorem step_60 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 60=stageVector 61 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 60) (stageCode 61)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_60 i)

private theorem check_61 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 61) 111 % 5=
      packedDigit 3 (stageCode 62) i.val % 5 := by decide +kernel

private theorem step_61 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 61=stageVector 62 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 61) (stageCode 62)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_61 i)

private theorem check_62 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 62) 111 % 5=
      packedDigit 3 (stageCode 63) i.val % 5 := by decide +kernel

private theorem step_62 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 62=stageVector 63 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 62) (stageCode 63)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_62 i)

private theorem check_63 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 63) 111 % 5=
      packedDigit 3 (stageCode 64) i.val % 5 := by decide +kernel

private theorem step_63 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 63=stageVector 64 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 63) (stageCode 64)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_63 i)

private theorem check_64 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 64) 111 % 5=
      packedDigit 3 (stageCode 65) i.val % 5 := by decide +kernel

private theorem step_64 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 64=stageVector 65 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 64) (stageCode 65)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_64 i)

private theorem check_65 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 65) 111 % 5=
      packedDigit 3 (stageCode 66) i.val % 5 := by decide +kernel

private theorem step_65 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 65=stageVector 66 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 65) (stageCode 66)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_65 i)

private theorem check_66 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 66) 111 % 5=
      packedDigit 3 (stageCode 67) i.val % 5 := by decide +kernel

private theorem step_66 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 66=stageVector 67 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 66) (stageCode 67)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_66 i)

private theorem check_67 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 67) 111 % 5=
      packedDigit 3 (stageCode 68) i.val % 5 := by decide +kernel

private theorem step_67 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 67=stageVector 68 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 67) (stageCode 68)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_67 i)

private theorem check_68 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 68) 111 % 5=
      packedDigit 3 (stageCode 69) i.val % 5 := by decide +kernel

private theorem step_68 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 68=stageVector 69 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 68) (stageCode 69)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_68 i)

private theorem check_69 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 69) 111 % 5=
      packedDigit 3 (stageCode 70) i.val % 5 := by decide +kernel

private theorem step_69 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 69=stageVector 70 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 69) (stageCode 70)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_69 i)

private theorem check_70 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 70) 111 % 5=
      packedDigit 3 (stageCode 71) i.val % 5 := by decide +kernel

private theorem step_70 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 70=stageVector 71 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 70) (stageCode 71)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_70 i)

private theorem check_71 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 71) 111 % 5=
      packedDigit 3 (stageCode 72) i.val % 5 := by decide +kernel

private theorem step_71 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 71=stageVector 72 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 71) (stageCode 72)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_71 i)

private theorem check_72 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 72) 111 % 5=
      packedDigit 3 (stageCode 73) i.val % 5 := by decide +kernel

private theorem step_72 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 72=stageVector 73 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 72) (stageCode 73)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_72 i)

private theorem check_73 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 73) 111 % 5=
      packedDigit 3 (stageCode 74) i.val % 5 := by decide +kernel

private theorem step_73 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 73=stageVector 74 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 73) (stageCode 74)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_73 i)

private theorem check_74 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 74) 111 % 5=
      packedDigit 3 (stageCode 75) i.val % 5 := by decide +kernel

private theorem step_74 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 74=stageVector 75 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 74) (stageCode 75)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_74 i)

private theorem check_75 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 75) 111 % 5=
      packedDigit 3 (stageCode 76) i.val % 5 := by decide +kernel

private theorem step_75 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 75=stageVector 76 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 75) (stageCode 76)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_75 i)

private theorem check_76 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 76) 111 % 5=
      packedDigit 3 (stageCode 77) i.val % 5 := by decide +kernel

private theorem step_76 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 76=stageVector 77 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 76) (stageCode 77)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_76 i)

private theorem check_77 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 77) 111 % 5=
      packedDigit 3 (stageCode 78) i.val % 5 := by decide +kernel

private theorem step_77 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 77=stageVector 78 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 77) (stageCode 78)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_77 i)

private theorem check_78 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 78) 111 % 5=
      packedDigit 3 (stageCode 79) i.val % 5 := by decide +kernel

private theorem step_78 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 78=stageVector 79 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 78) (stageCode 79)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_78 i)

private theorem check_79 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 79) 111 % 5=
      packedDigit 3 (stageCode 80) i.val % 5 := by decide +kernel

private theorem step_79 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 79=stageVector 80 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 79) (stageCode 80)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_79 i)

private theorem check_80 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 80) 111 % 5=
      packedDigit 3 (stageCode 81) i.val % 5 := by decide +kernel

private theorem step_80 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 80=stageVector 81 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 80) (stageCode 81)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_80 i)

private theorem check_81 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 81) 111 % 5=
      packedDigit 3 (stageCode 82) i.val % 5 := by decide +kernel

private theorem step_81 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 81=stageVector 82 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 81) (stageCode 82)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_81 i)

private theorem check_82 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 82) 111 % 5=
      packedDigit 3 (stageCode 83) i.val % 5 := by decide +kernel

private theorem step_82 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 82=stageVector 83 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 82) (stageCode 83)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_82 i)

private theorem check_83 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 83) 111 % 5=
      packedDigit 3 (stageCode 84) i.val % 5 := by decide +kernel

private theorem step_83 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 83=stageVector 84 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 83) (stageCode 84)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_83 i)

private theorem check_84 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 84) 111 % 5=
      packedDigit 3 (stageCode 85) i.val % 5 := by decide +kernel

private theorem step_84 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 84=stageVector 85 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 84) (stageCode 85)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_84 i)

private theorem check_85 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 85) 111 % 5=
      packedDigit 3 (stageCode 86) i.val % 5 := by decide +kernel

private theorem step_85 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 85=stageVector 86 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 85) (stageCode 86)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_85 i)

private theorem check_86 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 86) 111 % 5=
      packedDigit 3 (stageCode 87) i.val % 5 := by decide +kernel

private theorem step_86 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 86=stageVector 87 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 86) (stageCode 87)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_86 i)

private theorem check_87 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 87) 111 % 5=
      packedDigit 3 (stageCode 88) i.val % 5 := by decide +kernel

private theorem step_87 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 87=stageVector 88 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 87) (stageCode 88)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_87 i)

private theorem check_88 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 88) 111 % 5=
      packedDigit 3 (stageCode 89) i.val % 5 := by decide +kernel

private theorem step_88 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 88=stageVector 89 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 88) (stageCode 89)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_88 i)

private theorem check_89 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 89) 111 % 5=
      packedDigit 3 (stageCode 90) i.val % 5 := by decide +kernel

private theorem step_89 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 89=stageVector 90 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 89) (stageCode 90)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_89 i)

private theorem check_90 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 90) 111 % 5=
      packedDigit 3 (stageCode 91) i.val % 5 := by decide +kernel

private theorem step_90 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 90=stageVector 91 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 90) (stageCode 91)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_90 i)

private theorem check_91 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 91) 111 % 5=
      packedDigit 3 (stageCode 92) i.val % 5 := by decide +kernel

private theorem step_91 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 91=stageVector 92 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 91) (stageCode 92)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_91 i)

private theorem check_92 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 92) 111 % 5=
      packedDigit 3 (stageCode 93) i.val % 5 := by decide +kernel

private theorem step_92 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 92=stageVector 93 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 92) (stageCode 93)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_92 i)

private theorem check_93 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 93) 111 % 5=
      packedDigit 3 (stageCode 94) i.val % 5 := by decide +kernel

private theorem step_93 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 93=stageVector 94 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 93) (stageCode 94)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_93 i)

private theorem check_94 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 94) 111 % 5=
      packedDigit 3 (stageCode 95) i.val % 5 := by decide +kernel

private theorem step_94 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 94=stageVector 95 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 94) (stageCode 95)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_94 i)

private theorem check_95 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 95) 111 % 5=
      packedDigit 3 (stageCode 96) i.val % 5 := by decide +kernel

private theorem step_95 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 95=stageVector 96 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 95) (stageCode 96)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_95 i)

private theorem check_96 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 96) 111 % 5=
      packedDigit 3 (stageCode 97) i.val % 5 := by decide +kernel

private theorem step_96 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 96=stageVector 97 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 96) (stageCode 97)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_96 i)

private theorem check_97 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 97) 111 % 5=
      packedDigit 3 (stageCode 98) i.val % 5 := by decide +kernel

private theorem step_97 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 97=stageVector 98 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 97) (stageCode 98)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_97 i)

private theorem check_98 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 98) 111 % 5=
      packedDigit 3 (stageCode 99) i.val % 5 := by decide +kernel

private theorem step_98 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 98=stageVector 99 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 98) (stageCode 99)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_98 i)

private theorem check_99 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 99) 111 % 5=
      packedDigit 3 (stageCode 100) i.val % 5 := by decide +kernel

private theorem step_99 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 99=stageVector 100 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 99) (stageCode 100)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_99 i)

private theorem check_100 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 100) 111 % 5=
      packedDigit 3 (stageCode 101) i.val % 5 := by decide +kernel

private theorem step_100 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 100=stageVector 101 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 100) (stageCode 101)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_100 i)

private theorem check_101 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 101) 111 % 5=
      packedDigit 3 (stageCode 102) i.val % 5 := by decide +kernel

private theorem step_101 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 101=stageVector 102 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 101) (stageCode 102)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_101 i)

private theorem check_102 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 102) 111 % 5=
      packedDigit 3 (stageCode 103) i.val % 5 := by decide +kernel

private theorem step_102 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 102=stageVector 103 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 102) (stageCode 103)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_102 i)

private theorem check_103 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 103) 111 % 5=
      packedDigit 3 (stageCode 104) i.val % 5 := by decide +kernel

private theorem step_103 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 103=stageVector 104 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 103) (stageCode 104)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_103 i)

private theorem check_104 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 104) 111 % 5=
      packedDigit 3 (stageCode 105) i.val % 5 := by decide +kernel

private theorem step_104 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 104=stageVector 105 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 104) (stageCode 105)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_104 i)

private theorem check_105 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 105) 111 % 5=
      packedDigit 3 (stageCode 106) i.val % 5 := by decide +kernel

private theorem step_105 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 105=stageVector 106 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 105) (stageCode 106)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_105 i)

private theorem check_106 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 106) 111 % 5=
      packedDigit 3 (stageCode 107) i.val % 5 := by decide +kernel

private theorem step_106 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 106=stageVector 107 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 106) (stageCode 107)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_106 i)

private theorem check_107 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 107) 111 % 5=
      packedDigit 3 (stageCode 108) i.val % 5 := by decide +kernel

private theorem step_107 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 107=stageVector 108 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 107) (stageCode 108)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_107 i)

private theorem check_108 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 108) 111 % 5=
      packedDigit 3 (stageCode 109) i.val % 5 := by decide +kernel

private theorem step_108 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 108=stageVector 109 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 108) (stageCode 109)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_108 i)

private theorem check_109 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 109) 111 % 5=
      packedDigit 3 (stageCode 110) i.val % 5 := by decide +kernel

private theorem step_109 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 109=stageVector 110 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 109) (stageCode 110)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_109 i)

private theorem check_110 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 110) 111 % 5=
      packedDigit 3 (stageCode 111) i.val % 5 := by decide +kernel

private theorem step_110 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 110=stageVector 111 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 110) (stageCode 111)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_110 i)

private theorem check_111 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 111) 111 % 5=
      packedDigit 3 (stageCode 112) i.val % 5 := by decide +kernel

private theorem step_111 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 111=stageVector 112 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 111) (stageCode 112)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_111 i)

private theorem check_112 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 112) 111 % 5=
      packedDigit 3 (stageCode 113) i.val % 5 := by decide +kernel

private theorem step_112 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 112=stageVector 113 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 112) (stageCode 113)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_112 i)

private theorem check_113 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 113) 111 % 5=
      packedDigit 3 (stageCode 114) i.val % 5 := by decide +kernel

private theorem step_113 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 113=stageVector 114 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 113) (stageCode 114)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_113 i)

private theorem check_114 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 114) 111 % 5=
      packedDigit 3 (stageCode 115) i.val % 5 := by decide +kernel

private theorem step_114 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 114=stageVector 115 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 114) (stageCode 115)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_114 i)

private theorem check_115 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 115) 111 % 5=
      packedDigit 3 (stageCode 116) i.val % 5 := by decide +kernel

private theorem step_115 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 115=stageVector 116 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 115) (stageCode 116)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_115 i)

private theorem check_116 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 116) 111 % 5=
      packedDigit 3 (stageCode 117) i.val % 5 := by decide +kernel

private theorem step_116 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 116=stageVector 117 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 116) (stageCode 117)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_116 i)

private theorem check_117 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 117) 111 % 5=
      packedDigit 3 (stageCode 118) i.val % 5 := by decide +kernel

private theorem step_117 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 117=stageVector 118 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 117) (stageCode 118)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_117 i)

private theorem check_118 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 118) 111 % 5=
      packedDigit 3 (stageCode 119) i.val % 5 := by decide +kernel

private theorem step_118 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 118=stageVector 119 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 118) (stageCode 119)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_118 i)

private theorem check_119 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 119) 111 % 5=
      packedDigit 3 (stageCode 120) i.val % 5 := by decide +kernel

private theorem step_119 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 119=stageVector 120 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 119) (stageCode 120)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_119 i)

private theorem check_120 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 120) 111 % 5=
      packedDigit 3 (stageCode 121) i.val % 5 := by decide +kernel

private theorem step_120 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 120=stageVector 121 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 120) (stageCode 121)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_120 i)

private theorem check_121 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 121) 111 % 5=
      packedDigit 3 (stageCode 122) i.val % 5 := by decide +kernel

private theorem step_121 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 121=stageVector 122 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 121) (stageCode 122)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_121 i)

private theorem check_122 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 122) 111 % 5=
      packedDigit 3 (stageCode 123) i.val % 5 := by decide +kernel

private theorem step_122 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 122=stageVector 123 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 122) (stageCode 123)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_122 i)

private theorem check_123 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 123) 111 % 5=
      packedDigit 3 (stageCode 124) i.val % 5 := by decide +kernel

private theorem step_123 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 123=stageVector 124 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 123) (stageCode 124)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_123 i)

private theorem check_124 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 124) 111 % 5=
      packedDigit 3 (stageCode 125) i.val % 5 := by decide +kernel

private theorem step_124 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 124=stageVector 125 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 124) (stageCode 125)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_124 i)

private theorem check_125 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 125) 111 % 5=
      packedDigit 3 (stageCode 126) i.val % 5 := by decide +kernel

private theorem step_125 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 125=stageVector 126 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 125) (stageCode 126)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_125 i)

private theorem check_126 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 126) 111 % 5=
      packedDigit 3 (stageCode 127) i.val % 5 := by decide +kernel

private theorem step_126 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 126=stageVector 127 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 126) (stageCode 127)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_126 i)

private theorem check_127 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 127) 111 % 5=
      packedDigit 3 (stageCode 128) i.val % 5 := by decide +kernel

private theorem step_127 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 127=stageVector 128 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 127) (stageCode 128)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_127 i)

private theorem check_128 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 128) 111 % 5=
      packedDigit 3 (stageCode 129) i.val % 5 := by decide +kernel

private theorem step_128 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 128=stageVector 129 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 128) (stageCode 129)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_128 i)

private theorem check_129 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 129) 111 % 5=
      packedDigit 3 (stageCode 130) i.val % 5 := by decide +kernel

private theorem step_129 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 129=stageVector 130 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 129) (stageCode 130)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_129 i)

private theorem check_130 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 130) 111 % 5=
      packedDigit 3 (stageCode 131) i.val % 5 := by decide +kernel

private theorem step_130 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 130=stageVector 131 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 130) (stageCode 131)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_130 i)

private theorem check_131 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 131) 111 % 5=
      packedDigit 3 (stageCode 132) i.val % 5 := by decide +kernel

private theorem step_131 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 131=stageVector 132 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 131) (stageCode 132)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_131 i)

private theorem check_132 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 132) 111 % 5=
      packedDigit 3 (stageCode 133) i.val % 5 := by decide +kernel

private theorem step_132 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 132=stageVector 133 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 132) (stageCode 133)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_132 i)

private theorem check_133 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 133) 111 % 5=
      packedDigit 3 (stageCode 134) i.val % 5 := by decide +kernel

private theorem step_133 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 133=stageVector 134 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 133) (stageCode 134)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_133 i)

private theorem check_134 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 134) 111 % 5=
      packedDigit 3 (stageCode 135) i.val % 5 := by decide +kernel

private theorem step_134 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 134=stageVector 135 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 134) (stageCode 135)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_134 i)

private theorem check_135 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 135) 111 % 5=
      packedDigit 3 (stageCode 136) i.val % 5 := by decide +kernel

private theorem step_135 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 135=stageVector 136 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 135) (stageCode 136)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_135 i)

private theorem check_136 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 136) 111 % 5=
      packedDigit 3 (stageCode 137) i.val % 5 := by decide +kernel

private theorem step_136 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 136=stageVector 137 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 136) (stageCode 137)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_136 i)

private theorem check_137 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 137) 111 % 5=
      packedDigit 3 (stageCode 138) i.val % 5 := by decide +kernel

private theorem step_137 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 137=stageVector 138 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 137) (stageCode 138)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_137 i)

private theorem check_138 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 138) 111 % 5=
      packedDigit 3 (stageCode 139) i.val % 5 := by decide +kernel

private theorem step_138 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 138=stageVector 139 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 138) (stageCode 139)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_138 i)

private theorem check_139 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 139) 111 % 5=
      packedDigit 3 (stageCode 140) i.val % 5 := by decide +kernel

private theorem step_139 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 139=stageVector 140 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 139) (stageCode 140)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_139 i)

private theorem check_140 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 140) 111 % 5=
      packedDigit 3 (stageCode 141) i.val % 5 := by decide +kernel

private theorem step_140 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 140=stageVector 141 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 140) (stageCode 141)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_140 i)

private theorem check_141 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 141) 111 % 5=
      packedDigit 3 (stageCode 142) i.val % 5 := by decide +kernel

private theorem step_141 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 141=stageVector 142 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 141) (stageCode 142)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_141 i)

private theorem check_142 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 142) 111 % 5=
      packedDigit 3 (stageCode 143) i.val % 5 := by decide +kernel

private theorem step_142 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 142=stageVector 143 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 142) (stageCode 143)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_142 i)

private theorem check_143 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 143) 111 % 5=
      packedDigit 3 (stageCode 144) i.val % 5 := by decide +kernel

private theorem step_143 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 143=stageVector 144 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 143) (stageCode 144)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_143 i)

private theorem check_144 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 144) 111 % 5=
      packedDigit 3 (stageCode 145) i.val % 5 := by decide +kernel

private theorem step_144 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 144=stageVector 145 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 144) (stageCode 145)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_144 i)

private theorem check_145 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 145) 111 % 5=
      packedDigit 3 (stageCode 146) i.val % 5 := by decide +kernel

private theorem step_145 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 145=stageVector 146 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 145) (stageCode 146)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_145 i)

private theorem check_146 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 146) 111 % 5=
      packedDigit 3 (stageCode 147) i.val % 5 := by decide +kernel

private theorem step_146 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 146=stageVector 147 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 146) (stageCode 147)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_146 i)

private theorem check_147 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 147) 111 % 5=
      packedDigit 3 (stageCode 148) i.val % 5 := by decide +kernel

private theorem step_147 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 147=stageVector 148 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 147) (stageCode 148)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_147 i)

private theorem check_148 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 148) 111 % 5=
      packedDigit 3 (stageCode 149) i.val % 5 := by decide +kernel

private theorem step_148 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 148=stageVector 149 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 148) (stageCode 149)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_148 i)

private theorem check_149 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 149) 111 % 5=
      packedDigit 3 (stageCode 150) i.val % 5 := by decide +kernel

private theorem step_149 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 149=stageVector 150 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 149) (stageCode 150)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_149 i)

private theorem check_150 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 150) 111 % 5=
      packedDigit 3 (stageCode 151) i.val % 5 := by decide +kernel

private theorem step_150 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 150=stageVector 151 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 150) (stageCode 151)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_150 i)

private theorem check_151 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 151) 111 % 5=
      packedDigit 3 (stageCode 152) i.val % 5 := by decide +kernel

private theorem step_151 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 151=stageVector 152 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 151) (stageCode 152)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_151 i)

private theorem check_152 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 152) 111 % 5=
      packedDigit 3 (stageCode 153) i.val % 5 := by decide +kernel

private theorem step_152 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 152=stageVector 153 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 152) (stageCode 153)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_152 i)

private theorem check_153 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 153) 111 % 5=
      packedDigit 3 (stageCode 154) i.val % 5 := by decide +kernel

private theorem step_153 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 153=stageVector 154 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 153) (stageCode 154)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_153 i)

private theorem check_154 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 154) 111 % 5=
      packedDigit 3 (stageCode 155) i.val % 5 := by decide +kernel

private theorem step_154 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 154=stageVector 155 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 154) (stageCode 155)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_154 i)

private theorem check_155 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 155) 111 % 5=
      packedDigit 3 (stageCode 156) i.val % 5 := by decide +kernel

private theorem step_155 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 155=stageVector 156 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 155) (stageCode 156)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_155 i)

private theorem check_156 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 156) 111 % 5=
      packedDigit 3 (stageCode 157) i.val % 5 := by decide +kernel

private theorem step_156 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 156=stageVector 157 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 156) (stageCode 157)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_156 i)

private theorem check_157 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 157) 111 % 5=
      packedDigit 3 (stageCode 158) i.val % 5 := by decide +kernel

private theorem step_157 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 157=stageVector 158 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 157) (stageCode 158)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_157 i)

private theorem check_158 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 158) 111 % 5=
      packedDigit 3 (stageCode 159) i.val % 5 := by decide +kernel

private theorem step_158 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 158=stageVector 159 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 158) (stageCode 159)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_158 i)

private theorem check_159 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 159) 111 % 5=
      packedDigit 3 (stageCode 160) i.val % 5 := by decide +kernel

private theorem step_159 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 159=stageVector 160 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 159) (stageCode 160)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_159 i)

private theorem check_160 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 160) 111 % 5=
      packedDigit 3 (stageCode 161) i.val % 5 := by decide +kernel

private theorem step_160 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 160=stageVector 161 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 160) (stageCode 161)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_160 i)

private theorem check_161 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 161) 111 % 5=
      packedDigit 3 (stageCode 162) i.val % 5 := by decide +kernel

private theorem step_161 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 161=stageVector 162 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 161) (stageCode 162)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_161 i)

private theorem check_162 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 162) 111 % 5=
      packedDigit 3 (stageCode 163) i.val % 5 := by decide +kernel

private theorem step_162 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 162=stageVector 163 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 162) (stageCode 163)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_162 i)

private theorem check_163 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 163) 111 % 5=
      packedDigit 3 (stageCode 164) i.val % 5 := by decide +kernel

private theorem step_163 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 163=stageVector 164 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 163) (stageCode 164)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_163 i)

private theorem check_164 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 164) 111 % 5=
      packedDigit 3 (stageCode 165) i.val % 5 := by decide +kernel

private theorem step_164 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 164=stageVector 165 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 164) (stageCode 165)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_164 i)

private theorem check_165 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 165) 111 % 5=
      packedDigit 3 (stageCode 166) i.val % 5 := by decide +kernel

private theorem step_165 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 165=stageVector 166 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 165) (stageCode 166)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_165 i)

private theorem check_166 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 166) 111 % 5=
      packedDigit 3 (stageCode 167) i.val % 5 := by decide +kernel

private theorem step_166 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 166=stageVector 167 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 166) (stageCode 167)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_166 i)

private theorem check_167 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 167) 111 % 5=
      packedDigit 3 (stageCode 168) i.val % 5 := by decide +kernel

private theorem step_167 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 167=stageVector 168 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 167) (stageCode 168)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_167 i)

private theorem check_168 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 168) 111 % 5=
      packedDigit 3 (stageCode 169) i.val % 5 := by decide +kernel

private theorem step_168 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 168=stageVector 169 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 168) (stageCode 169)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_168 i)

private theorem check_169 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 169) 111 % 5=
      packedDigit 3 (stageCode 170) i.val % 5 := by decide +kernel

private theorem step_169 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 169=stageVector 170 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 169) (stageCode 170)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_169 i)

private theorem check_170 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 170) 111 % 5=
      packedDigit 3 (stageCode 171) i.val % 5 := by decide +kernel

private theorem step_170 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 170=stageVector 171 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 170) (stageCode 171)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_170 i)

private theorem check_171 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 171) 111 % 5=
      packedDigit 3 (stageCode 172) i.val % 5 := by decide +kernel

private theorem step_171 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 171=stageVector 172 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 171) (stageCode 172)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_171 i)

private theorem check_172 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 172) 111 % 5=
      packedDigit 3 (stageCode 173) i.val % 5 := by decide +kernel

private theorem step_172 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 172=stageVector 173 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 172) (stageCode 173)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_172 i)

private theorem check_173 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 173) 111 % 5=
      packedDigit 3 (stageCode 174) i.val % 5 := by decide +kernel

private theorem step_173 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 173=stageVector 174 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 173) (stageCode 174)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_173 i)

private theorem check_174 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 174) 111 % 5=
      packedDigit 3 (stageCode 175) i.val % 5 := by decide +kernel

private theorem step_174 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 174=stageVector 175 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 174) (stageCode 175)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_174 i)

private theorem check_175 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 175) 111 % 5=
      packedDigit 3 (stageCode 176) i.val % 5 := by decide +kernel

private theorem step_175 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 175=stageVector 176 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 175) (stageCode 176)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_175 i)

private theorem check_176 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 176) 111 % 5=
      packedDigit 3 (stageCode 177) i.val % 5 := by decide +kernel

private theorem step_176 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 176=stageVector 177 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 176) (stageCode 177)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_176 i)

private theorem check_177 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 177) 111 % 5=
      packedDigit 3 (stageCode 178) i.val % 5 := by decide +kernel

private theorem step_177 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 177=stageVector 178 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 177) (stageCode 178)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_177 i)

private theorem check_178 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 178) 111 % 5=
      packedDigit 3 (stageCode 179) i.val % 5 := by decide +kernel

private theorem step_178 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 178=stageVector 179 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 178) (stageCode 179)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_178 i)

private theorem check_179 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 179) 111 % 5=
      packedDigit 3 (stageCode 180) i.val % 5 := by decide +kernel

private theorem step_179 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 179=stageVector 180 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 179) (stageCode 180)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_179 i)

private theorem check_180 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 180) 111 % 5=
      packedDigit 3 (stageCode 181) i.val % 5 := by decide +kernel

private theorem step_180 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 180=stageVector 181 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 180) (stageCode 181)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_180 i)

private theorem check_181 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 181) 111 % 5=
      packedDigit 3 (stageCode 182) i.val % 5 := by decide +kernel

private theorem step_181 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 181=stageVector 182 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 181) (stageCode 182)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_181 i)

private theorem check_182 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 182) 111 % 5=
      packedDigit 3 (stageCode 183) i.val % 5 := by decide +kernel

private theorem step_182 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 182=stageVector 183 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 182) (stageCode 183)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_182 i)

private theorem check_183 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 183) 111 % 5=
      packedDigit 3 (stageCode 184) i.val % 5 := by decide +kernel

private theorem step_183 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 183=stageVector 184 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 183) (stageCode 184)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_183 i)

private theorem check_184 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 184) 111 % 5=
      packedDigit 3 (stageCode 185) i.val % 5 := by decide +kernel

private theorem step_184 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 184=stageVector 185 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 184) (stageCode 185)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_184 i)

private theorem check_185 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 185) 111 % 5=
      packedDigit 3 (stageCode 186) i.val % 5 := by decide +kernel

private theorem step_185 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 185=stageVector 186 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 185) (stageCode 186)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_185 i)

private theorem check_186 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 186) 111 % 5=
      packedDigit 3 (stageCode 187) i.val % 5 := by decide +kernel

private theorem step_186 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 186=stageVector 187 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 186) (stageCode 187)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_186 i)

private theorem check_187 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 187) 111 % 5=
      packedDigit 3 (stageCode 188) i.val % 5 := by decide +kernel

private theorem step_187 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 187=stageVector 188 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 187) (stageCode 188)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_187 i)

private theorem check_188 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 188) 111 % 5=
      packedDigit 3 (stageCode 189) i.val % 5 := by decide +kernel

private theorem step_188 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 188=stageVector 189 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 188) (stageCode 189)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_188 i)

private theorem check_189 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 189) 111 % 5=
      packedDigit 3 (stageCode 190) i.val % 5 := by decide +kernel

private theorem step_189 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 189=stageVector 190 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 189) (stageCode 190)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_189 i)

private theorem check_190 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 190) 111 % 5=
      packedDigit 3 (stageCode 191) i.val % 5 := by decide +kernel

private theorem step_190 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 190=stageVector 191 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 190) (stageCode 191)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_190 i)

private theorem check_191 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 191) 111 % 5=
      packedDigit 3 (stageCode 192) i.val % 5 := by decide +kernel

private theorem step_191 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 191=stageVector 192 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 191) (stageCode 192)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_191 i)

private theorem check_192 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 192) 111 % 5=
      packedDigit 3 (stageCode 193) i.val % 5 := by decide +kernel

private theorem step_192 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 192=stageVector 193 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 192) (stageCode 193)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_192 i)

private theorem check_193 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 193) 111 % 5=
      packedDigit 3 (stageCode 194) i.val % 5 := by decide +kernel

private theorem step_193 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 193=stageVector 194 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 193) (stageCode 194)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_193 i)

private theorem check_194 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 194) 111 % 5=
      packedDigit 3 (stageCode 195) i.val % 5 := by decide +kernel

private theorem step_194 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 194=stageVector 195 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 194) (stageCode 195)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_194 i)

private theorem check_195 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 195) 111 % 5=
      packedDigit 3 (stageCode 196) i.val % 5 := by decide +kernel

private theorem step_195 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 195=stageVector 196 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 195) (stageCode 196)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_195 i)

private theorem check_196 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 196) 111 % 5=
      packedDigit 3 (stageCode 197) i.val % 5 := by decide +kernel

private theorem step_196 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 196=stageVector 197 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 196) (stageCode 197)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_196 i)

private theorem check_197 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 197) 111 % 5=
      packedDigit 3 (stageCode 198) i.val % 5 := by decide +kernel

private theorem step_197 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 197=stageVector 198 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 197) (stageCode 198)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_197 i)

private theorem check_198 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 198) 111 % 5=
      packedDigit 3 (stageCode 199) i.val % 5 := by decide +kernel

private theorem step_198 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 198=stageVector 199 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 198) (stageCode 199)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_198 i)

private theorem check_199 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 199) 111 % 5=
      packedDigit 3 (stageCode 200) i.val % 5 := by decide +kernel

private theorem step_199 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 199=stageVector 200 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 199) (stageCode 200)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_199 i)

private theorem check_200 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 200) 111 % 5=
      packedDigit 3 (stageCode 201) i.val % 5 := by decide +kernel

private theorem step_200 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 200=stageVector 201 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 200) (stageCode 201)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_200 i)

private theorem check_201 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 201) 111 % 5=
      packedDigit 3 (stageCode 202) i.val % 5 := by decide +kernel

private theorem step_201 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 201=stageVector 202 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 201) (stageCode 202)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_201 i)

private theorem check_202 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 202) 111 % 5=
      packedDigit 3 (stageCode 203) i.val % 5 := by decide +kernel

private theorem step_202 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 202=stageVector 203 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 202) (stageCode 203)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_202 i)

private theorem check_203 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 203) 111 % 5=
      packedDigit 3 (stageCode 204) i.val % 5 := by decide +kernel

private theorem step_203 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 203=stageVector 204 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 203) (stageCode 204)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_203 i)

private theorem check_204 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 204) 111 % 5=
      packedDigit 3 (stageCode 205) i.val % 5 := by decide +kernel

private theorem step_204 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 204=stageVector 205 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 204) (stageCode 205)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_204 i)

private theorem check_205 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 205) 111 % 5=
      packedDigit 3 (stageCode 206) i.val % 5 := by decide +kernel

private theorem step_205 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 205=stageVector 206 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 205) (stageCode 206)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_205 i)

private theorem check_206 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 206) 111 % 5=
      packedDigit 3 (stageCode 207) i.val % 5 := by decide +kernel

private theorem step_206 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 206=stageVector 207 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 206) (stageCode 207)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_206 i)

private theorem check_207 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 207) 111 % 5=
      packedDigit 3 (stageCode 208) i.val % 5 := by decide +kernel

private theorem step_207 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 207=stageVector 208 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 207) (stageCode 208)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_207 i)

private theorem check_208 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 208) 111 % 5=
      packedDigit 3 (stageCode 209) i.val % 5 := by decide +kernel

private theorem step_208 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 208=stageVector 209 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 208) (stageCode 209)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_208 i)

private theorem check_209 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 209) 111 % 5=
      packedDigit 3 (stageCode 210) i.val % 5 := by decide +kernel

private theorem step_209 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 209=stageVector 210 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 209) (stageCode 210)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_209 i)

private theorem check_210 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 210) 111 % 5=
      packedDigit 3 (stageCode 211) i.val % 5 := by decide +kernel

private theorem step_210 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 210=stageVector 211 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 210) (stageCode 211)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_210 i)

private theorem check_211 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 211) 111 % 5=
      packedDigit 3 (stageCode 212) i.val % 5 := by decide +kernel

private theorem step_211 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 211=stageVector 212 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 211) (stageCode 212)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_211 i)

private theorem check_212 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 212) 111 % 5=
      packedDigit 3 (stageCode 213) i.val % 5 := by decide +kernel

private theorem step_212 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 212=stageVector 213 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 212) (stageCode 213)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_212 i)

private theorem check_213 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 213) 111 % 5=
      packedDigit 3 (stageCode 214) i.val % 5 := by decide +kernel

private theorem step_213 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 213=stageVector 214 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 213) (stageCode 214)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_213 i)

private theorem check_214 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 214) 111 % 5=
      packedDigit 3 (stageCode 215) i.val % 5 := by decide +kernel

private theorem step_214 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 214=stageVector 215 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 214) (stageCode 215)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_214 i)

private theorem check_215 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 215) 111 % 5=
      packedDigit 3 (stageCode 216) i.val % 5 := by decide +kernel

private theorem step_215 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 215=stageVector 216 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 215) (stageCode 216)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_215 i)

private theorem check_216 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 216) 111 % 5=
      packedDigit 3 (stageCode 217) i.val % 5 := by decide +kernel

private theorem step_216 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 216=stageVector 217 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 216) (stageCode 217)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_216 i)

private theorem check_217 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 217) 111 % 5=
      packedDigit 3 (stageCode 218) i.val % 5 := by decide +kernel

private theorem step_217 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 217=stageVector 218 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 217) (stageCode 218)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_217 i)

private theorem check_218 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 218) 111 % 5=
      packedDigit 3 (stageCode 219) i.val % 5 := by decide +kernel

private theorem step_218 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 218=stageVector 219 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 218) (stageCode 219)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_218 i)

private theorem check_219 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 219) 111 % 5=
      packedDigit 3 (stageCode 220) i.val % 5 := by decide +kernel

private theorem step_219 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 219=stageVector 220 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 219) (stageCode 220)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_219 i)

private theorem check_220 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 220) 111 % 5=
      packedDigit 3 (stageCode 221) i.val % 5 := by decide +kernel

private theorem step_220 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 220=stageVector 221 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 220) (stageCode 221)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_220 i)

private theorem check_221 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 221) 111 % 5=
      packedDigit 3 (stageCode 222) i.val % 5 := by decide +kernel

private theorem step_221 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 221=stageVector 222 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 221) (stageCode 222)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_221 i)

private theorem check_222 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 222) 111 % 5=
      packedDigit 3 (stageCode 223) i.val % 5 := by decide +kernel

private theorem step_222 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 222=stageVector 223 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 222) (stageCode 223)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_222 i)

private theorem check_223 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 223) 111 % 5=
      packedDigit 3 (stageCode 224) i.val % 5 := by decide +kernel

private theorem step_223 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 223=stageVector 224 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 223) (stageCode 224)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_223 i)

private theorem check_224 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 224) 111 % 5=
      packedDigit 3 (stageCode 225) i.val % 5 := by decide +kernel

private theorem step_224 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 224=stageVector 225 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 224) (stageCode 225)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_224 i)

private theorem check_225 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 225) 111 % 5=
      packedDigit 3 (stageCode 226) i.val % 5 := by decide +kernel

private theorem step_225 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 225=stageVector 226 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 225) (stageCode 226)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_225 i)

private theorem check_226 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 226) 111 % 5=
      packedDigit 3 (stageCode 227) i.val % 5 := by decide +kernel

private theorem step_226 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 226=stageVector 227 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 226) (stageCode 227)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_226 i)

private theorem check_227 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 227) 111 % 5=
      packedDigit 3 (stageCode 228) i.val % 5 := by decide +kernel

private theorem step_227 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 227=stageVector 228 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 227) (stageCode 228)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_227 i)

private theorem check_228 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 228) 111 % 5=
      packedDigit 3 (stageCode 229) i.val % 5 := by decide +kernel

private theorem step_228 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 228=stageVector 229 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 228) (stageCode 229)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_228 i)

private theorem check_229 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 229) 111 % 5=
      packedDigit 3 (stageCode 230) i.val % 5 := by decide +kernel

private theorem step_229 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 229=stageVector 230 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 229) (stageCode 230)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_229 i)

private theorem check_230 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 230) 111 % 5=
      packedDigit 3 (stageCode 231) i.val % 5 := by decide +kernel

private theorem step_230 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 230=stageVector 231 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 230) (stageCode 231)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_230 i)

private theorem check_231 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 231) 111 % 5=
      packedDigit 3 (stageCode 232) i.val % 5 := by decide +kernel

private theorem step_231 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 231=stageVector 232 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 231) (stageCode 232)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_231 i)

private theorem check_232 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 232) 111 % 5=
      packedDigit 3 (stageCode 233) i.val % 5 := by decide +kernel

private theorem step_232 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 232=stageVector 233 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 232) (stageCode 233)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_232 i)

private theorem check_233 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 233) 111 % 5=
      packedDigit 3 (stageCode 234) i.val % 5 := by decide +kernel

private theorem step_233 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 233=stageVector 234 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 233) (stageCode 234)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_233 i)

private theorem check_234 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 234) 111 % 5=
      packedDigit 3 (stageCode 235) i.val % 5 := by decide +kernel

private theorem step_234 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 234=stageVector 235 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 234) (stageCode 235)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_234 i)

private theorem check_235 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 235) 111 % 5=
      packedDigit 3 (stageCode 236) i.val % 5 := by decide +kernel

private theorem step_235 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 235=stageVector 236 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 235) (stageCode 236)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_235 i)

private theorem check_236 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 236) 111 % 5=
      packedDigit 3 (stageCode 237) i.val % 5 := by decide +kernel

private theorem step_236 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 236=stageVector 237 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 236) (stageCode 237)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_236 i)

private theorem check_237 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 237) 111 % 5=
      packedDigit 3 (stageCode 238) i.val % 5 := by decide +kernel

private theorem step_237 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 237=stageVector 238 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 237) (stageCode 238)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_237 i)

private theorem check_238 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 238) 111 % 5=
      packedDigit 3 (stageCode 239) i.val % 5 := by decide +kernel

private theorem step_238 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 238=stageVector 239 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 238) (stageCode 239)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_238 i)

private theorem check_239 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 239) 111 % 5=
      packedDigit 3 (stageCode 240) i.val % 5 := by decide +kernel

private theorem step_239 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 239=stageVector 240 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 239) (stageCode 240)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_239 i)

private theorem check_240 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 240) 111 % 5=
      packedDigit 3 (stageCode 241) i.val % 5 := by decide +kernel

private theorem step_240 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 240=stageVector 241 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 240) (stageCode 241)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_240 i)

private theorem check_241 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 241) 111 % 5=
      packedDigit 3 (stageCode 242) i.val % 5 := by decide +kernel

private theorem step_241 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 241=stageVector 242 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 241) (stageCode 242)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_241 i)

private theorem check_242 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 242) 111 % 5=
      packedDigit 3 (stageCode 243) i.val % 5 := by decide +kernel

private theorem step_242 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 242=stageVector 243 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 242) (stageCode 243)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_242 i)

private theorem check_243 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 243) 111 % 5=
      packedDigit 3 (stageCode 244) i.val % 5 := by decide +kernel

private theorem step_243 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 243=stageVector 244 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 243) (stageCode 244)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_243 i)

private theorem check_244 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 244) 111 % 5=
      packedDigit 3 (stageCode 245) i.val % 5 := by decide +kernel

private theorem step_244 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 244=stageVector 245 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 244) (stageCode 245)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_244 i)

private theorem check_245 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 245) 111 % 5=
      packedDigit 3 (stageCode 246) i.val % 5 := by decide +kernel

private theorem step_245 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 245=stageVector 246 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 245) (stageCode 246)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_245 i)

private theorem check_246 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 246) 111 % 5=
      packedDigit 3 (stageCode 247) i.val % 5 := by decide +kernel

private theorem step_246 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 246=stageVector 247 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 246) (stageCode 247)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_246 i)

private theorem check_247 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 247) 111 % 5=
      packedDigit 3 (stageCode 248) i.val % 5 := by decide +kernel

private theorem step_247 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 247=stageVector 248 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 247) (stageCode 248)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_247 i)

private theorem check_248 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 248) 111 % 5=
      packedDigit 3 (stageCode 249) i.val % 5 := by decide +kernel

private theorem step_248 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 248=stageVector 249 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 248) (stageCode 249)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_248 i)

private theorem check_249 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 249) 111 % 5=
      packedDigit 3 (stageCode 250) i.val % 5 := by decide +kernel

private theorem step_249 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 249=stageVector 250 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 249) (stageCode 250)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_249 i)

private theorem check_250 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 250) 111 % 5=
      packedDigit 3 (stageCode 251) i.val % 5 := by decide +kernel

private theorem step_250 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 250=stageVector 251 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 250) (stageCode 251)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_250 i)

private theorem check_251 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 251) 111 % 5=
      packedDigit 3 (stageCode 252) i.val % 5 := by decide +kernel

private theorem step_251 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 251=stageVector 252 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 251) (stageCode 252)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_251 i)

private theorem check_252 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 252) 111 % 5=
      packedDigit 3 (stageCode 253) i.val % 5 := by decide +kernel

private theorem step_252 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 252=stageVector 253 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 252) (stageCode 253)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_252 i)

private theorem check_253 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 253) 111 % 5=
      packedDigit 3 (stageCode 254) i.val % 5 := by decide +kernel

private theorem step_253 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 253=stageVector 254 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 253) (stageCode 254)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_253 i)

private theorem check_254 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 254) 111 % 5=
      packedDigit 3 (stageCode 255) i.val % 5 := by decide +kernel

private theorem step_254 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 254=stageVector 255 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 254) (stageCode 255)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_254 i)

private theorem check_255 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 255) 111 % 5=
      packedDigit 3 (stageCode 256) i.val % 5 := by decide +kernel

private theorem step_255 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 255=stageVector 256 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 255) (stageCode 256)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_255 i)

private theorem check_256 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 256) 111 % 5=
      packedDigit 3 (stageCode 257) i.val % 5 := by decide +kernel

private theorem step_256 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 256=stageVector 257 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 256) (stageCode 257)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_256 i)

private theorem check_257 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 257) 111 % 5=
      packedDigit 3 (stageCode 258) i.val % 5 := by decide +kernel

private theorem step_257 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 257=stageVector 258 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 257) (stageCode 258)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_257 i)

private theorem check_258 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 258) 111 % 5=
      packedDigit 3 (stageCode 259) i.val % 5 := by decide +kernel

private theorem step_258 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 258=stageVector 259 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 258) (stageCode 259)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_258 i)

private theorem check_259 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 259) 111 % 5=
      packedDigit 3 (stageCode 260) i.val % 5 := by decide +kernel

private theorem step_259 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 259=stageVector 260 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 259) (stageCode 260)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_259 i)

private theorem check_260 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 260) 111 % 5=
      packedDigit 3 (stageCode 261) i.val % 5 := by decide +kernel

private theorem step_260 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 260=stageVector 261 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 260) (stageCode 261)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_260 i)

private theorem check_261 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 261) 111 % 5=
      packedDigit 3 (stageCode 262) i.val % 5 := by decide +kernel

private theorem step_261 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 261=stageVector 262 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 261) (stageCode 262)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_261 i)

private theorem check_262 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 262) 111 % 5=
      packedDigit 3 (stageCode 263) i.val % 5 := by decide +kernel

private theorem step_262 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 262=stageVector 263 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 262) (stageCode 263)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_262 i)

private theorem check_263 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 263) 111 % 5=
      packedDigit 3 (stageCode 264) i.val % 5 := by decide +kernel

private theorem step_263 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 263=stageVector 264 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 263) (stageCode 264)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_263 i)

private theorem check_264 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 264) 111 % 5=
      packedDigit 3 (stageCode 265) i.val % 5 := by decide +kernel

private theorem step_264 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 264=stageVector 265 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 264) (stageCode 265)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_264 i)

private theorem check_265 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 265) 111 % 5=
      packedDigit 3 (stageCode 266) i.val % 5 := by decide +kernel

private theorem step_265 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 265=stageVector 266 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 265) (stageCode 266)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_265 i)

private theorem check_266 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 266) 111 % 5=
      packedDigit 3 (stageCode 267) i.val % 5 := by decide +kernel

private theorem step_266 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 266=stageVector 267 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 266) (stageCode 267)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_266 i)

private theorem check_267 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 267) 111 % 5=
      packedDigit 3 (stageCode 268) i.val % 5 := by decide +kernel

private theorem step_267 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 267=stageVector 268 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 267) (stageCode 268)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_267 i)

private theorem check_268 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 268) 111 % 5=
      packedDigit 3 (stageCode 269) i.val % 5 := by decide +kernel

private theorem step_268 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 268=stageVector 269 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 268) (stageCode 269)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_268 i)

private theorem check_269 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 269) 111 % 5=
      packedDigit 3 (stageCode 270) i.val % 5 := by decide +kernel

private theorem step_269 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 269=stageVector 270 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 269) (stageCode 270)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_269 i)

private theorem check_270 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 270) 111 % 5=
      packedDigit 3 (stageCode 271) i.val % 5 := by decide +kernel

private theorem step_270 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 270=stageVector 271 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 270) (stageCode 271)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_270 i)

private theorem check_271 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 271) 111 % 5=
      packedDigit 3 (stageCode 272) i.val % 5 := by decide +kernel

private theorem step_271 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 271=stageVector 272 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 271) (stageCode 272)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_271 i)

private theorem check_272 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 272) 111 % 5=
      packedDigit 3 (stageCode 273) i.val % 5 := by decide +kernel

private theorem step_272 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 272=stageVector 273 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 272) (stageCode 273)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_272 i)

private theorem check_273 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 273) 111 % 5=
      packedDigit 3 (stageCode 274) i.val % 5 := by decide +kernel

private theorem step_273 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 273=stageVector 274 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 273) (stageCode 274)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_273 i)

private theorem check_274 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 274) 111 % 5=
      packedDigit 3 (stageCode 275) i.val % 5 := by decide +kernel

private theorem step_274 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 274=stageVector 275 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 274) (stageCode 275)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_274 i)

private theorem check_275 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 275) 111 % 5=
      packedDigit 3 (stageCode 276) i.val % 5 := by decide +kernel

private theorem step_275 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 275=stageVector 276 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 275) (stageCode 276)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_275 i)

private theorem check_276 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 276) 111 % 5=
      packedDigit 3 (stageCode 277) i.val % 5 := by decide +kernel

private theorem step_276 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 276=stageVector 277 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 276) (stageCode 277)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_276 i)

private theorem check_277 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 277) 111 % 5=
      packedDigit 3 (stageCode 278) i.val % 5 := by decide +kernel

private theorem step_277 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 277=stageVector 278 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 277) (stageCode 278)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_277 i)

private theorem check_278 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 278) 111 % 5=
      packedDigit 3 (stageCode 279) i.val % 5 := by decide +kernel

private theorem step_278 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 278=stageVector 279 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 278) (stageCode 279)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_278 i)

private theorem check_279 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 279) 111 % 5=
      packedDigit 3 (stageCode 280) i.val % 5 := by decide +kernel

private theorem step_279 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 279=stageVector 280 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 279) (stageCode 280)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_279 i)

private theorem check_280 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 280) 111 % 5=
      packedDigit 3 (stageCode 281) i.val % 5 := by decide +kernel

private theorem step_280 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 280=stageVector 281 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 280) (stageCode 281)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_280 i)

private theorem check_281 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 281) 111 % 5=
      packedDigit 3 (stageCode 282) i.val % 5 := by decide +kernel

private theorem step_281 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 281=stageVector 282 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 281) (stageCode 282)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_281 i)

private theorem check_282 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 282) 111 % 5=
      packedDigit 3 (stageCode 283) i.val % 5 := by decide +kernel

private theorem step_282 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 282=stageVector 283 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 282) (stageCode 283)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_282 i)

private theorem check_283 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 283) 111 % 5=
      packedDigit 3 (stageCode 284) i.val % 5 := by decide +kernel

private theorem step_283 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 283=stageVector 284 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 283) (stageCode 284)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_283 i)

private theorem check_284 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 284) 111 % 5=
      packedDigit 3 (stageCode 285) i.val % 5 := by decide +kernel

private theorem step_284 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 284=stageVector 285 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 284) (stageCode 285)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_284 i)

private theorem check_285 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 285) 111 % 5=
      packedDigit 3 (stageCode 286) i.val % 5 := by decide +kernel

private theorem step_285 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 285=stageVector 286 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 285) (stageCode 286)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_285 i)

private theorem check_286 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 286) 111 % 5=
      packedDigit 3 (stageCode 287) i.val % 5 := by decide +kernel

private theorem step_286 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 286=stageVector 287 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 286) (stageCode 287)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_286 i)

private theorem check_287 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 287) 111 % 5=
      packedDigit 3 (stageCode 288) i.val % 5 := by decide +kernel

private theorem step_287 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 287=stageVector 288 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 287) (stageCode 288)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_287 i)

private theorem check_288 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 288) 111 % 5=
      packedDigit 3 (stageCode 289) i.val % 5 := by decide +kernel

private theorem step_288 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 288=stageVector 289 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 288) (stageCode 289)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_288 i)

private theorem check_289 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 289) 111 % 5=
      packedDigit 3 (stageCode 290) i.val % 5 := by decide +kernel

private theorem step_289 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 289=stageVector 290 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 289) (stageCode 290)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_289 i)

private theorem check_290 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 290) 111 % 5=
      packedDigit 3 (stageCode 291) i.val % 5 := by decide +kernel

private theorem step_290 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 290=stageVector 291 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 290) (stageCode 291)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_290 i)

private theorem check_291 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 291) 111 % 5=
      packedDigit 3 (stageCode 292) i.val % 5 := by decide +kernel

private theorem step_291 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 291=stageVector 292 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 291) (stageCode 292)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_291 i)

private theorem check_292 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 292) 111 % 5=
      packedDigit 3 (stageCode 293) i.val % 5 := by decide +kernel

private theorem step_292 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 292=stageVector 293 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 292) (stageCode 293)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_292 i)

private theorem check_293 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 293) 111 % 5=
      packedDigit 3 (stageCode 294) i.val % 5 := by decide +kernel

private theorem step_293 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 293=stageVector 294 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 293) (stageCode 294)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_293 i)

private theorem check_294 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 294) 111 % 5=
      packedDigit 3 (stageCode 295) i.val % 5 := by decide +kernel

private theorem step_294 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 294=stageVector 295 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 294) (stageCode 295)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_294 i)

private theorem check_295 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 295) 111 % 5=
      packedDigit 3 (stageCode 296) i.val % 5 := by decide +kernel

private theorem step_295 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 295=stageVector 296 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 295) (stageCode 296)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_295 i)

private theorem check_296 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 296) 111 % 5=
      packedDigit 3 (stageCode 297) i.val % 5 := by decide +kernel

private theorem step_296 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 296=stageVector 297 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 296) (stageCode 297)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_296 i)

private theorem check_297 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 297) 111 % 5=
      packedDigit 3 (stageCode 298) i.val % 5 := by decide +kernel

private theorem step_297 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 297=stageVector 298 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 297) (stageCode 298)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_297 i)

private theorem check_298 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 298) 111 % 5=
      packedDigit 3 (stageCode 299) i.val % 5 := by decide +kernel

private theorem step_298 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 298=stageVector 299 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 298) (stageCode 299)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_298 i)

private theorem check_299 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 299) 111 % 5=
      packedDigit 3 (stageCode 300) i.val % 5 := by decide +kernel

private theorem step_299 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 299=stageVector 300 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 299) (stageCode 300)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_299 i)

private theorem check_300 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 300) 111 % 5=
      packedDigit 3 (stageCode 301) i.val % 5 := by decide +kernel

private theorem step_300 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 300=stageVector 301 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 300) (stageCode 301)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_300 i)

private theorem check_301 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 301) 111 % 5=
      packedDigit 3 (stageCode 302) i.val % 5 := by decide +kernel

private theorem step_301 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 301=stageVector 302 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 301) (stageCode 302)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_301 i)

private theorem check_302 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 302) 111 % 5=
      packedDigit 3 (stageCode 303) i.val % 5 := by decide +kernel

private theorem step_302 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 302=stageVector 303 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 302) (stageCode 303)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_302 i)

private theorem check_303 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 303) 111 % 5=
      packedDigit 3 (stageCode 304) i.val % 5 := by decide +kernel

private theorem step_303 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 303=stageVector 304 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 303) (stageCode 304)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_303 i)

private theorem check_304 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 304) 111 % 5=
      packedDigit 3 (stageCode 305) i.val % 5 := by decide +kernel

private theorem step_304 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 304=stageVector 305 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 304) (stageCode 305)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_304 i)

private theorem check_305 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 305) 111 % 5=
      packedDigit 3 (stageCode 306) i.val % 5 := by decide +kernel

private theorem step_305 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 305=stageVector 306 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 305) (stageCode 306)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_305 i)

private theorem check_306 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 306) 111 % 5=
      packedDigit 3 (stageCode 307) i.val % 5 := by decide +kernel

private theorem step_306 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 306=stageVector 307 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 306) (stageCode 307)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_306 i)

private theorem check_307 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 307) 111 % 5=
      packedDigit 3 (stageCode 308) i.val % 5 := by decide +kernel

private theorem step_307 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 307=stageVector 308 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 307) (stageCode 308)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_307 i)

private theorem check_308 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 308) 111 % 5=
      packedDigit 3 (stageCode 309) i.val % 5 := by decide +kernel

private theorem step_308 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 308=stageVector 309 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 308) (stageCode 309)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_308 i)

private theorem check_309 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 309) 111 % 5=
      packedDigit 3 (stageCode 310) i.val % 5 := by decide +kernel

private theorem step_309 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 309=stageVector 310 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 309) (stageCode 310)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_309 i)

private theorem check_310 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 310) 111 % 5=
      packedDigit 3 (stageCode 311) i.val % 5 := by decide +kernel

private theorem step_310 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 310=stageVector 311 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 310) (stageCode 311)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_310 i)

private theorem check_311 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 311) 111 % 5=
      packedDigit 3 (stageCode 312) i.val % 5 := by decide +kernel

private theorem step_311 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 311=stageVector 312 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 311) (stageCode 312)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_311 i)

private theorem check_312 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 312) 111 % 5=
      packedDigit 3 (stageCode 313) i.val % 5 := by decide +kernel

private theorem step_312 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 312=stageVector 313 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 312) (stageCode 313)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_312 i)

private theorem check_313 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 313) 111 % 5=
      packedDigit 3 (stageCode 314) i.val % 5 := by decide +kernel

private theorem step_313 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 313=stageVector 314 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 313) (stageCode 314)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_313 i)

private theorem check_314 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 314) 111 % 5=
      packedDigit 3 (stageCode 315) i.val % 5 := by decide +kernel

private theorem step_314 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 314=stageVector 315 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 314) (stageCode 315)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_314 i)

private theorem check_315 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 315) 111 % 5=
      packedDigit 3 (stageCode 316) i.val % 5 := by decide +kernel

private theorem step_315 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 315=stageVector 316 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 315) (stageCode 316)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_315 i)

private theorem check_316 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 316) 111 % 5=
      packedDigit 3 (stageCode 317) i.val % 5 := by decide +kernel

private theorem step_316 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 316=stageVector 317 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 316) (stageCode 317)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_316 i)

private theorem check_317 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 317) 111 % 5=
      packedDigit 3 (stageCode 318) i.val % 5 := by decide +kernel

private theorem step_317 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 317=stageVector 318 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 317) (stageCode 318)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_317 i)

private theorem check_318 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 318) 111 % 5=
      packedDigit 3 (stageCode 319) i.val % 5 := by decide +kernel

private theorem step_318 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 318=stageVector 319 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 318) (stageCode 319)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_318 i)

private theorem check_319 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 319) 111 % 5=
      packedDigit 3 (stageCode 320) i.val % 5 := by decide +kernel

private theorem step_319 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 319=stageVector 320 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 319) (stageCode 320)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_319 i)

private theorem check_320 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 320) 111 % 5=
      packedDigit 3 (stageCode 321) i.val % 5 := by decide +kernel

private theorem step_320 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 320=stageVector 321 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 320) (stageCode 321)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_320 i)

private theorem check_321 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 321) 111 % 5=
      packedDigit 3 (stageCode 322) i.val % 5 := by decide +kernel

private theorem step_321 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 321=stageVector 322 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 321) (stageCode 322)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_321 i)

private theorem check_322 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 322) 111 % 5=
      packedDigit 3 (stageCode 323) i.val % 5 := by decide +kernel

private theorem step_322 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 322=stageVector 323 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 322) (stageCode 323)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_322 i)

private theorem check_323 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 323) 111 % 5=
      packedDigit 3 (stageCode 324) i.val % 5 := by decide +kernel

private theorem step_323 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 323=stageVector 324 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 323) (stageCode 324)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_323 i)

private theorem check_324 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 324) 111 % 5=
      packedDigit 3 (stageCode 325) i.val % 5 := by decide +kernel

private theorem step_324 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 324=stageVector 325 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 324) (stageCode 325)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_324 i)

private theorem check_325 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 325) 111 % 5=
      packedDigit 3 (stageCode 326) i.val % 5 := by decide +kernel

private theorem step_325 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 325=stageVector 326 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 325) (stageCode 326)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_325 i)

private theorem check_326 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 326) 111 % 5=
      packedDigit 3 (stageCode 327) i.val % 5 := by decide +kernel

private theorem step_326 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 326=stageVector 327 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 326) (stageCode 327)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_326 i)

private theorem check_327 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 327) 111 % 5=
      packedDigit 3 (stageCode 328) i.val % 5 := by decide +kernel

private theorem step_327 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 327=stageVector 328 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 327) (stageCode 328)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_327 i)

private theorem check_328 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 328) 111 % 5=
      packedDigit 3 (stageCode 329) i.val % 5 := by decide +kernel

private theorem step_328 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 328=stageVector 329 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 328) (stageCode 329)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_328 i)

private theorem check_329 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 329) 111 % 5=
      packedDigit 3 (stageCode 330) i.val % 5 := by decide +kernel

private theorem step_329 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 329=stageVector 330 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 329) (stageCode 330)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_329 i)

private theorem check_330 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 330) 111 % 5=
      packedDigit 3 (stageCode 331) i.val % 5 := by decide +kernel

private theorem step_330 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 330=stageVector 331 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 330) (stageCode 331)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_330 i)

private theorem check_331 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 331) 111 % 5=
      packedDigit 3 (stageCode 332) i.val % 5 := by decide +kernel

private theorem step_331 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 331=stageVector 332 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 331) (stageCode 332)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_331 i)

private theorem check_332 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 332) 111 % 5=
      packedDigit 3 (stageCode 333) i.val % 5 := by decide +kernel

private theorem step_332 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 332=stageVector 333 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 332) (stageCode 333)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_332 i)

private theorem check_333 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 333) 111 % 5=
      packedDigit 3 (stageCode 334) i.val % 5 := by decide +kernel

private theorem step_333 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 333=stageVector 334 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 333) (stageCode 334)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_333 i)

private theorem check_334 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 334) 111 % 5=
      packedDigit 3 (stageCode 335) i.val % 5 := by decide +kernel

private theorem step_334 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 334=stageVector 335 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 334) (stageCode 335)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_334 i)

private theorem check_335 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 335) 111 % 5=
      packedDigit 3 (stageCode 336) i.val % 5 := by decide +kernel

private theorem step_335 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 335=stageVector 336 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 335) (stageCode 336)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_335 i)

private theorem check_336 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 336) 111 % 5=
      packedDigit 3 (stageCode 337) i.val % 5 := by decide +kernel

private theorem step_336 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 336=stageVector 337 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 336) (stageCode 337)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_336 i)

private theorem check_337 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 337) 111 % 5=
      packedDigit 3 (stageCode 338) i.val % 5 := by decide +kernel

private theorem step_337 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 337=stageVector 338 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 337) (stageCode 338)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_337 i)

private theorem check_338 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 338) 111 % 5=
      packedDigit 3 (stageCode 339) i.val % 5 := by decide +kernel

private theorem step_338 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 338=stageVector 339 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 338) (stageCode 339)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_338 i)

private theorem check_339 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 339) 111 % 5=
      packedDigit 3 (stageCode 340) i.val % 5 := by decide +kernel

private theorem step_339 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 339=stageVector 340 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 339) (stageCode 340)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_339 i)

private theorem check_340 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 340) 111 % 5=
      packedDigit 3 (stageCode 341) i.val % 5 := by decide +kernel

private theorem step_340 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 340=stageVector 341 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 340) (stageCode 341)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_340 i)

private theorem check_341 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 341) 111 % 5=
      packedDigit 3 (stageCode 342) i.val % 5 := by decide +kernel

private theorem step_341 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 341=stageVector 342 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 341) (stageCode 342)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_341 i)

private theorem check_342 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 342) 111 % 5=
      packedDigit 3 (stageCode 343) i.val % 5 := by decide +kernel

private theorem step_342 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 342=stageVector 343 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 342) (stageCode 343)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_342 i)

private theorem check_343 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 343) 111 % 5=
      packedDigit 3 (stageCode 344) i.val % 5 := by decide +kernel

private theorem step_343 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 343=stageVector 344 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 343) (stageCode 344)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_343 i)

private theorem check_344 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 344) 111 % 5=
      packedDigit 3 (stageCode 345) i.val % 5 := by decide +kernel

private theorem step_344 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 344=stageVector 345 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 344) (stageCode 345)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_344 i)

private theorem check_345 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 345) 111 % 5=
      packedDigit 3 (stageCode 346) i.val % 5 := by decide +kernel

private theorem step_345 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 345=stageVector 346 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 345) (stageCode 346)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_345 i)

private theorem check_346 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 346) 111 % 5=
      packedDigit 3 (stageCode 347) i.val % 5 := by decide +kernel

private theorem step_346 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 346=stageVector 347 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 346) (stageCode 347)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_346 i)

private theorem check_347 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 347) 111 % 5=
      packedDigit 3 (stageCode 348) i.val % 5 := by decide +kernel

private theorem step_347 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 347=stageVector 348 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 347) (stageCode 348)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_347 i)

private theorem check_348 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 348) 111 % 5=
      packedDigit 3 (stageCode 349) i.val % 5 := by decide +kernel

private theorem step_348 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 348=stageVector 349 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 348) (stageCode 349)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_348 i)

private theorem check_349 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 349) 111 % 5=
      packedDigit 3 (stageCode 350) i.val % 5 := by decide +kernel

private theorem step_349 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 349=stageVector 350 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 349) (stageCode 350)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_349 i)

private theorem check_350 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 350) 111 % 5=
      packedDigit 3 (stageCode 351) i.val % 5 := by decide +kernel

private theorem step_350 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 350=stageVector 351 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 350) (stageCode 351)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_350 i)

private theorem check_351 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 351) 111 % 5=
      packedDigit 3 (stageCode 352) i.val % 5 := by decide +kernel

private theorem step_351 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 351=stageVector 352 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 351) (stageCode 352)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_351 i)

private theorem check_352 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 352) 111 % 5=
      packedDigit 3 (stageCode 353) i.val % 5 := by decide +kernel

private theorem step_352 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 352=stageVector 353 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 352) (stageCode 353)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_352 i)

private theorem check_353 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 353) 111 % 5=
      packedDigit 3 (stageCode 354) i.val % 5 := by decide +kernel

private theorem step_353 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 353=stageVector 354 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 353) (stageCode 354)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_353 i)

private theorem check_354 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 354) 111 % 5=
      packedDigit 3 (stageCode 355) i.val % 5 := by decide +kernel

private theorem step_354 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 354=stageVector 355 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 354) (stageCode 355)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_354 i)

private theorem check_355 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 355) 111 % 5=
      packedDigit 3 (stageCode 356) i.val % 5 := by decide +kernel

private theorem step_355 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 355=stageVector 356 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 355) (stageCode 356)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_355 i)

private theorem check_356 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 356) 111 % 5=
      packedDigit 3 (stageCode 357) i.val % 5 := by decide +kernel

private theorem step_356 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 356=stageVector 357 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 356) (stageCode 357)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_356 i)

private theorem check_357 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 357) 111 % 5=
      packedDigit 3 (stageCode 358) i.val % 5 := by decide +kernel

private theorem step_357 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 357=stageVector 358 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 357) (stageCode 358)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_357 i)

private theorem check_358 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 358) 111 % 5=
      packedDigit 3 (stageCode 359) i.val % 5 := by decide +kernel

private theorem step_358 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 358=stageVector 359 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 358) (stageCode 359)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_358 i)

private theorem check_359 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 359) 111 % 5=
      packedDigit 3 (stageCode 360) i.val % 5 := by decide +kernel

private theorem step_359 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 359=stageVector 360 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 359) (stageCode 360)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_359 i)

private theorem check_360 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 360) 111 % 5=
      packedDigit 3 (stageCode 361) i.val % 5 := by decide +kernel

private theorem step_360 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 360=stageVector 361 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 360) (stageCode 361)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_360 i)

private theorem check_361 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 361) 111 % 5=
      packedDigit 3 (stageCode 362) i.val % 5 := by decide +kernel

private theorem step_361 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 361=stageVector 362 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 361) (stageCode 362)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_361 i)

private theorem check_362 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 362) 111 % 5=
      packedDigit 3 (stageCode 363) i.val % 5 := by decide +kernel

private theorem step_362 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 362=stageVector 363 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 362) (stageCode 363)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_362 i)

private theorem check_363 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 363) 111 % 5=
      packedDigit 3 (stageCode 364) i.val % 5 := by decide +kernel

private theorem step_363 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 363=stageVector 364 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 363) (stageCode 364)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_363 i)

private theorem check_364 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 364) 111 % 5=
      packedDigit 3 (stageCode 365) i.val % 5 := by decide +kernel

private theorem step_364 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 364=stageVector 365 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 364) (stageCode 365)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_364 i)

private theorem check_365 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 365) 111 % 5=
      packedDigit 3 (stageCode 366) i.val % 5 := by decide +kernel

private theorem step_365 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 365=stageVector 366 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 365) (stageCode 366)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_365 i)

private theorem check_366 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 366) 111 % 5=
      packedDigit 3 (stageCode 367) i.val % 5 := by decide +kernel

private theorem step_366 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 366=stageVector 367 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 366) (stageCode 367)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_366 i)

private theorem check_367 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 367) 111 % 5=
      packedDigit 3 (stageCode 368) i.val % 5 := by decide +kernel

private theorem step_367 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 367=stageVector 368 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 367) (stageCode 368)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_367 i)

private theorem check_368 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 368) 111 % 5=
      packedDigit 3 (stageCode 369) i.val % 5 := by decide +kernel

private theorem step_368 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 368=stageVector 369 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 368) (stageCode 369)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_368 i)

private theorem check_369 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 369) 111 % 5=
      packedDigit 3 (stageCode 370) i.val % 5 := by decide +kernel

private theorem step_369 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 369=stageVector 370 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 369) (stageCode 370)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_369 i)

private theorem check_370 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 370) 111 % 5=
      packedDigit 3 (stageCode 371) i.val % 5 := by decide +kernel

private theorem step_370 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 370=stageVector 371 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 370) (stageCode 371)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_370 i)

private theorem check_371 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 371) 111 % 5=
      packedDigit 3 (stageCode 372) i.val % 5 := by decide +kernel

private theorem step_371 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 371=stageVector 372 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 371) (stageCode 372)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_371 i)

private theorem check_372 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 372) 111 % 5=
      packedDigit 3 (stageCode 373) i.val % 5 := by decide +kernel

private theorem step_372 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 372=stageVector 373 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 372) (stageCode 373)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_372 i)

private theorem check_373 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 373) 111 % 5=
      packedDigit 3 (stageCode 374) i.val % 5 := by decide +kernel

private theorem step_373 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 373=stageVector 374 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 373) (stageCode 374)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_373 i)

private theorem check_374 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 374) 111 % 5=
      packedDigit 3 (stageCode 375) i.val % 5 := by decide +kernel

private theorem step_374 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 374=stageVector 375 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 374) (stageCode 375)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_374 i)

private theorem check_375 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 375) 111 % 5=
      packedDigit 3 (stageCode 376) i.val % 5 := by decide +kernel

private theorem step_375 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 375=stageVector 376 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 375) (stageCode 376)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_375 i)

private theorem check_376 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 376) 111 % 5=
      packedDigit 3 (stageCode 377) i.val % 5 := by decide +kernel

private theorem step_376 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 376=stageVector 377 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 376) (stageCode 377)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_376 i)

private theorem check_377 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 377) 111 % 5=
      packedDigit 3 (stageCode 378) i.val % 5 := by decide +kernel

private theorem step_377 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 377=stageVector 378 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 377) (stageCode 378)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_377 i)

private theorem check_378 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 378) 111 % 5=
      packedDigit 3 (stageCode 379) i.val % 5 := by decide +kernel

private theorem step_378 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 378=stageVector 379 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 378) (stageCode 379)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_378 i)

private theorem check_379 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 379) 111 % 5=
      packedDigit 3 (stageCode 380) i.val % 5 := by decide +kernel

private theorem step_379 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 379=stageVector 380 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 379) (stageCode 380)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_379 i)

private theorem check_380 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 380) 111 % 5=
      packedDigit 3 (stageCode 381) i.val % 5 := by decide +kernel

private theorem step_380 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 380=stageVector 381 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 380) (stageCode 381)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_380 i)

private theorem check_381 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 381) 111 % 5=
      packedDigit 3 (stageCode 382) i.val % 5 := by decide +kernel

private theorem step_381 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 381=stageVector 382 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 381) (stageCode 382)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_381 i)

private theorem check_382 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 382) 111 % 5=
      packedDigit 3 (stageCode 383) i.val % 5 := by decide +kernel

private theorem step_382 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 382=stageVector 383 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 382) (stageCode 383)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_382 i)

private theorem check_383 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 383) 111 % 5=
      packedDigit 3 (stageCode 384) i.val % 5 := by decide +kernel

private theorem step_383 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 383=stageVector 384 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 383) (stageCode 384)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_383 i)

private theorem check_384 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 384) 111 % 5=
      packedDigit 3 (stageCode 385) i.val % 5 := by decide +kernel

private theorem step_384 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 384=stageVector 385 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 384) (stageCode 385)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_384 i)

private theorem check_385 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 385) 111 % 5=
      packedDigit 3 (stageCode 386) i.val % 5 := by decide +kernel

private theorem step_385 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 385=stageVector 386 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 385) (stageCode 386)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_385 i)

private theorem check_386 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 386) 111 % 5=
      packedDigit 3 (stageCode 387) i.val % 5 := by decide +kernel

private theorem step_386 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 386=stageVector 387 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 386) (stageCode 387)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_386 i)

private theorem check_387 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 387) 111 % 5=
      packedDigit 3 (stageCode 388) i.val % 5 := by decide +kernel

private theorem step_387 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 387=stageVector 388 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 387) (stageCode 388)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_387 i)

private theorem check_388 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 388) 111 % 5=
      packedDigit 3 (stageCode 389) i.val % 5 := by decide +kernel

private theorem step_388 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 388=stageVector 389 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 388) (stageCode 389)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_388 i)

private theorem check_389 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 389) 111 % 5=
      packedDigit 3 (stageCode 390) i.val % 5 := by decide +kernel

private theorem step_389 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 389=stageVector 390 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 389) (stageCode 390)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_389 i)

private theorem check_390 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 390) 111 % 5=
      packedDigit 3 (stageCode 391) i.val % 5 := by decide +kernel

private theorem step_390 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 390=stageVector 391 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 390) (stageCode 391)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_390 i)

private theorem check_391 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 391) 111 % 5=
      packedDigit 3 (stageCode 392) i.val % 5 := by decide +kernel

private theorem step_391 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 391=stageVector 392 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 391) (stageCode 392)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_391 i)

private theorem check_392 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 392) 111 % 5=
      packedDigit 3 (stageCode 393) i.val % 5 := by decide +kernel

private theorem step_392 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 392=stageVector 393 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 392) (stageCode 393)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_392 i)

private theorem check_393 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 393) 111 % 5=
      packedDigit 3 (stageCode 394) i.val % 5 := by decide +kernel

private theorem step_393 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 393=stageVector 394 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 393) (stageCode 394)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_393 i)

private theorem check_394 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 394) 111 % 5=
      packedDigit 3 (stageCode 395) i.val % 5 := by decide +kernel

private theorem step_394 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 394=stageVector 395 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 394) (stageCode 395)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_394 i)

private theorem check_395 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 395) 111 % 5=
      packedDigit 3 (stageCode 396) i.val % 5 := by decide +kernel

private theorem step_395 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 395=stageVector 396 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 395) (stageCode 396)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_395 i)

private theorem check_396 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 396) 111 % 5=
      packedDigit 3 (stageCode 397) i.val % 5 := by decide +kernel

private theorem step_396 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 396=stageVector 397 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 396) (stageCode 397)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_396 i)

private theorem check_397 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 397) 111 % 5=
      packedDigit 3 (stageCode 398) i.val % 5 := by decide +kernel

private theorem step_397 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 397=stageVector 398 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 397) (stageCode 398)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_397 i)

private theorem check_398 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 398) 111 % 5=
      packedDigit 3 (stageCode 399) i.val % 5 := by decide +kernel

private theorem step_398 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 398=stageVector 399 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 398) (stageCode 399)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_398 i)

private theorem check_399 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 399) 111 % 5=
      packedDigit 3 (stageCode 400) i.val % 5 := by decide +kernel

private theorem step_399 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 399=stageVector 400 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 399) (stageCode 400)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_399 i)

private theorem check_400 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 400) 111 % 5=
      packedDigit 3 (stageCode 401) i.val % 5 := by decide +kernel

private theorem step_400 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 400=stageVector 401 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 400) (stageCode 401)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_400 i)

private theorem check_401 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 401) 111 % 5=
      packedDigit 3 (stageCode 402) i.val % 5 := by decide +kernel

private theorem step_401 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 401=stageVector 402 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 401) (stageCode 402)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_401 i)

private theorem check_402 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 402) 111 % 5=
      packedDigit 3 (stageCode 403) i.val % 5 := by decide +kernel

private theorem step_402 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 402=stageVector 403 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 402) (stageCode 403)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_402 i)

private theorem check_403 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 403) 111 % 5=
      packedDigit 3 (stageCode 404) i.val % 5 := by decide +kernel

private theorem step_403 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 403=stageVector 404 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 403) (stageCode 404)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_403 i)

private theorem check_404 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 404) 111 % 5=
      packedDigit 3 (stageCode 405) i.val % 5 := by decide +kernel

private theorem step_404 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 404=stageVector 405 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 404) (stageCode 405)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_404 i)

private theorem check_405 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 405) 111 % 5=
      packedDigit 3 (stageCode 406) i.val % 5 := by decide +kernel

private theorem step_405 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 405=stageVector 406 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 405) (stageCode 406)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_405 i)

private theorem check_406 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 406) 111 % 5=
      packedDigit 3 (stageCode 407) i.val % 5 := by decide +kernel

private theorem step_406 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 406=stageVector 407 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 406) (stageCode 407)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_406 i)

private theorem check_407 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 407) 111 % 5=
      packedDigit 3 (stageCode 408) i.val % 5 := by decide +kernel

private theorem step_407 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 407=stageVector 408 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 407) (stageCode 408)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_407 i)

private theorem check_408 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 408) 111 % 5=
      packedDigit 3 (stageCode 409) i.val % 5 := by decide +kernel

private theorem step_408 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 408=stageVector 409 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 408) (stageCode 409)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_408 i)

private theorem check_409 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 409) 111 % 5=
      packedDigit 3 (stageCode 410) i.val % 5 := by decide +kernel

private theorem step_409 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 409=stageVector 410 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 409) (stageCode 410)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_409 i)

private theorem check_410 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 410) 111 % 5=
      packedDigit 3 (stageCode 411) i.val % 5 := by decide +kernel

private theorem step_410 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 410=stageVector 411 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 410) (stageCode 411)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_410 i)

private theorem check_411 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 411) 111 % 5=
      packedDigit 3 (stageCode 412) i.val % 5 := by decide +kernel

private theorem step_411 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 411=stageVector 412 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 411) (stageCode 412)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_411 i)

private theorem check_412 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 412) 111 % 5=
      packedDigit 3 (stageCode 413) i.val % 5 := by decide +kernel

private theorem step_412 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 412=stageVector 413 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 412) (stageCode 413)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_412 i)

private theorem check_413 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 413) 111 % 5=
      packedDigit 3 (stageCode 414) i.val % 5 := by decide +kernel

private theorem step_413 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 413=stageVector 414 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 413) (stageCode 414)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_413 i)

private theorem check_414 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 414) 111 % 5=
      packedDigit 3 (stageCode 415) i.val % 5 := by decide +kernel

private theorem step_414 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 414=stageVector 415 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 414) (stageCode 415)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_414 i)

private theorem check_415 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 415) 111 % 5=
      packedDigit 3 (stageCode 416) i.val % 5 := by decide +kernel

private theorem step_415 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 415=stageVector 416 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 415) (stageCode 416)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_415 i)

private theorem check_416 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 416) 111 % 5=
      packedDigit 3 (stageCode 417) i.val % 5 := by decide +kernel

private theorem step_416 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 416=stageVector 417 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 416) (stageCode 417)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_416 i)

private theorem check_417 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 417) 111 % 5=
      packedDigit 3 (stageCode 418) i.val % 5 := by decide +kernel

private theorem step_417 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 417=stageVector 418 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 417) (stageCode 418)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_417 i)

private theorem check_418 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 418) 111 % 5=
      packedDigit 3 (stageCode 419) i.val % 5 := by decide +kernel

private theorem step_418 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 418=stageVector 419 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 418) (stageCode 419)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_418 i)

private theorem check_419 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 419) 111 % 5=
      packedDigit 3 (stageCode 420) i.val % 5 := by decide +kernel

private theorem step_419 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 419=stageVector 420 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 419) (stageCode 420)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_419 i)

private theorem check_420 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 420) 111 % 5=
      packedDigit 3 (stageCode 421) i.val % 5 := by decide +kernel

private theorem step_420 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 420=stageVector 421 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 420) (stageCode 421)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_420 i)

private theorem check_421 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 421) 111 % 5=
      packedDigit 3 (stageCode 422) i.val % 5 := by decide +kernel

private theorem step_421 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 421=stageVector 422 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 421) (stageCode 422)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_421 i)

private theorem check_422 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 422) 111 % 5=
      packedDigit 3 (stageCode 423) i.val % 5 := by decide +kernel

private theorem step_422 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 422=stageVector 423 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 422) (stageCode 423)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_422 i)

private theorem check_423 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 423) 111 % 5=
      packedDigit 3 (stageCode 424) i.val % 5 := by decide +kernel

private theorem step_423 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 423=stageVector 424 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 423) (stageCode 424)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_423 i)

private theorem check_424 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 424) 111 % 5=
      packedDigit 3 (stageCode 425) i.val % 5 := by decide +kernel

private theorem step_424 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 424=stageVector 425 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 424) (stageCode 425)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_424 i)

private theorem check_425 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 425) 111 % 5=
      packedDigit 3 (stageCode 426) i.val % 5 := by decide +kernel

private theorem step_425 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 425=stageVector 426 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 425) (stageCode 426)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_425 i)

private theorem check_426 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 426) 111 % 5=
      packedDigit 3 (stageCode 427) i.val % 5 := by decide +kernel

private theorem step_426 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 426=stageVector 427 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 426) (stageCode 427)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_426 i)

private theorem check_427 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 427) 111 % 5=
      packedDigit 3 (stageCode 428) i.val % 5 := by decide +kernel

private theorem step_427 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 427=stageVector 428 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 427) (stageCode 428)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_427 i)

private theorem check_428 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 428) 111 % 5=
      packedDigit 3 (stageCode 429) i.val % 5 := by decide +kernel

private theorem step_428 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 428=stageVector 429 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 428) (stageCode 429)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_428 i)

private theorem check_429 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 429) 111 % 5=
      packedDigit 3 (stageCode 430) i.val % 5 := by decide +kernel

private theorem step_429 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 429=stageVector 430 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 429) (stageCode 430)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_429 i)

private theorem check_430 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 430) 111 % 5=
      packedDigit 3 (stageCode 431) i.val % 5 := by decide +kernel

private theorem step_430 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 430=stageVector 431 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 430) (stageCode 431)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_430 i)

private theorem check_431 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 431) 111 % 5=
      packedDigit 3 (stageCode 432) i.val % 5 := by decide +kernel

private theorem step_431 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 431=stageVector 432 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 431) (stageCode 432)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_431 i)

private theorem check_432 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 432) 111 % 5=
      packedDigit 3 (stageCode 433) i.val % 5 := by decide +kernel

private theorem step_432 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 432=stageVector 433 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 432) (stageCode 433)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_432 i)

private theorem check_433 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 433) 111 % 5=
      packedDigit 3 (stageCode 434) i.val % 5 := by decide +kernel

private theorem step_433 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 433=stageVector 434 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 433) (stageCode 434)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_433 i)

private theorem check_434 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 434) 111 % 5=
      packedDigit 3 (stageCode 435) i.val % 5 := by decide +kernel

private theorem step_434 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 434=stageVector 435 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 434) (stageCode 435)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_434 i)

private theorem check_435 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 435) 111 % 5=
      packedDigit 3 (stageCode 436) i.val % 5 := by decide +kernel

private theorem step_435 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 435=stageVector 436 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 435) (stageCode 436)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_435 i)

private theorem check_436 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 436) 111 % 5=
      packedDigit 3 (stageCode 437) i.val % 5 := by decide +kernel

private theorem step_436 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 436=stageVector 437 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 436) (stageCode 437)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_436 i)

private theorem check_437 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 437) 111 % 5=
      packedDigit 3 (stageCode 438) i.val % 5 := by decide +kernel

private theorem step_437 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 437=stageVector 438 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 437) (stageCode 438)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_437 i)

private theorem check_438 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 438) 111 % 5=
      packedDigit 3 (stageCode 439) i.val % 5 := by decide +kernel

private theorem step_438 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 438=stageVector 439 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 438) (stageCode 439)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_438 i)

private theorem check_439 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 439) 111 % 5=
      packedDigit 3 (stageCode 440) i.val % 5 := by decide +kernel

private theorem step_439 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 439=stageVector 440 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 439) (stageCode 440)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_439 i)

private theorem check_440 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 440) 111 % 5=
      packedDigit 3 (stageCode 441) i.val % 5 := by decide +kernel

private theorem step_440 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 440=stageVector 441 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 440) (stageCode 441)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_440 i)

private theorem check_441 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 441) 111 % 5=
      packedDigit 3 (stageCode 442) i.val % 5 := by decide +kernel

private theorem step_441 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 441=stageVector 442 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 441) (stageCode 442)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_441 i)

private theorem check_442 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 442) 111 % 5=
      packedDigit 3 (stageCode 443) i.val % 5 := by decide +kernel

private theorem step_442 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 442=stageVector 443 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 442) (stageCode 443)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_442 i)

private theorem check_443 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 443) 111 % 5=
      packedDigit 3 (stageCode 444) i.val % 5 := by decide +kernel

private theorem step_443 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 443=stageVector 444 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 443) (stageCode 444)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_443 i)

private theorem check_444 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 444) 111 % 5=
      packedDigit 3 (stageCode 445) i.val % 5 := by decide +kernel

private theorem step_444 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 444=stageVector 445 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 444) (stageCode 445)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_444 i)

private theorem check_445 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 445) 111 % 5=
      packedDigit 3 (stageCode 446) i.val % 5 := by decide +kernel

private theorem step_445 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 445=stageVector 446 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 445) (stageCode 446)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_445 i)

private theorem check_446 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 446) 111 % 5=
      packedDigit 3 (stageCode 447) i.val % 5 := by decide +kernel

private theorem step_446 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 446=stageVector 447 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 446) (stageCode 447)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_446 i)

private theorem check_447 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 447) 111 % 5=
      packedDigit 3 (stageCode 448) i.val % 5 := by decide +kernel

private theorem step_447 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 447=stageVector 448 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 447) (stageCode 448)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_447 i)

private theorem check_448 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 448) 111 % 5=
      packedDigit 3 (stageCode 449) i.val % 5 := by decide +kernel

private theorem step_448 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 448=stageVector 449 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 448) (stageCode 449)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_448 i)

private theorem check_449 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 449) 111 % 5=
      packedDigit 3 (stageCode 450) i.val % 5 := by decide +kernel

private theorem step_449 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 449=stageVector 450 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 449) (stageCode 450)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_449 i)

private theorem check_450 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 450) 111 % 5=
      packedDigit 3 (stageCode 451) i.val % 5 := by decide +kernel

private theorem step_450 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 450=stageVector 451 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 450) (stageCode 451)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_450 i)

private theorem check_451 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 451) 111 % 5=
      packedDigit 3 (stageCode 452) i.val % 5 := by decide +kernel

private theorem step_451 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 451=stageVector 452 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 451) (stageCode 452)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_451 i)

private theorem check_452 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 452) 111 % 5=
      packedDigit 3 (stageCode 453) i.val % 5 := by decide +kernel

private theorem step_452 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 452=stageVector 453 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 452) (stageCode 453)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_452 i)

private theorem check_453 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 453) 111 % 5=
      packedDigit 3 (stageCode 454) i.val % 5 := by decide +kernel

private theorem step_453 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 453=stageVector 454 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 453) (stageCode 454)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_453 i)

private theorem check_454 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 454) 111 % 5=
      packedDigit 3 (stageCode 455) i.val % 5 := by decide +kernel

private theorem step_454 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 454=stageVector 455 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 454) (stageCode 455)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_454 i)

private theorem check_455 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 455) 111 % 5=
      packedDigit 3 (stageCode 456) i.val % 5 := by decide +kernel

private theorem step_455 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 455=stageVector 456 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 455) (stageCode 456)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_455 i)

private theorem check_456 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 456) 111 % 5=
      packedDigit 3 (stageCode 457) i.val % 5 := by decide +kernel

private theorem step_456 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 456=stageVector 457 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 456) (stageCode 457)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_456 i)

private theorem check_457 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 457) 111 % 5=
      packedDigit 3 (stageCode 458) i.val % 5 := by decide +kernel

private theorem step_457 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 457=stageVector 458 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 457) (stageCode 458)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_457 i)

private theorem check_458 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 458) 111 % 5=
      packedDigit 3 (stageCode 459) i.val % 5 := by decide +kernel

private theorem step_458 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 458=stageVector 459 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 458) (stageCode 459)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_458 i)

private theorem check_459 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 459) 111 % 5=
      packedDigit 3 (stageCode 460) i.val % 5 := by decide +kernel

private theorem step_459 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 459=stageVector 460 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 459) (stageCode 460)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_459 i)

private theorem check_460 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 460) 111 % 5=
      packedDigit 3 (stageCode 461) i.val % 5 := by decide +kernel

private theorem step_460 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 460=stageVector 461 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 460) (stageCode 461)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_460 i)

private theorem check_461 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 461) 111 % 5=
      packedDigit 3 (stageCode 462) i.val % 5 := by decide +kernel

private theorem step_461 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 461=stageVector 462 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 461) (stageCode 462)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_461 i)

private theorem check_462 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 462) 111 % 5=
      packedDigit 3 (stageCode 463) i.val % 5 := by decide +kernel

private theorem step_462 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 462=stageVector 463 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 462) (stageCode 463)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_462 i)

private theorem check_463 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 463) 111 % 5=
      packedDigit 3 (stageCode 464) i.val % 5 := by decide +kernel

private theorem step_463 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 463=stageVector 464 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 463) (stageCode 464)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_463 i)

private theorem check_464 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 464) 111 % 5=
      packedDigit 3 (stageCode 465) i.val % 5 := by decide +kernel

private theorem step_464 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 464=stageVector 465 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 464) (stageCode 465)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_464 i)

private theorem check_465 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 465) 111 % 5=
      packedDigit 3 (stageCode 466) i.val % 5 := by decide +kernel

private theorem step_465 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 465=stageVector 466 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 465) (stageCode 466)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_465 i)

private theorem check_466 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 466) 111 % 5=
      packedDigit 3 (stageCode 467) i.val % 5 := by decide +kernel

private theorem step_466 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 466=stageVector 467 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 466) (stageCode 467)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_466 i)

private theorem check_467 : ∀ i : Fin 111,
    packedDot 3 (secondRowCode i.val) (stageCode 467) 111 % 5=
      packedDigit 3 (stageCode 468) i.val % 5 := by decide +kernel

private theorem step_467 : CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ
    stageVector 467=stageVector 468 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows2 i
    (secondRowCode i.val) (stageCode 467) (stageCode 468)
    (fun j => CFSGLyPrimeSixtySevenSecondRows.binding i j) (check_467 i)

private theorem check_468 : ∀ i : Fin 111,
    packedDot 3 (firstRowCode i.val) (stageCode 468) 111 % 5=
      packedDigit 3 (stageCode 469) i.val % 5 := by decide +kernel

private theorem step_468 : CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ
    stageVector 468=stageVector 469 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 5 111 3 rows1 i
    (firstRowCode i.val) (stageCode 468) (stageCode 469)
    (fun j => CFSGLyPrimeSixtySevenFirstRows.binding i j) (check_468 i)

private theorem phase_0 (i : Fin 67) :
    CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ stageVector (7*i.val+0)=
      stageVector (7*i.val+1) := by
  fin_cases i
  · exact step_0
  · exact step_7
  · exact step_14
  · exact step_21
  · exact step_28
  · exact step_35
  · exact step_42
  · exact step_49
  · exact step_56
  · exact step_63
  · exact step_70
  · exact step_77
  · exact step_84
  · exact step_91
  · exact step_98
  · exact step_105
  · exact step_112
  · exact step_119
  · exact step_126
  · exact step_133
  · exact step_140
  · exact step_147
  · exact step_154
  · exact step_161
  · exact step_168
  · exact step_175
  · exact step_182
  · exact step_189
  · exact step_196
  · exact step_203
  · exact step_210
  · exact step_217
  · exact step_224
  · exact step_231
  · exact step_238
  · exact step_245
  · exact step_252
  · exact step_259
  · exact step_266
  · exact step_273
  · exact step_280
  · exact step_287
  · exact step_294
  · exact step_301
  · exact step_308
  · exact step_315
  · exact step_322
  · exact step_329
  · exact step_336
  · exact step_343
  · exact step_350
  · exact step_357
  · exact step_364
  · exact step_371
  · exact step_378
  · exact step_385
  · exact step_392
  · exact step_399
  · exact step_406
  · exact step_413
  · exact step_420
  · exact step_427
  · exact step_434
  · exact step_441
  · exact step_448
  · exact step_455
  · exact step_462

private theorem phase_1 (i : Fin 67) :
    CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ stageVector (7*i.val+1)=
      stageVector (7*i.val+2) := by
  fin_cases i
  · exact step_1
  · exact step_8
  · exact step_15
  · exact step_22
  · exact step_29
  · exact step_36
  · exact step_43
  · exact step_50
  · exact step_57
  · exact step_64
  · exact step_71
  · exact step_78
  · exact step_85
  · exact step_92
  · exact step_99
  · exact step_106
  · exact step_113
  · exact step_120
  · exact step_127
  · exact step_134
  · exact step_141
  · exact step_148
  · exact step_155
  · exact step_162
  · exact step_169
  · exact step_176
  · exact step_183
  · exact step_190
  · exact step_197
  · exact step_204
  · exact step_211
  · exact step_218
  · exact step_225
  · exact step_232
  · exact step_239
  · exact step_246
  · exact step_253
  · exact step_260
  · exact step_267
  · exact step_274
  · exact step_281
  · exact step_288
  · exact step_295
  · exact step_302
  · exact step_309
  · exact step_316
  · exact step_323
  · exact step_330
  · exact step_337
  · exact step_344
  · exact step_351
  · exact step_358
  · exact step_365
  · exact step_372
  · exact step_379
  · exact step_386
  · exact step_393
  · exact step_400
  · exact step_407
  · exact step_414
  · exact step_421
  · exact step_428
  · exact step_435
  · exact step_442
  · exact step_449
  · exact step_456
  · exact step_463

private theorem phase_2 (i : Fin 67) :
    CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ stageVector (7*i.val+2)=
      stageVector (7*i.val+3) := by
  fin_cases i
  · exact step_2
  · exact step_9
  · exact step_16
  · exact step_23
  · exact step_30
  · exact step_37
  · exact step_44
  · exact step_51
  · exact step_58
  · exact step_65
  · exact step_72
  · exact step_79
  · exact step_86
  · exact step_93
  · exact step_100
  · exact step_107
  · exact step_114
  · exact step_121
  · exact step_128
  · exact step_135
  · exact step_142
  · exact step_149
  · exact step_156
  · exact step_163
  · exact step_170
  · exact step_177
  · exact step_184
  · exact step_191
  · exact step_198
  · exact step_205
  · exact step_212
  · exact step_219
  · exact step_226
  · exact step_233
  · exact step_240
  · exact step_247
  · exact step_254
  · exact step_261
  · exact step_268
  · exact step_275
  · exact step_282
  · exact step_289
  · exact step_296
  · exact step_303
  · exact step_310
  · exact step_317
  · exact step_324
  · exact step_331
  · exact step_338
  · exact step_345
  · exact step_352
  · exact step_359
  · exact step_366
  · exact step_373
  · exact step_380
  · exact step_387
  · exact step_394
  · exact step_401
  · exact step_408
  · exact step_415
  · exact step_422
  · exact step_429
  · exact step_436
  · exact step_443
  · exact step_450
  · exact step_457
  · exact step_464

private theorem phase_3 (i : Fin 67) :
    CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ stageVector (7*i.val+3)=
      stageVector (7*i.val+4) := by
  fin_cases i
  · exact step_3
  · exact step_10
  · exact step_17
  · exact step_24
  · exact step_31
  · exact step_38
  · exact step_45
  · exact step_52
  · exact step_59
  · exact step_66
  · exact step_73
  · exact step_80
  · exact step_87
  · exact step_94
  · exact step_101
  · exact step_108
  · exact step_115
  · exact step_122
  · exact step_129
  · exact step_136
  · exact step_143
  · exact step_150
  · exact step_157
  · exact step_164
  · exact step_171
  · exact step_178
  · exact step_185
  · exact step_192
  · exact step_199
  · exact step_206
  · exact step_213
  · exact step_220
  · exact step_227
  · exact step_234
  · exact step_241
  · exact step_248
  · exact step_255
  · exact step_262
  · exact step_269
  · exact step_276
  · exact step_283
  · exact step_290
  · exact step_297
  · exact step_304
  · exact step_311
  · exact step_318
  · exact step_325
  · exact step_332
  · exact step_339
  · exact step_346
  · exact step_353
  · exact step_360
  · exact step_367
  · exact step_374
  · exact step_381
  · exact step_388
  · exact step_395
  · exact step_402
  · exact step_409
  · exact step_416
  · exact step_423
  · exact step_430
  · exact step_437
  · exact step_444
  · exact step_451
  · exact step_458
  · exact step_465

private theorem phase_4 (i : Fin 67) :
    CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ stageVector (7*i.val+4)=
      stageVector (7*i.val+5) := by
  fin_cases i
  · exact step_4
  · exact step_11
  · exact step_18
  · exact step_25
  · exact step_32
  · exact step_39
  · exact step_46
  · exact step_53
  · exact step_60
  · exact step_67
  · exact step_74
  · exact step_81
  · exact step_88
  · exact step_95
  · exact step_102
  · exact step_109
  · exact step_116
  · exact step_123
  · exact step_130
  · exact step_137
  · exact step_144
  · exact step_151
  · exact step_158
  · exact step_165
  · exact step_172
  · exact step_179
  · exact step_186
  · exact step_193
  · exact step_200
  · exact step_207
  · exact step_214
  · exact step_221
  · exact step_228
  · exact step_235
  · exact step_242
  · exact step_249
  · exact step_256
  · exact step_263
  · exact step_270
  · exact step_277
  · exact step_284
  · exact step_291
  · exact step_298
  · exact step_305
  · exact step_312
  · exact step_319
  · exact step_326
  · exact step_333
  · exact step_340
  · exact step_347
  · exact step_354
  · exact step_361
  · exact step_368
  · exact step_375
  · exact step_382
  · exact step_389
  · exact step_396
  · exact step_403
  · exact step_410
  · exact step_417
  · exact step_424
  · exact step_431
  · exact step_438
  · exact step_445
  · exact step_452
  · exact step_459
  · exact step_466

private theorem phase_5 (i : Fin 67) :
    CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ stageVector (7*i.val+5)=
      stageVector (7*i.val+6) := by
  fin_cases i
  · exact step_5
  · exact step_12
  · exact step_19
  · exact step_26
  · exact step_33
  · exact step_40
  · exact step_47
  · exact step_54
  · exact step_61
  · exact step_68
  · exact step_75
  · exact step_82
  · exact step_89
  · exact step_96
  · exact step_103
  · exact step_110
  · exact step_117
  · exact step_124
  · exact step_131
  · exact step_138
  · exact step_145
  · exact step_152
  · exact step_159
  · exact step_166
  · exact step_173
  · exact step_180
  · exact step_187
  · exact step_194
  · exact step_201
  · exact step_208
  · exact step_215
  · exact step_222
  · exact step_229
  · exact step_236
  · exact step_243
  · exact step_250
  · exact step_257
  · exact step_264
  · exact step_271
  · exact step_278
  · exact step_285
  · exact step_292
  · exact step_299
  · exact step_306
  · exact step_313
  · exact step_320
  · exact step_327
  · exact step_334
  · exact step_341
  · exact step_348
  · exact step_355
  · exact step_362
  · exact step_369
  · exact step_376
  · exact step_383
  · exact step_390
  · exact step_397
  · exact step_404
  · exact step_411
  · exact step_418
  · exact step_425
  · exact step_432
  · exact step_439
  · exact step_446
  · exact step_453
  · exact step_460
  · exact step_467

private theorem phase_6 (i : Fin 67) :
    CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ stageVector (7*i.val+6)=
      stageVector (7*i.val+7) := by
  fin_cases i
  · exact step_6
  · exact step_13
  · exact step_20
  · exact step_27
  · exact step_34
  · exact step_41
  · exact step_48
  · exact step_55
  · exact step_62
  · exact step_69
  · exact step_76
  · exact step_83
  · exact step_90
  · exact step_97
  · exact step_104
  · exact step_111
  · exact step_118
  · exact step_125
  · exact step_132
  · exact step_139
  · exact step_146
  · exact step_153
  · exact step_160
  · exact step_167
  · exact step_174
  · exact step_181
  · exact step_188
  · exact step_195
  · exact step_202
  · exact step_209
  · exact step_216
  · exact step_223
  · exact step_230
  · exact step_237
  · exact step_244
  · exact step_251
  · exact step_258
  · exact step_265
  · exact step_272
  · exact step_279
  · exact step_286
  · exact step_293
  · exact step_300
  · exact step_307
  · exact step_314
  · exact step_321
  · exact step_328
  · exact step_335
  · exact step_342
  · exact step_349
  · exact step_356
  · exact step_363
  · exact step_370
  · exact step_377
  · exact step_384
  · exact step_391
  · exact step_398
  · exact step_405
  · exact step_412
  · exact step_419
  · exact step_426
  · exact step_433
  · exact step_440
  · exact step_447
  · exact step_454
  · exact step_461
  · exact step_468

theorem word_step (i : Fin 67) : selectedEnd (vectors i.castSucc)=vectors i.succ := by
  rw [selectedEnd_apply]
  change (CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ (CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ (CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ (CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ (CFSG.Models.MatrixData.matrix 5 111 rows1 *ᵥ (CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ (CFSG.Models.MatrixData.matrix 5 111 rows2 *ᵥ stageVector (7*i.val+0))))))))=stageVector (7*(i.val+1))
  rw [phase_0,phase_1,phase_2,phase_3,phase_4,phase_5,phase_6]
  exact congrArg stageVector (by omega)

attribute [local irreducible] selectedEnd CFSG.Models.MatrixData.matrix
  CFSG.Models.MatrixData.generators rows1 rows2
  MatrixModelSelectedPositiveWordPrimePeriod.wordEnd

set_option maxRecDepth 4096 in
theorem selected_return : (selectedEnd^67) (vectors 0)=vectors 0 := by
  have hp : (selectedEnd ^ 67) (vectors 0) = vectors (Fin.last 67) :=
    LinearMapSelectedKrylovPeriod.pow_apply_eq_vector selectedEnd 67 vectors
      word_step (Fin.last 67)
  have he : vectors (Fin.last 67)=vectors 0 := by
    funext j
    change (packedDigit 3 (stageCode 469) j.val : ZMod 5)=
      (packedDigit 3 (stageCode 0) j.val : ZMod 5)
    rfl
  exact Eq.trans hp he

set_option maxRecDepth 4096 in
theorem selected_moved : selectedEnd (vectors 0)≠vectors 0 := by
  intro he
  have hn : vectors 1 (0 : Fin 111)≠vectors 0 (0 : Fin 111) := by decide +kernel
  exact hn (congrArg (fun v : CFSGLyPrimeSixtySevenPackedData.V => v (0 : Fin 111)) ((word_step 0).symm.trans he))

set_option maxRecDepth 4096 in
theorem sixty_seven_dvd_card (hn : ¬IsMulCommutative Model) : 67 ∣ Nat.card Model := by
  apply MatrixModelSelectedPositiveWordPrimePeriod.prime_dvd_card 5 111 rows1 rows2 actualWord
    67 (by decide) (vectors 0)
  · rw [wordEnd_binding]
    exact selected_return
  · rw [wordEnd_binding]
    exact selected_moved
  · exact hn

end SymmetricSubgroupAsymptotics.CFSGLySelectedPositiveSevenPrimeSixtySeven
