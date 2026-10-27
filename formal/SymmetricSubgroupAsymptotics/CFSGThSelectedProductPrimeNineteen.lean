import SymmetricSubgroupAsymptotics.CFSGThPrimeNineteenFirstRows
import SymmetricSubgroupAsymptotics.CFSGThPrimeNineteenSecondRows
import SymmetricSubgroupAsymptotics.CFSGThSelectedProductWord
import SymmetricSubgroupAsymptotics.MatrixModelSelectedRowVectorReflection
import SymmetricSubgroupAsymptotics.LinearMapSelectedKrylovPeriod

/-! SAME selected original matvecs. Separate arithmetic commands; no whole-word order. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGThSelectedProductPrimeNineteen
open MatrixNaturalRowDotReflection CFSGThPrimeNineteenPackedData CFSGThSelectedProductWord
open CFSG.Models.MatrixGroups.Th

private theorem check_0 : ∀ i : Fin 248,
    packedDot 2 (secondRowCode i.val) (stageCode 0) 248 % 3=
      packedDigit 2 (stageCode 1) i.val % 3 := by decide +kernel

private theorem step_0 : CFSG.Models.MatrixData.matrix 3 248 rows2 *ᵥ
    stageVector 0=stageVector 1 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 3 248 2 rows2 i
    (secondRowCode i.val) (stageCode 0) (stageCode 1)
    (fun j => CFSGThPrimeNineteenSecondRows.binding i j) (check_0 i)

private theorem check_1 : ∀ i : Fin 248,
    packedDot 2 (firstRowCode i.val) (stageCode 1) 248 % 3=
      packedDigit 2 (stageCode 2) i.val % 3 := by decide +kernel

private theorem step_1 : CFSG.Models.MatrixData.matrix 3 248 rows1 *ᵥ
    stageVector 1=stageVector 2 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 3 248 2 rows1 i
    (firstRowCode i.val) (stageCode 1) (stageCode 2)
    (fun j => CFSGThPrimeNineteenFirstRows.binding i j) (check_1 i)

private theorem check_2 : ∀ i : Fin 248,
    packedDot 2 (secondRowCode i.val) (stageCode 2) 248 % 3=
      packedDigit 2 (stageCode 3) i.val % 3 := by decide +kernel

private theorem step_2 : CFSG.Models.MatrixData.matrix 3 248 rows2 *ᵥ
    stageVector 2=stageVector 3 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 3 248 2 rows2 i
    (secondRowCode i.val) (stageCode 2) (stageCode 3)
    (fun j => CFSGThPrimeNineteenSecondRows.binding i j) (check_2 i)

private theorem check_3 : ∀ i : Fin 248,
    packedDot 2 (firstRowCode i.val) (stageCode 3) 248 % 3=
      packedDigit 2 (stageCode 4) i.val % 3 := by decide +kernel

private theorem step_3 : CFSG.Models.MatrixData.matrix 3 248 rows1 *ᵥ
    stageVector 3=stageVector 4 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 3 248 2 rows1 i
    (firstRowCode i.val) (stageCode 3) (stageCode 4)
    (fun j => CFSGThPrimeNineteenFirstRows.binding i j) (check_3 i)

private theorem check_4 : ∀ i : Fin 248,
    packedDot 2 (secondRowCode i.val) (stageCode 4) 248 % 3=
      packedDigit 2 (stageCode 5) i.val % 3 := by decide +kernel

private theorem step_4 : CFSG.Models.MatrixData.matrix 3 248 rows2 *ᵥ
    stageVector 4=stageVector 5 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 3 248 2 rows2 i
    (secondRowCode i.val) (stageCode 4) (stageCode 5)
    (fun j => CFSGThPrimeNineteenSecondRows.binding i j) (check_4 i)

private theorem check_5 : ∀ i : Fin 248,
    packedDot 2 (firstRowCode i.val) (stageCode 5) 248 % 3=
      packedDigit 2 (stageCode 6) i.val % 3 := by decide +kernel

private theorem step_5 : CFSG.Models.MatrixData.matrix 3 248 rows1 *ᵥ
    stageVector 5=stageVector 6 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 3 248 2 rows1 i
    (firstRowCode i.val) (stageCode 5) (stageCode 6)
    (fun j => CFSGThPrimeNineteenFirstRows.binding i j) (check_5 i)

private theorem check_6 : ∀ i : Fin 248,
    packedDot 2 (secondRowCode i.val) (stageCode 6) 248 % 3=
      packedDigit 2 (stageCode 7) i.val % 3 := by decide +kernel

private theorem step_6 : CFSG.Models.MatrixData.matrix 3 248 rows2 *ᵥ
    stageVector 6=stageVector 7 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 3 248 2 rows2 i
    (secondRowCode i.val) (stageCode 6) (stageCode 7)
    (fun j => CFSGThPrimeNineteenSecondRows.binding i j) (check_6 i)

private theorem check_7 : ∀ i : Fin 248,
    packedDot 2 (firstRowCode i.val) (stageCode 7) 248 % 3=
      packedDigit 2 (stageCode 8) i.val % 3 := by decide +kernel

private theorem step_7 : CFSG.Models.MatrixData.matrix 3 248 rows1 *ᵥ
    stageVector 7=stageVector 8 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 3 248 2 rows1 i
    (firstRowCode i.val) (stageCode 7) (stageCode 8)
    (fun j => CFSGThPrimeNineteenFirstRows.binding i j) (check_7 i)

private theorem check_8 : ∀ i : Fin 248,
    packedDot 2 (secondRowCode i.val) (stageCode 8) 248 % 3=
      packedDigit 2 (stageCode 9) i.val % 3 := by decide +kernel

private theorem step_8 : CFSG.Models.MatrixData.matrix 3 248 rows2 *ᵥ
    stageVector 8=stageVector 9 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 3 248 2 rows2 i
    (secondRowCode i.val) (stageCode 8) (stageCode 9)
    (fun j => CFSGThPrimeNineteenSecondRows.binding i j) (check_8 i)

private theorem check_9 : ∀ i : Fin 248,
    packedDot 2 (firstRowCode i.val) (stageCode 9) 248 % 3=
      packedDigit 2 (stageCode 10) i.val % 3 := by decide +kernel

private theorem step_9 : CFSG.Models.MatrixData.matrix 3 248 rows1 *ᵥ
    stageVector 9=stageVector 10 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 3 248 2 rows1 i
    (firstRowCode i.val) (stageCode 9) (stageCode 10)
    (fun j => CFSGThPrimeNineteenFirstRows.binding i j) (check_9 i)

private theorem check_10 : ∀ i : Fin 248,
    packedDot 2 (secondRowCode i.val) (stageCode 10) 248 % 3=
      packedDigit 2 (stageCode 11) i.val % 3 := by decide +kernel

private theorem step_10 : CFSG.Models.MatrixData.matrix 3 248 rows2 *ᵥ
    stageVector 10=stageVector 11 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 3 248 2 rows2 i
    (secondRowCode i.val) (stageCode 10) (stageCode 11)
    (fun j => CFSGThPrimeNineteenSecondRows.binding i j) (check_10 i)

private theorem check_11 : ∀ i : Fin 248,
    packedDot 2 (firstRowCode i.val) (stageCode 11) 248 % 3=
      packedDigit 2 (stageCode 12) i.val % 3 := by decide +kernel

private theorem step_11 : CFSG.Models.MatrixData.matrix 3 248 rows1 *ᵥ
    stageVector 11=stageVector 12 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 3 248 2 rows1 i
    (firstRowCode i.val) (stageCode 11) (stageCode 12)
    (fun j => CFSGThPrimeNineteenFirstRows.binding i j) (check_11 i)

private theorem check_12 : ∀ i : Fin 248,
    packedDot 2 (secondRowCode i.val) (stageCode 12) 248 % 3=
      packedDigit 2 (stageCode 13) i.val % 3 := by decide +kernel

private theorem step_12 : CFSG.Models.MatrixData.matrix 3 248 rows2 *ᵥ
    stageVector 12=stageVector 13 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 3 248 2 rows2 i
    (secondRowCode i.val) (stageCode 12) (stageCode 13)
    (fun j => CFSGThPrimeNineteenSecondRows.binding i j) (check_12 i)

private theorem check_13 : ∀ i : Fin 248,
    packedDot 2 (firstRowCode i.val) (stageCode 13) 248 % 3=
      packedDigit 2 (stageCode 14) i.val % 3 := by decide +kernel

private theorem step_13 : CFSG.Models.MatrixData.matrix 3 248 rows1 *ᵥ
    stageVector 13=stageVector 14 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 3 248 2 rows1 i
    (firstRowCode i.val) (stageCode 13) (stageCode 14)
    (fun j => CFSGThPrimeNineteenFirstRows.binding i j) (check_13 i)

private theorem check_14 : ∀ i : Fin 248,
    packedDot 2 (secondRowCode i.val) (stageCode 14) 248 % 3=
      packedDigit 2 (stageCode 15) i.val % 3 := by decide +kernel

private theorem step_14 : CFSG.Models.MatrixData.matrix 3 248 rows2 *ᵥ
    stageVector 14=stageVector 15 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 3 248 2 rows2 i
    (secondRowCode i.val) (stageCode 14) (stageCode 15)
    (fun j => CFSGThPrimeNineteenSecondRows.binding i j) (check_14 i)

private theorem check_15 : ∀ i : Fin 248,
    packedDot 2 (firstRowCode i.val) (stageCode 15) 248 % 3=
      packedDigit 2 (stageCode 16) i.val % 3 := by decide +kernel

private theorem step_15 : CFSG.Models.MatrixData.matrix 3 248 rows1 *ᵥ
    stageVector 15=stageVector 16 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 3 248 2 rows1 i
    (firstRowCode i.val) (stageCode 15) (stageCode 16)
    (fun j => CFSGThPrimeNineteenFirstRows.binding i j) (check_15 i)

private theorem check_16 : ∀ i : Fin 248,
    packedDot 2 (secondRowCode i.val) (stageCode 16) 248 % 3=
      packedDigit 2 (stageCode 17) i.val % 3 := by decide +kernel

private theorem step_16 : CFSG.Models.MatrixData.matrix 3 248 rows2 *ᵥ
    stageVector 16=stageVector 17 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 3 248 2 rows2 i
    (secondRowCode i.val) (stageCode 16) (stageCode 17)
    (fun j => CFSGThPrimeNineteenSecondRows.binding i j) (check_16 i)

private theorem check_17 : ∀ i : Fin 248,
    packedDot 2 (firstRowCode i.val) (stageCode 17) 248 % 3=
      packedDigit 2 (stageCode 18) i.val % 3 := by decide +kernel

private theorem step_17 : CFSG.Models.MatrixData.matrix 3 248 rows1 *ᵥ
    stageVector 17=stageVector 18 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 3 248 2 rows1 i
    (firstRowCode i.val) (stageCode 17) (stageCode 18)
    (fun j => CFSGThPrimeNineteenFirstRows.binding i j) (check_17 i)

private theorem check_18 : ∀ i : Fin 248,
    packedDot 2 (secondRowCode i.val) (stageCode 18) 248 % 3=
      packedDigit 2 (stageCode 19) i.val % 3 := by decide +kernel

private theorem step_18 : CFSG.Models.MatrixData.matrix 3 248 rows2 *ᵥ
    stageVector 18=stageVector 19 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 3 248 2 rows2 i
    (secondRowCode i.val) (stageCode 18) (stageCode 19)
    (fun j => CFSGThPrimeNineteenSecondRows.binding i j) (check_18 i)

private theorem check_19 : ∀ i : Fin 248,
    packedDot 2 (firstRowCode i.val) (stageCode 19) 248 % 3=
      packedDigit 2 (stageCode 20) i.val % 3 := by decide +kernel

private theorem step_19 : CFSG.Models.MatrixData.matrix 3 248 rows1 *ᵥ
    stageVector 19=stageVector 20 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 3 248 2 rows1 i
    (firstRowCode i.val) (stageCode 19) (stageCode 20)
    (fun j => CFSGThPrimeNineteenFirstRows.binding i j) (check_19 i)

private theorem check_20 : ∀ i : Fin 248,
    packedDot 2 (secondRowCode i.val) (stageCode 20) 248 % 3=
      packedDigit 2 (stageCode 21) i.val % 3 := by decide +kernel

private theorem step_20 : CFSG.Models.MatrixData.matrix 3 248 rows2 *ᵥ
    stageVector 20=stageVector 21 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 3 248 2 rows2 i
    (secondRowCode i.val) (stageCode 20) (stageCode 21)
    (fun j => CFSGThPrimeNineteenSecondRows.binding i j) (check_20 i)

private theorem check_21 : ∀ i : Fin 248,
    packedDot 2 (firstRowCode i.val) (stageCode 21) 248 % 3=
      packedDigit 2 (stageCode 22) i.val % 3 := by decide +kernel

private theorem step_21 : CFSG.Models.MatrixData.matrix 3 248 rows1 *ᵥ
    stageVector 21=stageVector 22 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 3 248 2 rows1 i
    (firstRowCode i.val) (stageCode 21) (stageCode 22)
    (fun j => CFSGThPrimeNineteenFirstRows.binding i j) (check_21 i)

private theorem check_22 : ∀ i : Fin 248,
    packedDot 2 (secondRowCode i.val) (stageCode 22) 248 % 3=
      packedDigit 2 (stageCode 23) i.val % 3 := by decide +kernel

private theorem step_22 : CFSG.Models.MatrixData.matrix 3 248 rows2 *ᵥ
    stageVector 22=stageVector 23 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 3 248 2 rows2 i
    (secondRowCode i.val) (stageCode 22) (stageCode 23)
    (fun j => CFSGThPrimeNineteenSecondRows.binding i j) (check_22 i)

private theorem check_23 : ∀ i : Fin 248,
    packedDot 2 (firstRowCode i.val) (stageCode 23) 248 % 3=
      packedDigit 2 (stageCode 24) i.val % 3 := by decide +kernel

private theorem step_23 : CFSG.Models.MatrixData.matrix 3 248 rows1 *ᵥ
    stageVector 23=stageVector 24 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 3 248 2 rows1 i
    (firstRowCode i.val) (stageCode 23) (stageCode 24)
    (fun j => CFSGThPrimeNineteenFirstRows.binding i j) (check_23 i)

private theorem check_24 : ∀ i : Fin 248,
    packedDot 2 (secondRowCode i.val) (stageCode 24) 248 % 3=
      packedDigit 2 (stageCode 25) i.val % 3 := by decide +kernel

private theorem step_24 : CFSG.Models.MatrixData.matrix 3 248 rows2 *ᵥ
    stageVector 24=stageVector 25 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 3 248 2 rows2 i
    (secondRowCode i.val) (stageCode 24) (stageCode 25)
    (fun j => CFSGThPrimeNineteenSecondRows.binding i j) (check_24 i)

private theorem check_25 : ∀ i : Fin 248,
    packedDot 2 (firstRowCode i.val) (stageCode 25) 248 % 3=
      packedDigit 2 (stageCode 26) i.val % 3 := by decide +kernel

private theorem step_25 : CFSG.Models.MatrixData.matrix 3 248 rows1 *ᵥ
    stageVector 25=stageVector 26 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 3 248 2 rows1 i
    (firstRowCode i.val) (stageCode 25) (stageCode 26)
    (fun j => CFSGThPrimeNineteenFirstRows.binding i j) (check_25 i)

private theorem check_26 : ∀ i : Fin 248,
    packedDot 2 (secondRowCode i.val) (stageCode 26) 248 % 3=
      packedDigit 2 (stageCode 27) i.val % 3 := by decide +kernel

private theorem step_26 : CFSG.Models.MatrixData.matrix 3 248 rows2 *ᵥ
    stageVector 26=stageVector 27 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 3 248 2 rows2 i
    (secondRowCode i.val) (stageCode 26) (stageCode 27)
    (fun j => CFSGThPrimeNineteenSecondRows.binding i j) (check_26 i)

private theorem check_27 : ∀ i : Fin 248,
    packedDot 2 (firstRowCode i.val) (stageCode 27) 248 % 3=
      packedDigit 2 (stageCode 28) i.val % 3 := by decide +kernel

private theorem step_27 : CFSG.Models.MatrixData.matrix 3 248 rows1 *ᵥ
    stageVector 27=stageVector 28 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 3 248 2 rows1 i
    (firstRowCode i.val) (stageCode 27) (stageCode 28)
    (fun j => CFSGThPrimeNineteenFirstRows.binding i j) (check_27 i)

private theorem check_28 : ∀ i : Fin 248,
    packedDot 2 (secondRowCode i.val) (stageCode 28) 248 % 3=
      packedDigit 2 (stageCode 29) i.val % 3 := by decide +kernel

private theorem step_28 : CFSG.Models.MatrixData.matrix 3 248 rows2 *ᵥ
    stageVector 28=stageVector 29 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 3 248 2 rows2 i
    (secondRowCode i.val) (stageCode 28) (stageCode 29)
    (fun j => CFSGThPrimeNineteenSecondRows.binding i j) (check_28 i)

private theorem check_29 : ∀ i : Fin 248,
    packedDot 2 (firstRowCode i.val) (stageCode 29) 248 % 3=
      packedDigit 2 (stageCode 30) i.val % 3 := by decide +kernel

private theorem step_29 : CFSG.Models.MatrixData.matrix 3 248 rows1 *ᵥ
    stageVector 29=stageVector 30 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 3 248 2 rows1 i
    (firstRowCode i.val) (stageCode 29) (stageCode 30)
    (fun j => CFSGThPrimeNineteenFirstRows.binding i j) (check_29 i)

private theorem check_30 : ∀ i : Fin 248,
    packedDot 2 (secondRowCode i.val) (stageCode 30) 248 % 3=
      packedDigit 2 (stageCode 31) i.val % 3 := by decide +kernel

private theorem step_30 : CFSG.Models.MatrixData.matrix 3 248 rows2 *ᵥ
    stageVector 30=stageVector 31 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 3 248 2 rows2 i
    (secondRowCode i.val) (stageCode 30) (stageCode 31)
    (fun j => CFSGThPrimeNineteenSecondRows.binding i j) (check_30 i)

private theorem check_31 : ∀ i : Fin 248,
    packedDot 2 (firstRowCode i.val) (stageCode 31) 248 % 3=
      packedDigit 2 (stageCode 32) i.val % 3 := by decide +kernel

private theorem step_31 : CFSG.Models.MatrixData.matrix 3 248 rows1 *ᵥ
    stageVector 31=stageVector 32 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 3 248 2 rows1 i
    (firstRowCode i.val) (stageCode 31) (stageCode 32)
    (fun j => CFSGThPrimeNineteenFirstRows.binding i j) (check_31 i)

private theorem check_32 : ∀ i : Fin 248,
    packedDot 2 (secondRowCode i.val) (stageCode 32) 248 % 3=
      packedDigit 2 (stageCode 33) i.val % 3 := by decide +kernel

private theorem step_32 : CFSG.Models.MatrixData.matrix 3 248 rows2 *ᵥ
    stageVector 32=stageVector 33 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 3 248 2 rows2 i
    (secondRowCode i.val) (stageCode 32) (stageCode 33)
    (fun j => CFSGThPrimeNineteenSecondRows.binding i j) (check_32 i)

private theorem check_33 : ∀ i : Fin 248,
    packedDot 2 (firstRowCode i.val) (stageCode 33) 248 % 3=
      packedDigit 2 (stageCode 34) i.val % 3 := by decide +kernel

private theorem step_33 : CFSG.Models.MatrixData.matrix 3 248 rows1 *ᵥ
    stageVector 33=stageVector 34 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 3 248 2 rows1 i
    (firstRowCode i.val) (stageCode 33) (stageCode 34)
    (fun j => CFSGThPrimeNineteenFirstRows.binding i j) (check_33 i)

private theorem check_34 : ∀ i : Fin 248,
    packedDot 2 (secondRowCode i.val) (stageCode 34) 248 % 3=
      packedDigit 2 (stageCode 35) i.val % 3 := by decide +kernel

private theorem step_34 : CFSG.Models.MatrixData.matrix 3 248 rows2 *ᵥ
    stageVector 34=stageVector 35 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 3 248 2 rows2 i
    (secondRowCode i.val) (stageCode 34) (stageCode 35)
    (fun j => CFSGThPrimeNineteenSecondRows.binding i j) (check_34 i)

private theorem check_35 : ∀ i : Fin 248,
    packedDot 2 (firstRowCode i.val) (stageCode 35) 248 % 3=
      packedDigit 2 (stageCode 36) i.val % 3 := by decide +kernel

private theorem step_35 : CFSG.Models.MatrixData.matrix 3 248 rows1 *ᵥ
    stageVector 35=stageVector 36 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 3 248 2 rows1 i
    (firstRowCode i.val) (stageCode 35) (stageCode 36)
    (fun j => CFSGThPrimeNineteenFirstRows.binding i j) (check_35 i)

private theorem check_36 : ∀ i : Fin 248,
    packedDot 2 (secondRowCode i.val) (stageCode 36) 248 % 3=
      packedDigit 2 (stageCode 37) i.val % 3 := by decide +kernel

private theorem step_36 : CFSG.Models.MatrixData.matrix 3 248 rows2 *ᵥ
    stageVector 36=stageVector 37 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 3 248 2 rows2 i
    (secondRowCode i.val) (stageCode 36) (stageCode 37)
    (fun j => CFSGThPrimeNineteenSecondRows.binding i j) (check_36 i)

private theorem check_37 : ∀ i : Fin 248,
    packedDot 2 (firstRowCode i.val) (stageCode 37) 248 % 3=
      packedDigit 2 (stageCode 38) i.val % 3 := by decide +kernel

private theorem step_37 : CFSG.Models.MatrixData.matrix 3 248 rows1 *ᵥ
    stageVector 37=stageVector 38 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 3 248 2 rows1 i
    (firstRowCode i.val) (stageCode 37) (stageCode 38)
    (fun j => CFSGThPrimeNineteenFirstRows.binding i j) (check_37 i)

private theorem phase_0 (i : Fin 19) :
    CFSG.Models.MatrixData.matrix 3 248 rows2 *ᵥ stageVector (2*i.val+0)=
      stageVector (2*i.val+1) := by
  fin_cases i
  · exact step_0
  · exact step_2
  · exact step_4
  · exact step_6
  · exact step_8
  · exact step_10
  · exact step_12
  · exact step_14
  · exact step_16
  · exact step_18
  · exact step_20
  · exact step_22
  · exact step_24
  · exact step_26
  · exact step_28
  · exact step_30
  · exact step_32
  · exact step_34
  · exact step_36

private theorem phase_1 (i : Fin 19) :
    CFSG.Models.MatrixData.matrix 3 248 rows1 *ᵥ stageVector (2*i.val+1)=
      stageVector (2*i.val+2) := by
  fin_cases i
  · exact step_1
  · exact step_3
  · exact step_5
  · exact step_7
  · exact step_9
  · exact step_11
  · exact step_13
  · exact step_15
  · exact step_17
  · exact step_19
  · exact step_21
  · exact step_23
  · exact step_25
  · exact step_27
  · exact step_29
  · exact step_31
  · exact step_33
  · exact step_35
  · exact step_37

theorem word_step (i : Fin 19) : selectedEnd (vectors i.castSucc)=vectors i.succ := by
  rw [selectedEnd_apply]
  change (CFSG.Models.MatrixData.matrix 3 248 rows1 *ᵥ (CFSG.Models.MatrixData.matrix 3 248 rows2 *ᵥ stageVector (2*i.val+0)))=stageVector (2*(i.val+1))
  rw [phase_0,phase_1]
  exact congrArg stageVector (by omega)

set_option maxRecDepth 4096 in
theorem selected_return : (selectedEnd^19) (vectors 0)=vectors 0 := by
  have hp := LinearMapSelectedKrylovPeriod.pow_apply_eq_vector selectedEnd 19 vectors
    word_step (Fin.last 19)
  have he : vectors (Fin.last 19)=vectors 0 := by
    funext j
    change (packedDigit 2 (stageCode 38) j.val : ZMod 3)=
      (packedDigit 2 (stageCode 0) j.val : ZMod 3)
    rfl
  exact hp.trans he

set_option maxRecDepth 4096 in
theorem selected_moved : selectedEnd (vectors 0)≠vectors 0 := by
  intro he
  have hn : vectors 1 (0 : Fin 248)≠vectors 0 (0 : Fin 248) := by decide +kernel
  exact hn (congrArg (fun v : CFSGThPrimeNineteenPackedData.V => v (0 : Fin 248)) ((word_step 0).symm.trans he))

attribute [local irreducible] selectedEnd CFSG.Models.MatrixData.matrix
  CFSG.Models.MatrixData.generators rows1 rows2
  MatrixModelSelectedPositiveWordPrimePeriod.wordEnd

set_option maxRecDepth 4096 in
theorem nineteen_dvd_card (hn : ¬IsMulCommutative Model) : 19 ∣ Nat.card Model := by
  apply MatrixModelSelectedPositiveWordPrimePeriod.prime_dvd_card 3 248 rows1 rows2 actualWord
    19 (by decide) (vectors 0)
  · rw [wordEnd_binding]
    exact selected_return
  · rw [wordEnd_binding]
    exact selected_moved
  · exact hn

end SymmetricSubgroupAsymptotics.CFSGThSelectedProductPrimeNineteen
