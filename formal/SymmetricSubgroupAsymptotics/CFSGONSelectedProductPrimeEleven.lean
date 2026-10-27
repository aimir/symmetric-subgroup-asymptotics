import SymmetricSubgroupAsymptotics.CFSGONPrimeElevenFirstTransposeRows
import SymmetricSubgroupAsymptotics.CFSGONPrimeElevenSecondTransposeRows
import SymmetricSubgroupAsymptotics.CFSGONSelectedProductWord
import SymmetricSubgroupAsymptotics.MatrixModelSelectedRowVectorReflection
import SymmetricSubgroupAsymptotics.LinearMapSelectedKrylovPeriod

/-! SAME selected original matvecs. Separate arithmetic commands; no whole-word order. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGONSelectedProductPrimeEleven
open MatrixNaturalRowDotReflection CFSGONPrimeElevenPackedData CFSGONSelectedProductWord
open CFSG.Models.MatrixGroups.ON

private theorem check_0 : ∀ i : Fin 154,
    packedDot 2 (secondRowCode i.val) (stageCode 0) 154 % 3=
      packedDigit 2 (stageCode 1) i.val % 3 := by decide +kernel

private theorem step_0 : CFSG.Models.MatrixData.matrix 3 154 rows2 *ᵥ
    stageVector 0=stageVector 1 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 3 154 2 rows2 i
    (secondRowCode i.val) (stageCode 0) (stageCode 1)
    (fun j => CFSGONPrimeElevenSecondTransposeRows.binding i j) (check_0 i)

private theorem check_1 : ∀ i : Fin 154,
    packedDot 2 (firstRowCode i.val) (stageCode 1) 154 % 3=
      packedDigit 2 (stageCode 2) i.val % 3 := by decide +kernel

private theorem step_1 : CFSG.Models.MatrixData.matrix 3 154 rows1 *ᵥ
    stageVector 1=stageVector 2 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 3 154 2 rows1 i
    (firstRowCode i.val) (stageCode 1) (stageCode 2)
    (fun j => CFSGONPrimeElevenFirstTransposeRows.binding i j) (check_1 i)

private theorem check_2 : ∀ i : Fin 154,
    packedDot 2 (secondRowCode i.val) (stageCode 2) 154 % 3=
      packedDigit 2 (stageCode 3) i.val % 3 := by decide +kernel

private theorem step_2 : CFSG.Models.MatrixData.matrix 3 154 rows2 *ᵥ
    stageVector 2=stageVector 3 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 3 154 2 rows2 i
    (secondRowCode i.val) (stageCode 2) (stageCode 3)
    (fun j => CFSGONPrimeElevenSecondTransposeRows.binding i j) (check_2 i)

private theorem check_3 : ∀ i : Fin 154,
    packedDot 2 (firstRowCode i.val) (stageCode 3) 154 % 3=
      packedDigit 2 (stageCode 4) i.val % 3 := by decide +kernel

private theorem step_3 : CFSG.Models.MatrixData.matrix 3 154 rows1 *ᵥ
    stageVector 3=stageVector 4 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 3 154 2 rows1 i
    (firstRowCode i.val) (stageCode 3) (stageCode 4)
    (fun j => CFSGONPrimeElevenFirstTransposeRows.binding i j) (check_3 i)

private theorem check_4 : ∀ i : Fin 154,
    packedDot 2 (secondRowCode i.val) (stageCode 4) 154 % 3=
      packedDigit 2 (stageCode 5) i.val % 3 := by decide +kernel

private theorem step_4 : CFSG.Models.MatrixData.matrix 3 154 rows2 *ᵥ
    stageVector 4=stageVector 5 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 3 154 2 rows2 i
    (secondRowCode i.val) (stageCode 4) (stageCode 5)
    (fun j => CFSGONPrimeElevenSecondTransposeRows.binding i j) (check_4 i)

private theorem check_5 : ∀ i : Fin 154,
    packedDot 2 (firstRowCode i.val) (stageCode 5) 154 % 3=
      packedDigit 2 (stageCode 6) i.val % 3 := by decide +kernel

private theorem step_5 : CFSG.Models.MatrixData.matrix 3 154 rows1 *ᵥ
    stageVector 5=stageVector 6 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 3 154 2 rows1 i
    (firstRowCode i.val) (stageCode 5) (stageCode 6)
    (fun j => CFSGONPrimeElevenFirstTransposeRows.binding i j) (check_5 i)

private theorem check_6 : ∀ i : Fin 154,
    packedDot 2 (secondRowCode i.val) (stageCode 6) 154 % 3=
      packedDigit 2 (stageCode 7) i.val % 3 := by decide +kernel

private theorem step_6 : CFSG.Models.MatrixData.matrix 3 154 rows2 *ᵥ
    stageVector 6=stageVector 7 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 3 154 2 rows2 i
    (secondRowCode i.val) (stageCode 6) (stageCode 7)
    (fun j => CFSGONPrimeElevenSecondTransposeRows.binding i j) (check_6 i)

private theorem check_7 : ∀ i : Fin 154,
    packedDot 2 (firstRowCode i.val) (stageCode 7) 154 % 3=
      packedDigit 2 (stageCode 8) i.val % 3 := by decide +kernel

private theorem step_7 : CFSG.Models.MatrixData.matrix 3 154 rows1 *ᵥ
    stageVector 7=stageVector 8 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 3 154 2 rows1 i
    (firstRowCode i.val) (stageCode 7) (stageCode 8)
    (fun j => CFSGONPrimeElevenFirstTransposeRows.binding i j) (check_7 i)

private theorem check_8 : ∀ i : Fin 154,
    packedDot 2 (secondRowCode i.val) (stageCode 8) 154 % 3=
      packedDigit 2 (stageCode 9) i.val % 3 := by decide +kernel

private theorem step_8 : CFSG.Models.MatrixData.matrix 3 154 rows2 *ᵥ
    stageVector 8=stageVector 9 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 3 154 2 rows2 i
    (secondRowCode i.val) (stageCode 8) (stageCode 9)
    (fun j => CFSGONPrimeElevenSecondTransposeRows.binding i j) (check_8 i)

private theorem check_9 : ∀ i : Fin 154,
    packedDot 2 (firstRowCode i.val) (stageCode 9) 154 % 3=
      packedDigit 2 (stageCode 10) i.val % 3 := by decide +kernel

private theorem step_9 : CFSG.Models.MatrixData.matrix 3 154 rows1 *ᵥ
    stageVector 9=stageVector 10 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 3 154 2 rows1 i
    (firstRowCode i.val) (stageCode 9) (stageCode 10)
    (fun j => CFSGONPrimeElevenFirstTransposeRows.binding i j) (check_9 i)

private theorem check_10 : ∀ i : Fin 154,
    packedDot 2 (secondRowCode i.val) (stageCode 10) 154 % 3=
      packedDigit 2 (stageCode 11) i.val % 3 := by decide +kernel

private theorem step_10 : CFSG.Models.MatrixData.matrix 3 154 rows2 *ᵥ
    stageVector 10=stageVector 11 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 3 154 2 rows2 i
    (secondRowCode i.val) (stageCode 10) (stageCode 11)
    (fun j => CFSGONPrimeElevenSecondTransposeRows.binding i j) (check_10 i)

private theorem check_11 : ∀ i : Fin 154,
    packedDot 2 (firstRowCode i.val) (stageCode 11) 154 % 3=
      packedDigit 2 (stageCode 12) i.val % 3 := by decide +kernel

private theorem step_11 : CFSG.Models.MatrixData.matrix 3 154 rows1 *ᵥ
    stageVector 11=stageVector 12 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 3 154 2 rows1 i
    (firstRowCode i.val) (stageCode 11) (stageCode 12)
    (fun j => CFSGONPrimeElevenFirstTransposeRows.binding i j) (check_11 i)

private theorem check_12 : ∀ i : Fin 154,
    packedDot 2 (secondRowCode i.val) (stageCode 12) 154 % 3=
      packedDigit 2 (stageCode 13) i.val % 3 := by decide +kernel

private theorem step_12 : CFSG.Models.MatrixData.matrix 3 154 rows2 *ᵥ
    stageVector 12=stageVector 13 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 3 154 2 rows2 i
    (secondRowCode i.val) (stageCode 12) (stageCode 13)
    (fun j => CFSGONPrimeElevenSecondTransposeRows.binding i j) (check_12 i)

private theorem check_13 : ∀ i : Fin 154,
    packedDot 2 (firstRowCode i.val) (stageCode 13) 154 % 3=
      packedDigit 2 (stageCode 14) i.val % 3 := by decide +kernel

private theorem step_13 : CFSG.Models.MatrixData.matrix 3 154 rows1 *ᵥ
    stageVector 13=stageVector 14 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 3 154 2 rows1 i
    (firstRowCode i.val) (stageCode 13) (stageCode 14)
    (fun j => CFSGONPrimeElevenFirstTransposeRows.binding i j) (check_13 i)

private theorem check_14 : ∀ i : Fin 154,
    packedDot 2 (secondRowCode i.val) (stageCode 14) 154 % 3=
      packedDigit 2 (stageCode 15) i.val % 3 := by decide +kernel

private theorem step_14 : CFSG.Models.MatrixData.matrix 3 154 rows2 *ᵥ
    stageVector 14=stageVector 15 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 3 154 2 rows2 i
    (secondRowCode i.val) (stageCode 14) (stageCode 15)
    (fun j => CFSGONPrimeElevenSecondTransposeRows.binding i j) (check_14 i)

private theorem check_15 : ∀ i : Fin 154,
    packedDot 2 (firstRowCode i.val) (stageCode 15) 154 % 3=
      packedDigit 2 (stageCode 16) i.val % 3 := by decide +kernel

private theorem step_15 : CFSG.Models.MatrixData.matrix 3 154 rows1 *ᵥ
    stageVector 15=stageVector 16 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 3 154 2 rows1 i
    (firstRowCode i.val) (stageCode 15) (stageCode 16)
    (fun j => CFSGONPrimeElevenFirstTransposeRows.binding i j) (check_15 i)

private theorem check_16 : ∀ i : Fin 154,
    packedDot 2 (secondRowCode i.val) (stageCode 16) 154 % 3=
      packedDigit 2 (stageCode 17) i.val % 3 := by decide +kernel

private theorem step_16 : CFSG.Models.MatrixData.matrix 3 154 rows2 *ᵥ
    stageVector 16=stageVector 17 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 3 154 2 rows2 i
    (secondRowCode i.val) (stageCode 16) (stageCode 17)
    (fun j => CFSGONPrimeElevenSecondTransposeRows.binding i j) (check_16 i)

private theorem check_17 : ∀ i : Fin 154,
    packedDot 2 (firstRowCode i.val) (stageCode 17) 154 % 3=
      packedDigit 2 (stageCode 18) i.val % 3 := by decide +kernel

private theorem step_17 : CFSG.Models.MatrixData.matrix 3 154 rows1 *ᵥ
    stageVector 17=stageVector 18 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 3 154 2 rows1 i
    (firstRowCode i.val) (stageCode 17) (stageCode 18)
    (fun j => CFSGONPrimeElevenFirstTransposeRows.binding i j) (check_17 i)

private theorem check_18 : ∀ i : Fin 154,
    packedDot 2 (secondRowCode i.val) (stageCode 18) 154 % 3=
      packedDigit 2 (stageCode 19) i.val % 3 := by decide +kernel

private theorem step_18 : CFSG.Models.MatrixData.matrix 3 154 rows2 *ᵥ
    stageVector 18=stageVector 19 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 3 154 2 rows2 i
    (secondRowCode i.val) (stageCode 18) (stageCode 19)
    (fun j => CFSGONPrimeElevenSecondTransposeRows.binding i j) (check_18 i)

private theorem check_19 : ∀ i : Fin 154,
    packedDot 2 (firstRowCode i.val) (stageCode 19) 154 % 3=
      packedDigit 2 (stageCode 20) i.val % 3 := by decide +kernel

private theorem step_19 : CFSG.Models.MatrixData.matrix 3 154 rows1 *ᵥ
    stageVector 19=stageVector 20 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 3 154 2 rows1 i
    (firstRowCode i.val) (stageCode 19) (stageCode 20)
    (fun j => CFSGONPrimeElevenFirstTransposeRows.binding i j) (check_19 i)

private theorem check_20 : ∀ i : Fin 154,
    packedDot 2 (secondRowCode i.val) (stageCode 20) 154 % 3=
      packedDigit 2 (stageCode 21) i.val % 3 := by decide +kernel

private theorem step_20 : CFSG.Models.MatrixData.matrix 3 154 rows2 *ᵥ
    stageVector 20=stageVector 21 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 3 154 2 rows2 i
    (secondRowCode i.val) (stageCode 20) (stageCode 21)
    (fun j => CFSGONPrimeElevenSecondTransposeRows.binding i j) (check_20 i)

private theorem check_21 : ∀ i : Fin 154,
    packedDot 2 (firstRowCode i.val) (stageCode 21) 154 % 3=
      packedDigit 2 (stageCode 22) i.val % 3 := by decide +kernel

private theorem step_21 : CFSG.Models.MatrixData.matrix 3 154 rows1 *ᵥ
    stageVector 21=stageVector 22 := by
  funext i
  exact MatrixModelSelectedRowVectorReflection.coordinate_step 3 154 2 rows1 i
    (firstRowCode i.val) (stageCode 21) (stageCode 22)
    (fun j => CFSGONPrimeElevenFirstTransposeRows.binding i j) (check_21 i)

private theorem phase_0 (i : Fin 11) :
    CFSG.Models.MatrixData.matrix 3 154 rows2 *ᵥ stageVector (2*i.val+0)=
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

private theorem phase_1 (i : Fin 11) :
    CFSG.Models.MatrixData.matrix 3 154 rows1 *ᵥ stageVector (2*i.val+1)=
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

theorem word_step (i : Fin 11) : selectedEnd (vectors i.castSucc)=vectors i.succ := by
  rw [selectedEnd_apply]
  change (CFSG.Models.MatrixData.matrix 3 154 rows1 *ᵥ (CFSG.Models.MatrixData.matrix 3 154 rows2 *ᵥ stageVector (2*i.val+0)))=stageVector (2*(i.val+1))
  rw [phase_0,phase_1]
  exact congrArg stageVector (by omega)

set_option maxRecDepth 4096 in
theorem selected_return : (selectedEnd^11) (vectors 0)=vectors 0 := by
  have hp := LinearMapSelectedKrylovPeriod.pow_apply_eq_vector selectedEnd 11 vectors
    word_step (Fin.last 11)
  have he : vectors (Fin.last 11)=vectors 0 := by
    funext j
    change (packedDigit 2 (stageCode 22) j.val : ZMod 3)=
      (packedDigit 2 (stageCode 0) j.val : ZMod 3)
    rfl
  exact hp.trans he

set_option maxRecDepth 4096 in
theorem selected_moved : selectedEnd (vectors 0)≠vectors 0 := by
  intro he
  have hn : vectors 1 (0 : Fin 154)≠vectors 0 (0 : Fin 154) := by decide +kernel
  exact hn (congrArg (fun v : CFSGONPrimeElevenPackedData.V => v (0 : Fin 154)) ((word_step 0).symm.trans he))

attribute [local irreducible] selectedEnd CFSG.Models.MatrixData.matrix
  CFSG.Models.MatrixData.generators rows1 rows2
  MatrixModelSelectedPositiveWordPrimePeriod.wordEnd

set_option maxRecDepth 4096 in
theorem eleven_dvd_card (hn : ¬IsMulCommutative Model) : 11 ∣ Nat.card Model := by
  apply MatrixModelSelectedPositiveWordPrimePeriod.prime_dvd_card 3 154 rows1 rows2 actualWord
    11 (by decide) (vectors 0)
  · rw [wordEnd_binding]
    exact selected_return
  · rw [wordEnd_binding]
    exact selected_moved
  · exact hn

end SymmetricSubgroupAsymptotics.CFSGONSelectedProductPrimeEleven
