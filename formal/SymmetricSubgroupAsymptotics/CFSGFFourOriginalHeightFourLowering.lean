import SymmetricSubgroupAsymptotics.CFSGFFourOriginalHeightFourRaising

/-! All opposite simple lowerings on the three displayed original
height-four paths. Their values lie in the height-three source family
with integer coefficients. This is a Jacobi/weight calculation in the
original quotient, before any base change. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourOriginalHeightFourLowering
open CFSG.Models.Chevalley CFSGSerreSignedRootWeights CFSGSerreRootLoweringComparison
open CFSGFFourOriginalFiftyTwoFamily CFSGFFourOriginalHeightThreeImages
open CFSGFFourOriginalHeightThreeLowering CFSGFFourOriginalHeightThreeRaising
open CFSGFFourOriginalFirstLoweringComparison CFSGFFourOriginalHeightFourRaising
local notation "A" => CartanMatrix.F₄
local notation "L" => RationalLie A

private theorem weight_eight : ∀i:Fin 4,simpleWeight i 8=(![-2,2,0,-1]:Fin 4→ℤ) i :=
  by decide +kernel
private theorem weight_nine : ∀i:Fin 4,simpleWeight i 9=(![1,-1,1,-1]:Fin 4→ℤ) i :=
  by decide +kernel

theorem opposite_ten (neg:Bool) (i:Fin 4) :
    ⁅oppositeVector A neg i,(rootVectors neg 10).val⁆=
      (![0,-(rootVectors neg 7).val,0,(rootVectors neg 8).val]:Fin 4→L) i := by
  rw [path_ten]
  have h:=opposite_raising A neg 3 i (rootVectors neg 8).val
    (simpleWeight i 8:ℚ) (rootVectors_weight neg i 8)
  rw [opposite_eight,weight_eight] at h
  fin_cases i
  · change ⁅oppositeVector A neg 0,⁅rootVector A neg 3,(rootVectors neg 8).val⁆⁆=
      0+⁅rootVector A neg 3,(0:L)⁆ at h
    simpa only [lie_zero,zero_add] using h
  · change ⁅oppositeVector A neg 1,⁅rootVector A neg 3,(rootVectors neg 8).val⁆⁆=
      0+⁅rootVector A neg 3,-(rootVectors neg 5).val⁆ at h
    simpa only [zero_add,lie_neg,←path_seven] using h
  · change ⁅oppositeVector A neg 2,⁅rootVector A neg 3,(rootVectors neg 8).val⁆⁆=
      0+⁅rootVector A neg 3,(0:L)⁆ at h
    simpa only [lie_zero,zero_add] using h
  · change ⁅oppositeVector A neg 3,⁅rootVector A neg 3,(rootVectors neg 8).val⁆⁆=
      -((-1:ℚ) • (rootVectors neg 8).val)+⁅rootVector A neg 3,(0:L)⁆ at h
    simpa only [lie_zero,add_zero,neg_one_smul,neg_neg] using h

theorem opposite_eleven (neg:Bool) (i:Fin 4) :
    ⁅oppositeVector A neg i,(rootVectors neg 11).val⁆=
      (![-(rootVectors neg 7).val,0,0,(rootVectors neg 9).val]:Fin 4→L) i := by
  rw [path_eleven]
  have h:=opposite_raising A neg 3 i (rootVectors neg 9).val
    (simpleWeight i 9:ℚ) (rootVectors_weight neg i 9)
  rw [opposite_nine,weight_nine] at h
  have h6:⁅rootVector A neg 3,(rootVectors neg 6).val⁆=0:=raising_six neg 3
  fin_cases i
  · change ⁅oppositeVector A neg 0,⁅rootVector A neg 3,(rootVectors neg 9).val⁆⁆=
      0+⁅rootVector A neg 3,-(rootVectors neg 5).val⁆ at h
    simpa only [zero_add,lie_neg,←path_seven] using h
  · change ⁅oppositeVector A neg 1,⁅rootVector A neg 3,(rootVectors neg 9).val⁆⁆=
      0+⁅rootVector A neg 3,(0:L)⁆ at h
    simpa only [lie_zero,zero_add] using h
  · change ⁅oppositeVector A neg 2,⁅rootVector A neg 3,(rootVectors neg 9).val⁆⁆=
      0+⁅rootVector A neg 3,(rootVectors neg 6).val⁆ at h
    simpa only [h6,zero_add] using h
  · change ⁅oppositeVector A neg 3,⁅rootVector A neg 3,(rootVectors neg 9).val⁆⁆=
      -((-1:ℚ) • (rootVectors neg 9).val)+⁅rootVector A neg 3,(0:L)⁆ at h
    simpa only [lie_zero,add_zero,neg_one_smul,neg_neg] using h

theorem opposite_twelve (neg:Bool) (i:Fin 4) :
    ⁅oppositeVector A neg i,(rootVectors neg 12).val⁆=
      (![(2:ℚ) • (rootVectors neg 8).val,(rootVectors neg 9).val,0,0]:Fin 4→L) i := by
  rw [path_twelve]
  have h:=opposite_raising A neg 0 i (rootVectors neg 8).val
    (simpleWeight i 8:ℚ) (rootVectors_weight neg i 8)
  rw [opposite_eight,weight_eight] at h
  have h5:⁅rootVector A neg 0,(rootVectors neg 5).val⁆= -(rootVectors neg 9).val:=
    raising_five neg 0
  fin_cases i
  · change ⁅oppositeVector A neg 0,⁅rootVector A neg 0,(rootVectors neg 8).val⁆⁆=
      -((-2:ℚ) • (rootVectors neg 8).val)+⁅rootVector A neg 0,(0:L)⁆ at h
    simpa only [lie_zero,add_zero,neg_smul,neg_neg] using h
  · change ⁅oppositeVector A neg 1,⁅rootVector A neg 0,(rootVectors neg 8).val⁆⁆=
      0+⁅rootVector A neg 0,-(rootVectors neg 5).val⁆ at h
    simpa only [zero_add,lie_neg,h5,neg_neg] using h
  · change ⁅oppositeVector A neg 2,⁅rootVector A neg 0,(rootVectors neg 8).val⁆⁆=
      0+⁅rootVector A neg 0,(0:L)⁆ at h
    simpa only [lie_zero,zero_add] using h
  · change ⁅oppositeVector A neg 3,⁅rootVector A neg 0,(rootVectors neg 8).val⁆⁆=
      0+⁅rootVector A neg 0,(0:L)⁆ at h
    simpa only [lie_zero,zero_add] using h

end SymmetricSubgroupAsymptotics.CFSGFFourOriginalHeightFourLowering
