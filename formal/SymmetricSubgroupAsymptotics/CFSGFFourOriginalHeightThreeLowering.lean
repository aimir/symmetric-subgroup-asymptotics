import SymmetricSubgroupAsymptotics.CFSGFFourOriginalHeightThreeImages
import SymmetricSubgroupAsymptotics.CFSGSerreRootLoweringComparison
import SymmetricSubgroupAsymptotics.CFSGSerreCrossNodeCommutation

/-! All twelve opposite simple lowerings on the three height-three
original F4 paths. Each result is an integral combination of displayed
height-two paths. The proofs use original Jacobi/Serre relations and the
normalized middle string; no matrix-to-source inference is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourOriginalHeightThreeLowering
open CFSG.Models.Chevalley CFSGSerreSignedRootWeights CFSGSerreSimpleBracketLowering
open CFSGFFourOriginalFiftyTwoFamily CFSGFFourOriginalHeightTwoSpan
open CFSGFFourOriginalHeightThreeImages CFSGFFourOriginalMiddleSerreStrings
open CFSGFFourOriginalMiddleLowering CFSGSerreRootLoweringComparison
open CFSGSerreCrossNodeCommutation
local notation "A" => CartanMatrix.F₄
local notation "L" => RationalLie A

private theorem weight_five : ∀i:Fin 4,simpleWeight i 5=(![-1,0,1,-1]:Fin 4→ℤ) i :=
  by decide +kernel

private theorem weight_six : ∀i:Fin 4,simpleWeight i 6=(![1,1,-1,0]:Fin 4→ℤ) i :=
  by decide +kernel

theorem opposite_seven (neg:Bool) (i:Fin 4) :
    ⁅oppositeVector A neg i,(rootVectors neg 7).val⁆=
      (![0,(-2:ℚ) • (rootVectors neg 4).val,0,(rootVectors neg 5).val]:Fin 4→L) i := by
  rw [path_seven]
  have hl:⁅oppositeVector A neg i,(rootVectors neg 5).val⁆=
      (if i=2 then -(A 2 1:ℚ) • rootVector A neg 1 else 0)+
      (if i=1 then (A 1 2:ℚ) • rootVector A neg 2 else 0) := by
    rw [path_five]
    exact opposite_simple_bracket A neg i 2 1
  have h:=opposite_raising A neg 3 i (rootVectors neg 5).val
    (simpleWeight i 5:ℚ) (rootVectors_weight neg i 5)
  rw [hl,weight_five] at h
  have h31:⁅rootVector A neg 3,rootVector A neg 1⁆=0:=
    rootVector_lie_zero_of_cartan_zero A neg 3 1 (by decide)
  fin_cases i
  · change ⁅oppositeVector A neg 0,⁅rootVector A neg 3,(rootVectors neg 5).val⁆⁆=
      0+⁅rootVector A neg 3,(0:L)+0⁆ at h
    simpa only [zero_add,lie_zero] using h
  · change ⁅oppositeVector A neg 1,⁅rootVector A neg 3,(rootVectors neg 5).val⁆⁆=
      0+⁅rootVector A neg 3,0+(-2:ℚ) • rootVector A neg 2⁆ at h
    simpa only [zero_add,lie_smul,←path_four] using h
  · change ⁅oppositeVector A neg 2,⁅rootVector A neg 3,(rootVectors neg 5).val⁆⁆=
      0+⁅rootVector A neg 3,(1:ℚ) • rootVector A neg 1+0⁆ at h
    simpa only [zero_add,add_zero,one_smul,h31] using h
  · change ⁅oppositeVector A neg 3,⁅rootVector A neg 3,(rootVectors neg 5).val⁆⁆=
      -((-1:ℚ) • (rootVectors neg 5).val)+⁅rootVector A neg 3,(0:L)+0⁆ at h
    simpa only [neg_one_smul,neg_neg,zero_add,lie_zero,add_zero] using h

private theorem outer_lower_middle_two (neg:Bool) (i:Fin 4) (hi1:i≠1) (hi2:i≠2) :
    ⁅oppositeVector A neg i,stringVector neg 2⁆=0 := by
  have h1:⁅oppositeVector A neg i,shortVector neg⁆=0:=opposite_distinct A neg i 1 hi1
  have h2:⁅oppositeVector A neg i,longVector neg⁆=0:=opposite_distinct A neg i 2 hi2
  have hinner:⁅oppositeVector A neg i,⁅shortVector neg,longVector neg⁆⁆=0 := by
    rw [leibniz_lie,h1,h2,zero_lie,lie_zero,add_zero]
  rw [string_two,lie_smul,leibniz_lie,h1,hinner,zero_lie,lie_zero,add_zero,smul_zero]

theorem opposite_eight (neg:Bool) (i:Fin 4) :
    ⁅oppositeVector A neg i,(rootVectors neg 8).val⁆=
      (![0,-(rootVectors neg 5).val,0,0]:Fin 4→L) i := by
  fin_cases i
  · change ⁅oppositeVector A neg 0,stringVector neg 2⁆=0
    exact outer_lower_middle_two neg 0 (by decide) (by decide)
  · change ⁅oppositeVector A neg 1,(rootVectors neg 8).val⁆= -(rootVectors neg 5).val
    exact lower_eight neg
  · change ⁅oppositeVector A neg 2,stringVector neg 2⁆=0
    exact opposite_long_string_two neg
  · change ⁅oppositeVector A neg 3,stringVector neg 2⁆=0
    exact outer_lower_middle_two neg 3 (by decide) (by decide)

theorem opposite_nine (neg:Bool) (i:Fin 4) :
    ⁅oppositeVector A neg i,(rootVectors neg 9).val⁆=
      (![-(rootVectors neg 5).val,0,(rootVectors neg 6).val,0]:Fin 4→L) i := by
  rw [path_nine]
  have hl:⁅oppositeVector A neg i,(rootVectors neg 6).val⁆=
      (if i=1 then -(A 1 0:ℚ) • rootVector A neg 0 else 0)+
      (if i=0 then (A 0 1:ℚ) • rootVector A neg 1 else 0) := by
    rw [path_six]
    exact opposite_simple_bracket A neg i 1 0
  have h:=opposite_raising A neg 2 i (rootVectors neg 6).val
    (simpleWeight i 6:ℚ) (rootVectors_weight neg i 6)
  rw [hl,weight_six] at h
  have h20:⁅rootVector A neg 2,rootVector A neg 0⁆=0:=
    rootVector_lie_zero_of_cartan_zero A neg 2 0 (by decide)
  fin_cases i
  · change ⁅oppositeVector A neg 0,⁅rootVector A neg 2,(rootVectors neg 6).val⁆⁆=
      0+⁅rootVector A neg 2,0+(-1:ℚ) • rootVector A neg 1⁆ at h
    simpa only [zero_add,lie_smul,neg_one_smul,lie_neg,←path_five] using h
  · change ⁅oppositeVector A neg 1,⁅rootVector A neg 2,(rootVectors neg 6).val⁆⁆=
      0+⁅rootVector A neg 2,(1:ℚ) • rootVector A neg 0+0⁆ at h
    simpa only [zero_add,add_zero,one_smul,h20] using h
  · change ⁅oppositeVector A neg 2,⁅rootVector A neg 2,(rootVectors neg 6).val⁆⁆=
      -((-1:ℚ) • (rootVectors neg 6).val)+⁅rootVector A neg 2,(0:L)+0⁆ at h
    simpa only [neg_one_smul,neg_neg,zero_add,lie_zero,add_zero] using h
  · change ⁅oppositeVector A neg 3,⁅rootVector A neg 2,(rootVectors neg 6).val⁆⁆=
      0+⁅rootVector A neg 2,(0:L)+0⁆ at h
    simpa only [zero_add,lie_zero] using h

end SymmetricSubgroupAsymptotics.CFSGFFourOriginalHeightThreeLowering
