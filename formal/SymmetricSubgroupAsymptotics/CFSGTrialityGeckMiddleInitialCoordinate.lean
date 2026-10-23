import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleLayerCoordinates
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateLeadingFactor

/-! The first TOTAL-height projection reads exactly the initial middle
cube coordinate. All seven raised tensor words have greater literal
integer height, even in small characteristic. Thus vanishing of the
original simple leading layer forces that initial coordinate to vanish. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleInitialCoordinate
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance CFSGTrialityD4MiddleCube
open CFSGTrialityGeckMiddleFirstLayer CFSGTrialityGeckMiddleCubeCoordinates
open CFSGTrialityGeckMiddleSignedTensorBasis CFSGTrialityGeckMiddleOrderedTensor
open CFSGTrialityGeckMiddleTensorCovariance CFSGTrialityGeckMiddleLayerCoordinates
open CFSGNormTwoCoordinateRootHeightLeading CFSGNormTwoCoordinateRootBracketTransport
open CFSGGradedMatrixSingleDegreeSpan CFSGGradedMatrixGroupFirstLayer CFSGGradedMatrixLieFirstLayer
local notation "A" => CartanMatrix.D 4
local notation "hd" => CartanMatrix.D_diag 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite
local notation "ho" => CartanMatrix.D_off_diag_nonpos 4
local notation "w" => heightWeight A hd hs hp ho
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots A) := Classical.decEq _
local instance : DecidableEq GeckIndex := inferInstance

private theorem firstParts_commute (K : Type) [Field K] (w1 w2 : GeckIndex → ℤ) (M : Mat K) :
    firstPart w1 (firstPart w2 M) = firstPart w2 (firstPart w1 M) := by
  apply Matrix.ext
  intro i j
  by_cases h1 : w1 i = w1 j + 1 <;> by_cases h2 : w2 i = w2 j + 1 <;>
    simp only [firstPart_apply, h1, h2, if_true, if_false]

private theorem cube_height_zero :
    CFSGIntegerHeightSign.height (cubeRoot zeroCube).val = 1 := by decide

private theorem cube_height_other : ∀ i : Fin 8, i ≠ 0 →
    (1 : ℤ) ≠ CFSGIntegerHeightSign.height (cubeRoot (cubeBits i)).val := by decide

theorem heightPart_actualTensor (K : Type) [Field K] (i : Fin 8) :
    firstPart w (actualTensor K i) = if i=0 then cubeCoefficient K zeroCube else 0 := by
  by_cases hi : i=0
  · subst i
    rw [if_pos rfl]
    change degreePart w 1 (cubeCoefficient K zeroCube) = cubeCoefficient K zeroCube
    have hsup := first_height_support A hd hs hp ho K (cubeRoot zeroCube)
    rw [cube_height_zero] at hsup
    exact degreePart_eq _ _ _ hsup
  · rw [if_neg hi]
    rw [show actualTensor K i = tensorBasis K (cubeBits i) from tensorWord_eq K i]
    obtain ⟨epsilon,_,hvalue⟩ := tensorBasis_unit_sign (cubeBits i)
    rw [hvalue K,map_smul]
    have hz : firstPart w (cubeCoefficient K (cubeBits i)) = 0 :=
      degreePart_zero_of_other _ 1 _ _ (first_height_support A hd hs hp ho K (cubeRoot (cubeBits i)))
        (cube_height_other i hi)
    rw [hz,smul_zero]

theorem heightPart_tensorCoordinates (K : Type) [Field K] (c : Fin 8 → K) :
    firstPart w (tensorCoordinates K c) = c 0 • cubeCoefficient K zeroCube := by
  change firstPart w (∑ i : Fin 8, c i • actualTensor K i) = _
  rw [map_sum]
  calc
    _ = ∑ i : Fin 8, if i=0 then c 0 • cubeCoefficient K zeroCube else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul,heightPart_actualTensor]
      by_cases hi : i=0
      · subst i
        simp only [if_true]
      · simp only [if_neg hi,smul_zero]
    _ = _ := by simp

theorem initial_coordinate_zero (K : Type) [Field K] (u : CFSGTrialityGeckMiddleRadicalQuotient.Raw K)
    (c : Fin 8 → K) (hc : firstLayer middleWeight u = tensorCoordinates K c)
    (hheight : firstLayer w u = 0) : c 0 = 0 := by
  have he := congrArg (firstPart w) hc
  rw [heightPart_tensorCoordinates] at he
  have hz : firstPart w (firstLayer middleWeight u) = 0 := by
    let M : Mat K := u.val - (1 : Mat K)
    change firstPart w (firstPart middleWeight M) = 0
    have hh : firstPart w M = 0 := hheight
    exact (firstParts_commute K w middleWeight M).trans
      ((congrArg (firstPart middleWeight) hh).trans (map_zero _))
  rw [hz] at he
  have hnonzero : cubeCoefficient K zeroCube ≠ 0 :=
    selectedFieldCoefficient_ne_zero A hd hs hp ho K (cubeRoot zeroCube)
  exact (smul_eq_zero.mp he.symm).resolve_right hnonzero

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleInitialCoordinate
