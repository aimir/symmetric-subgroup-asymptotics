import SymmetricSubgroupAsymptotics.CFSGTrialityBinaryShortWeylTensorRoots
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleOrderedTensor
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleTensorCovariance
import SymmetricSubgroupAsymptotics.CFSGGradedMatrixBlockProjection

/-! The actual outer-three Weyl word acts on the middle coefficient
cube by complement. In characteristic two the literal integral tensor
signs vanish, so it takes the fully raised tensor to the zero vertex. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityBinaryShortWeylTensorAction
open CFSGTrialityD4NormTwo CFSGTrialityD4MiddleCube CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckMiddleFirstLayer CFSGTrialityGeckMiddleCubeCoordinates
open CFSGTrialityGeckMiddleOrderedTensor CFSGTrialityGeckMiddleSignedTensorBasis
open CFSGTrialityGeckMiddleTensorCovariance CFSGTrialityBinaryShortWeylTensorRoots
open CFSGGradedMatrixGroupFirstLayer CFSGGradedMatrixBlockProjection
open CFSGGradedMatrixSubgroups CFSGSerreQuadraticWeylWord
local instance trialityWeylTensorActionRootsDecidableEq :
    DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) := Classical.decEq _
local notation "A" => CartanMatrix.D 4
local notation "hd" => CartanMatrix.D_diag 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite
local notation "ho" => CartanMatrix.D_off_diag_nonpos 4
private abbrev U (K : Type) [CommRing K] := (Mat K)ˣ
private abbrev W (K : Type) [Field K] : U K := canonicalWord rawData K [0,2,3]

theorem short_word_coefficient (K : Type) [Field K] [CharP K 2] (a : Cube) :
    CFSGAlgebraConjugationAction.action K (Mat K) (W K) (cubeCoefficient K a)=
      cubeCoefficient K (flip a) := by
  let u : U K := CFSGNormTwoCoordinateSelectedRootElement.selectedRootElement
    A hd hs hp ho K (cubeRoot a) 1
  have h := congrArg (firstLayer middleWeight)
    (short_word_conjugate_parameter K a (1 : K))
  change firstLayer middleWeight (W K*u*(W K)⁻¹)=firstLayer middleWeight
    (CFSGNormTwoCoordinateSelectedRootElement.selectedRootElement
      A hd hs hp ho K (cubeRoot (flip a)) 1) at h
  have hW := short_word_preserving K
  rw [firstLayer_conjugate K middleWeight (W K) u hW
    ((preservingUnits middleWeight).inv_mem hW)] at h
  have hu : firstLayer middleWeight u=cubeCoefficient K a :=
    (root_firstLayer K (cubeRoot a) (cubeRoot_middle a) 1).trans (one_smul K _)
  have hv : firstLayer middleWeight
      (CFSGNormTwoCoordinateSelectedRootElement.selectedRootElement
        A hd hs hp ho K (cubeRoot (flip a)) 1)=cubeCoefficient K (flip a) :=
    (root_firstLayer K (cubeRoot (flip a)) (cubeRoot_middle (flip a)) 1).trans
      (one_smul K _)
  exact (congrArg (fun T : Mat K => (W K).val*T*((W K)⁻¹).val) hu.symm).trans
    (h.trans hv)

private theorem actualTensor_binary (K : Type) [Field K] [CharP K 2] (i : Fin 8) :
    actualTensor K i=cubeCoefficient K (cubeBits i) := by
  rw [actualTensor,tensorWord_eq]
  obtain ⟨epsilon,hepsilon,hvalue⟩ := tensorBasis_unit_sign (cubeBits i)
  rw [hvalue K]
  rcases hepsilon with rfl | rfl <;>
    simp only [Int.cast_one,Int.cast_neg,CharTwo.neg_eq,one_smul]

theorem short_word_raised (K : Type) [Field K] [CharP K 2] :
    CFSGAlgebraConjugationAction.action K (Mat K) (W K) (actualTensor K 7)=
      actualTensor K 0 := by
  rw [actualTensor_binary,actualTensor_binary,short_word_coefficient]
  have hf : flip (cubeBits 7)=cubeBits 0 := by decide
  rw [hf]

end SymmetricSubgroupAsymptotics.CFSGTrialityBinaryShortWeylTensorAction
