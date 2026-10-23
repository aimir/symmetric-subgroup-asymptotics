import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleTwistOperators
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateDiagramIndices

/-! Triality preserves the literal middle-coordinate grading, so its
matrix-field twist commutes with the first-layer projection. In
particular a fixed actual radical word has a fixed first coefficient.
No lifting from fixed quotient points is used. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleFixedLayer
open CFSGTrialityGeckDiagramCovariance CFSGTrialityGeckMiddleFirstLayer
open CFSGTrialityGeckMiddleCubeEdges CFSGTrialityGeckMiddleTwistOperators
open CFSGTrialityGeckMatrixTwist CFSGGradedMatrixGroupFirstLayer CFSGGradedMatrixLieFirstLayer
open CFSGNormTwoCoordinateDiagramIndices CFSGNormTwoCartanDiagramRoots
open CFSGTrialityD4NormTwo CFSGNormTwoGeckLatticeDegree CFSGSerreDiagram
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) := Classical.decEq _
local instance : DecidableEq GeckIndex := inferInstance

theorem middleWeight_triality (i : GeckIndex) :
    middleWeight (trialityIndex i) = middleWeight i := by
  rcases i with i | k
  · rfl
  · change k.val (trialityPermutation.symm 1) = k.val 1
    have h1 : trialityPermutation.symm 1 = 1 := by
      apply trialityPermutation.injective
      rw [Equiv.apply_symm_apply]
      change (1 : Fin 4) = trialityPermutation 1
      rfl
    rw [h1]

private theorem middleWeight_triality_symm (i : GeckIndex) :
    middleWeight (trialityIndex.symm i) = middleWeight i := by
  simpa only [Equiv.apply_symm_apply] using (middleWeight_triality (trialityIndex.symm i)).symm

theorem matrixTwist_firstPart (K : Type) [Field K] (sigma : K ≃+* K) (M : Mat K) :
    matrixTwist K sigma (firstPart middleWeight M) =
      firstPart middleWeight (matrixTwist K sigma M) := by
  apply Matrix.ext
  intro i j
  change sigma (if middleWeight (trialityIndex.symm i) =
      middleWeight (trialityIndex.symm j) + 1 then
        M (trialityIndex.symm i) (trialityIndex.symm j) else 0) =
    if middleWeight i = middleWeight j + 1 then
      sigma (M (trialityIndex.symm i) (trialityIndex.symm j)) else 0
  rw [middleWeight_triality_symm, middleWeight_triality_symm]
  by_cases hij : middleWeight i = middleWeight j + 1
  · simp only [if_pos hij]
  · simp only [if_neg hij, map_zero]

theorem matrixTwist_firstLayer (K : Type) [Field K] (sigma : K ≃+* K) (u : UnitsD4 K) :
    matrixTwist K sigma (firstLayer middleWeight u) =
      firstLayer middleWeight (unitTwist K sigma u) := by
  change matrixTwist K sigma (firstPart middleWeight (u.val - 1)) =
    firstPart middleWeight ((unitTwist K sigma u).val - 1)
  rw [matrixTwist_firstPart, map_sub, map_one]
  rfl

theorem fixed_word_firstLayer (K : Type) [Field K] (sigma : K ≃+* K) (u : UnitsD4 K)
    (hu : unitTwist K sigma u = u) :
    matrixTwist K sigma (firstLayer middleWeight u) = firstLayer middleWeight u := by
  rw [matrixTwist_firstLayer, hu]

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleFixedLayer
