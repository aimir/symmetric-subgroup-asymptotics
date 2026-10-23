import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleCubeSpanActions
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckShortLowestCommutant
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticWeylConjugationTransport

/-! Literal diagram-field covariance for the three actual edge operators.
The initial coefficient is fixed by comparison with the ORIGINAL middle
simple root. Hence this is not a sign convention on an abstract cube. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleTwistOperators
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance CFSGSerreDiagram
open CFSGTrialityD4MiddleCube CFSGTrialityGeckMiddleFirstLayer
open CFSGTrialityGeckMiddleCubeCoordinates CFSGTrialityGeckMiddleCubeEdges
open CFSGTrialityGeckMiddleCubeLinearEdges CFSGTrialityGeckMiddleCubeEdgeOperators
open CFSGTrialityGeckMiddleSignedTensorBasis CFSGTrialityGeckMiddleCubeSpanActions
open CFSGTrialityGeckMatrixTwist CFSGTrialityGeckRootSubgroupTwist
open CFSGSerreQuadraticMatrix
open CFSGNormTwoCoordinateSimpleRootParametrization CFSGNormTwoCoordinateRootHeightLeading
open CFSGGradedMatrixGroupFirstLayer
local notation "A" => CartanMatrix.D 4
local notation "hd" => CartanMatrix.D_diag 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite
local notation "ho" => CartanMatrix.D_off_diag_nonpos 4
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots A) := Classical.decEq _
local instance : DecidableEq GeckIndex := inferInstance

def edgeCycle : Equiv.Perm (Fin 3) := Equiv.ofBijective (fun j => (![1,2,0] : Fin 3 → Fin 3) j)
  (by decide)

theorem outerNode_edgeCycle (j : Fin 3) :
    CFSGTrialityFixedWeylWords.outerNode (edgeCycle j) =
      trialityPermutation (CFSGTrialityFixedWeylWords.outerNode j) := by
  fin_cases j <;> rfl

theorem matrixTwist_smul (K : Type) [Field K] (sigma : K ≃+* K) (a : K) (M : Mat K) :
    matrixTwist K sigma (a • M) = sigma a • matrixTwist K sigma M := by
  apply Matrix.ext
  intro i j
  change sigma (a * M (trialityIndex.symm i) (trialityIndex.symm j)) =
    sigma a * sigma (M (trialityIndex.symm i) (trialityIndex.symm j))
  exact map_mul sigma _ _

theorem matrixTwist_action (K : Type) [Field K] (sigma : K ≃+* K)
    (u : UnitsD4 K) (M : Mat K) :
    matrixTwist K sigma (CFSGAlgebraConjugationAction.action K (Mat K) u M) =
      CFSGAlgebraConjugationAction.action K (Mat K) (unitTwist K sigma u)
        (matrixTwist K sigma M) := by
  change matrixTwist K sigma (u.val * M * (↑(u⁻¹) : Mat K)) =
    matrixTwist K sigma u.val * matrixTwist K sigma M *
      matrixTwist K sigma (↑(u⁻¹) : Mat K)
  rw [map_mul, map_mul]

theorem unitTwist_outerWord (K : Type) [Field K] (sigma : K ≃+* K) (j : Fin 3) (t : K) :
    unitTwist K sigma (outerWord K j t) = outerWord K (edgeCycle j) (sigma t) := by
  unfold outerWord
  rw [unitTwist_raw_root, outerNode_edgeCycle]

theorem matrixTwist_edgeShift (K : Type) [Field K] (sigma : K ≃+* K)
    (j : Fin 3) (M : Mat K) :
    matrixTwist K sigma (edgeShift K j M) =
      edgeShift K (edgeCycle j) (matrixTwist K sigma M) := by
  change matrixTwist K sigma (outerLinear K j 1 M - M) =
    outerLinear K (edgeCycle j) 1 (matrixTwist K sigma M) - matrixTwist K sigma M
  rw [map_sub]
  change matrixTwist K sigma (CFSGAlgebraConjugationAction.action K (Mat K)
      (outerWord K j 1) M) - matrixTwist K sigma M = _
  rw [matrixTwist_action, unitTwist_outerWord, map_one]
  rfl

theorem zeroCube_coefficient_sign : ∃ epsilon : ℤ, (epsilon = 1 ∨ epsilon = -1) ∧
    ∀ (K : Type) [Field K], cubeCoefficient K zeroCube =
      (epsilon : K) • fieldRoot rawData K false 1 := by
  obtain ⟨epsilon, hsign, hparam⟩ := selected_simple_root_sign A hd hs hp ho 1
  refine ⟨epsilon, hsign, ?_⟩
  intro K _
  have hroot : cubeRoot zeroCube = (Index 1 : CFSGNormTwoRootPairing.Roots A) := by
    apply Subtype.ext
    funext i
    fin_cases i <;> rfl
  have hword : cubeWord K zeroCube 1 = canonicalRoot rawData K false 1 (epsilon : K) := by
    change CFSGNormTwoCoordinateSelectedRootElement.selectedRootElement A hd hs hp ho K
      (cubeRoot zeroCube) 1 = _
    rw [hroot]
    simpa only [mul_one] using hparam K 1
  have hheight : CFSGIntegerHeightSign.height (cubeRoot zeroCube).val = 1 := by decide
  have hlead := (selected_root_cut_and_leading A hd hs hp ho K (cubeRoot zeroCube)
    (by rw [hheight]; norm_num) 1).2
  rw [hheight, one_smul] at hlead
  change firstLayer (CFSGNormTwoCoordinateRootHeightLeading.heightWeight A hd hs hp ho)
      (cubeWord K zeroCube 1) = cubeCoefficient K zeroCube at hlead
  have he := congrArg (fun u : UnitsD4 K =>
    firstLayer (CFSGNormTwoCoordinateRootHeightLeading.heightWeight A hd hs hp ho) u) hword
  dsimp only at he
  rw [hlead, CFSGTrialityGeckShortLowestCommutant.simple_first_height] at he
  exact he

theorem matrixTwist_zeroCube (K : Type) [Field K] (sigma : K ≃+* K) :
    matrixTwist K sigma (cubeCoefficient K zeroCube) = cubeCoefficient K zeroCube := by
  obtain ⟨epsilon, _, hvalue⟩ := zeroCube_coefficient_sign
  have hfield : matrixTwist K sigma (fieldRoot rawData K false 1) =
      fieldRoot rawData K false 1 := by
    change Matrix.reindexAlgEquiv K K trialityIndex
      (sigma.toRingHom.mapMatrix (fieldRoot rawData K false 1)) = _
    rw [map_fieldRoot]
    have h := field_root_triality K false 1
    simpa only [data, fieldRoot, transportSource_integerRoot] using h
  rw [hvalue K, matrixTwist_smul, hfield, map_intCast]

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleTwistOperators
