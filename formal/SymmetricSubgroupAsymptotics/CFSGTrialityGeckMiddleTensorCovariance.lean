import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleOrderedTensor
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleTwistOperators

/-! The actual triality-field twist permutes the signed tensor basis
without additional signs: its initial root coefficient is fixed and
its three ORIGINAL commuting edge operators cycle. Fixed coordinates
therefore satisfy the two literal Frobenius triples and two fixed-slot
conditions. This is an equality of actual matrices, not a guessed descent. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleTensorCovariance
open CFSGTrialityGeckDiagramCovariance CFSGTrialityD4MiddleCube
open CFSGTrialityGeckMiddleFirstLayer CFSGTrialityGeckMiddleCubeCoordinates
open CFSGTrialityGeckMiddleCubeEdgeOperators CFSGTrialityGeckMiddleSignedTensorBasis
open CFSGTrialityGeckMiddleCubeSpanActions CFSGTrialityGeckMiddleOrderedTensor
open CFSGTrialityGeckMiddleTwistOperators CFSGTrialityGeckMatrixTwist
open CFSGOrderedCubeOperatorExpansion
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) := Classical.decEq _
local instance : DecidableEq GeckIndex := inferInstance

def tensorCycle : Equiv.Perm (Fin 8) :=
  Equiv.ofBijective (fun i => match i.val with
    | 0 => (0 : Fin 8) | 1 => 2 | 2 => 4 | 3 => 6
    | 4 => 1 | 5 => 3 | 6 => 5 | _ => 7) (by decide)

def actualTensor (K : Type) [Field K] : Fin 8 → Mat K :=
  tensorWord (edgeShift K 0) (edgeShift K 1) (edgeShift K 2) (cubeCoefficient K zeroCube)

private theorem edges_apply_commute (K : Type) [Field K] (i j : Fin 3) (M : Mat K) :
    edgeShift K i (edgeShift K j M) = edgeShift K j (edgeShift K i M) :=
  congrArg (fun L : Module.End K (Mat K) => L M) (edgeShift_commute K i j).eq

theorem matrixTwist_actualTensor (K : Type) [Field K] (sigma : K ≃+* K) (i : Fin 8) :
    matrixTwist K sigma (actualTensor K i) = actualTensor K (tensorCycle i) := by
  have h0 (M : Mat K) : matrixTwist K sigma (edgeShift K 0 M) =
      edgeShift K 1 (matrixTwist K sigma M) := matrixTwist_edgeShift K sigma 0 M
  have h1 (M : Mat K) : matrixTwist K sigma (edgeShift K 1 M) =
      edgeShift K 2 (matrixTwist K sigma M) := matrixTwist_edgeShift K sigma 1 M
  have h2 (M : Mat K) : matrixTwist K sigma (edgeShift K 2 M) =
      edgeShift K 0 (matrixTwist K sigma M) := matrixTwist_edgeShift K sigma 2 M
  let v := cubeCoefficient K zeroCube
  have hv : matrixTwist K sigma v = v := matrixTwist_zeroCube K sigma
  fin_cases i
  · change matrixTwist K sigma v = v
    exact hv
  · change matrixTwist K sigma (edgeShift K 0 v) = edgeShift K 1 v
    rw [h0, hv]
  · change matrixTwist K sigma (edgeShift K 1 v) = edgeShift K 2 v
    rw [h1, hv]
  · change matrixTwist K sigma (edgeShift K 1 (edgeShift K 0 v)) =
      edgeShift K 2 (edgeShift K 1 v)
    rw [h1, h0, hv]
  · change matrixTwist K sigma (edgeShift K 2 v) = edgeShift K 0 v
    rw [h2, hv]
  · change matrixTwist K sigma (edgeShift K 2 (edgeShift K 0 v)) =
      edgeShift K 1 (edgeShift K 0 v)
    rw [h2, h0, hv]
    exact edges_apply_commute K 0 1 v
  · change matrixTwist K sigma (edgeShift K 2 (edgeShift K 1 v)) =
      edgeShift K 2 (edgeShift K 0 v)
    rw [h2, h1, hv]
    exact edges_apply_commute K 0 2 v
  · change matrixTwist K sigma (edgeShift K 2 (edgeShift K 1 (edgeShift K 0 v))) =
      edgeShift K 2 (edgeShift K 1 (edgeShift K 0 v))
    rw [h2, h1, h0, hv, edges_apply_commute K 0 2, edges_apply_commute K 0 1]

def tensorCoordinates (K : Type) [Field K] : (Fin 8 → K) →ₗ[K] Mat K :=
  Fintype.linearCombination K (actualTensor K)

theorem tensorCoordinates_injective (K : Type) [Field K] :
    Function.Injective (tensorCoordinates K) :=
  (tensorWord_linearIndependent K).fintypeLinearCombination_injective

theorem matrixTwist_tensorCoordinates (K : Type) [Field K] (sigma : K ≃+* K)
    (c : Fin 8 → K) :
    matrixTwist K sigma (tensorCoordinates K c) =
      tensorCoordinates K (fun i => sigma (c (tensorCycle.symm i))) := by
  change matrixTwist K sigma (∑ i : Fin 8, c i • actualTensor K i) =
    ∑ i : Fin 8, sigma (c (tensorCycle.symm i)) • actualTensor K i
  simp only [map_sum, matrixTwist_smul, matrixTwist_actualTensor]
  simpa only [Equiv.symm_apply_apply] using
    Equiv.sum_comp tensorCycle (fun i => sigma (c (tensorCycle.symm i)) • actualTensor K i)

theorem fixed_tensorCoordinates (K : Type) [Field K] (sigma : K ≃+* K)
    (c : Fin 8 → K)
    (hc : matrixTwist K sigma (tensorCoordinates K c) = tensorCoordinates K c) :
    ∀ i, c (tensorCycle i) = sigma (c i) := by
  rw [matrixTwist_tensorCoordinates] at hc
  have he := tensorCoordinates_injective K hc
  intro i
  have hi := congrFun he (tensorCycle i)
  simpa only [Equiv.symm_apply_apply] using hi.symm

theorem fixed_tensorCoordinate_conditions (K : Type) [Field K] (sigma : K ≃+* K)
    (c : Fin 8 → K)
    (hc : matrixTwist K sigma (tensorCoordinates K c) = tensorCoordinates K c) :
    sigma (c 0) = c 0 ∧ sigma (c 7) = c 7 ∧
      c 2 = sigma (c 1) ∧ c 4 = sigma (c 2) ∧
      c 6 = sigma (c 3) ∧ c 5 = sigma (c 6) := by
  have h := fixed_tensorCoordinates K sigma c hc
  exact ⟨(h 0).symm, (h 7).symm, h 1, h 2, h 3, h 6⟩

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleTensorCovariance
