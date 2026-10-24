import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleTensorCovariance
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleLayerCoordinates

/-! The actual order-three diagram action on the original D4 cube
coefficient space. Only the field component is the identity; the actual
three-cycle on the source root coefficients is retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleDiagramAction

open CFSGTrialityGeckDiagramCovariance CFSGTrialityGeckMiddleFirstLayer
open CFSGTrialityGeckMiddleCubeSpanActions CFSGTrialityGeckMiddleTensorCovariance
open CFSGTrialityGeckMiddleLayerCoordinates CFSGTrialityGeckMatrixTwist
open CFSGTrialityGeckMiddleTwistOperators
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) := Classical.decEq _
local instance : DecidableEq GeckIndex := inferInstance

private theorem twist_mem (K : Type) [Field K] (M : cubeSpan K) :
    matrixTwist K (RingEquiv.refl K) M.val ∈ cubeSpan K := by
  have hm : M.val ∈ (tensorCoordinates K).range := (tensorCoordinates_range K).ge M.property
  apply (tensorCoordinates_range K).le
  obtain ⟨c,hc⟩ := hm
  refine ⟨(fun i => c (tensorCycle.symm i)),?_⟩
  exact (matrixTwist_tensorCoordinates K (RingEquiv.refl K) c).symm.trans
    (congrArg (matrixTwist K (RingEquiv.refl K)) hc)

def cubeDiagram (K : Type) [Field K] : Module.End K (cubeSpan K) where
  toFun M := ⟨matrixTwist K (RingEquiv.refl K) M.val,twist_mem K M⟩
  map_add' M N := Subtype.ext (map_add (matrixTwist K (RingEquiv.refl K)) M.val N.val)
  map_smul' a M := Subtype.ext (matrixTwist_smul K (RingEquiv.refl K) a M.val)

theorem cubeDiagram_val (K : Type) [Field K] (M : cubeSpan K) :
    (cubeDiagram K M).val = matrixTwist K (RingEquiv.refl K) M.val := rfl

theorem cubeDiagram_tensor (K : Type) [Field K] (c : Fin 8 → K)
    (M : cubeSpan K) (hc : tensorCoordinates K c = M.val) :
    (cubeDiagram K M).val = tensorCoordinates K (fun i => c (tensorCycle.symm i)) := by
  change matrixTwist K (RingEquiv.refl K) M.val = _
  exact (congrArg (matrixTwist K (RingEquiv.refl K)) hc).symm.trans
    (matrixTwist_tensorCoordinates K (RingEquiv.refl K) c)

theorem cubeDiagram_pow_three (K : Type) [Field K] : (cubeDiagram K)^3 = 1 := by
  apply LinearMap.ext
  intro M
  apply Subtype.ext
  have hm : M.val ∈ (tensorCoordinates K).range := (tensorCoordinates_range K).ge M.property
  obtain ⟨c,hc⟩ := hm
  change matrixTwist K (RingEquiv.refl K)
    (matrixTwist K (RingEquiv.refl K) (matrixTwist K (RingEquiv.refl K) M.val)) = M.val
  rw [←hc,matrixTwist_tensorCoordinates,matrixTwist_tensorCoordinates,matrixTwist_tensorCoordinates]
  apply congrArg (tensorCoordinates K)
  funext i
  change c (tensorCycle.symm (tensorCycle.symm (tensorCycle.symm i))) = c i
  have ht : ∀ j : Fin 8, tensorCycle (tensorCycle (tensorCycle j)) = j := by
    intro j
    fin_cases j <;> rfl
  apply congrArg c
  simpa only [Equiv.apply_symm_apply] using
    (ht (tensorCycle.symm (tensorCycle.symm (tensorCycle.symm i)))).symm

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleDiagramAction
