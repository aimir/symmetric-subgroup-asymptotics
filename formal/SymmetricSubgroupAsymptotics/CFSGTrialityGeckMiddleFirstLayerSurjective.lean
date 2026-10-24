import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleCubeSpanActions
import SymmetricSubgroupAsymptotics.CFSGAdditiveImageScalarSpan

/-! Every vector in the actual D4 middle coefficient span has an
actual radical-word lift. Individual scaled root words and the additive
first-layer homomorphism provide the lift over every coefficient field. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleFirstLayerSurjective

open CFSGTrialityD4NormTwo CFSGTrialityD4MiddleCube
open CFSGTrialityGeckDiagramCovariance CFSGTrialityGeckMiddleFirstLayer
open CFSGTrialityGeckMiddleRadicalQuotient CFSGTrialityGeckMiddleCubeCoordinates
open CFSGTrialityGeckMiddleCubeSpanActions CFSGGradedMatrixGroupFirstLayer
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) := Classical.decEq _
local instance : DecidableEq GeckIndex := inferInstance

theorem firstLayer_lifts (K : Type) [Field K] (M : Mat K) (hM : M ∈ cubeSpan K) :
    ∃ u : middleRadical K, firstLayer middleWeight u.val = M := by
  have hlift : ∀ (a : K) (b : Cube), ∃ u : middleRadical K,
      middleFirstLayerHom K u = Multiplicative.ofAdd (a • cubeCoefficient K b) := by
    intro a b
    refine ⟨middleParameter K (cubeRoot b) (cubeRoot_positive b)
      (by rw [cubeRoot_middle]) (Multiplicative.ofAdd a),?_⟩
    apply congrArg Multiplicative.ofAdd
    exact root_firstLayer K (cubeRoot b) (cubeRoot_middle b) a
  obtain ⟨u,hu⟩ := CFSGAdditiveImageScalarSpan.span_lifts (middleFirstLayerHom K)
    (cubeCoefficient K) hlift M hM
  exact ⟨u,congrArg Multiplicative.toAdd hu⟩

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleFirstLayerSurjective
