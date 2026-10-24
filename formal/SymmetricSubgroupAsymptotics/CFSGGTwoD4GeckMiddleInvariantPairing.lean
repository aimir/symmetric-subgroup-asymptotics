import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleDiagramAction
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckHighestDiagramFixed
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleScalarPairing
import SymmetricSubgroupAsymptotics.CFSGFiniteOrderInvariantPairing

/-! The actual highest-root scalar pairing is invariant under the
identity-field D4 diagram action. Its actual fixed subspace has a
nondegenerate restricted pairing when three is nonzero in the field.
Characteristic three is deliberately excluded from this conclusion. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleInvariantPairing

open CFSGTrialityD4NormTwo CFSGTrialityD4PositiveRootOrbits
open CFSGTrialityGeckDiagramCovariance CFSGTrialityGeckMiddleFirstLayer
open CFSGTrialityGeckMiddleCubeSpanActions CFSGTrialityGeckMiddleScalarPairing
open CFSGTrialityGeckMiddleTwistOperators CFSGTrialityGeckMatrixTwist
open CFSGGTwoD4GeckMiddleDiagramAction CFSGGTwoD4GeckHighestDiagramFixed
open CFSGNormTwoCoordinateRootBracketTransport
local notation "A" => CartanMatrix.D 4
local notation "hd" => CartanMatrix.D_diag 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite
local notation "ho" => CartanMatrix.D_off_diag_nonpos 4
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots A) := Classical.decEq _
local instance : DecidableEq GeckIndex := inferInstance

theorem cubePairing_diagram_invariant (K : Type) [Field K] (u v : cubeSpan K) :
    cubePairing K (cubeDiagram K u) (cubeDiagram K v) = cubePairing K u v := by
  let E : Mat K := selectedFieldCoefficient A hd hs hp ho K (longRoot 2)
  have hm := congrArg (matrixTwist K (RingEquiv.refl K)) (matrix_bracket_eq_pairing_smul K u v)
  have he : matrixTwist K (RingEquiv.refl K) E = E := highest_coefficient_fixed K
  have hbr : ⁅(cubeDiagram K u).val,(cubeDiagram K v).val⁆ =
      cubePairing K u v • E := by
    change ⁅matrixTwist K (RingEquiv.refl K) u.val,
      matrixTwist K (RingEquiv.refl K) v.val⁆ = _
    have hl : matrixTwist K (RingEquiv.refl K) ⁅u.val,v.val⁆ =
        ⁅matrixTwist K (RingEquiv.refl K) u.val,matrixTwist K (RingEquiv.refl K) v.val⁆ := by
      change matrixTwist K (RingEquiv.refl K) (u.val*v.val-v.val*u.val) = _
      rw [map_sub,map_mul,map_mul]
      rfl
    exact hl.symm.trans (hm.trans ((matrixTwist_smul K (RingEquiv.refl K) (cubePairing K u v) E).trans
      (congrArg (fun M : Mat K => cubePairing K u v • M) he)))
  change highestFunctional K ⁅(cubeDiagram K u).val,(cubeDiagram K v).val⁆ = _
  have hlin := (highestFunctional K).map_smul (cubePairing K u v) E
  have hv : highestFunctional K E = 1 := highestFunctional_highest K
  exact (congrArg (highestFunctional K) hbr).trans
    (hlin.trans ((congrArg (fun a : K => cubePairing K u v*a) hv).trans (mul_one _)))

theorem fixed_cubePairing_separating (K : Type) [Field K] (hthree : (3 : K) ≠ 0)
    (u : cubeSpan K) (hu : cubeDiagram K u = u)
    (hz : ∀ v : cubeSpan K, cubeDiagram K v = v → cubePairing K u v = 0) : u = 0 :=
  CFSGFiniteOrderInvariantPairing.separating_on_fixed (cubeDiagram K) 3 hthree
    (cubeDiagram_pow_three K) (cubePairing K) (cubePairing_diagram_invariant K)
    (cubePairing_separating K) u hu hz

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleInvariantPairing
