import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleFirstLayer
import SymmetricSubgroupAsymptotics.CFSGGradedMatrixCommutatorSecondLayer

/-! The degree-two coefficient of the literal highest root parameter is
its primitive first root coefficient. This permits the actual middle
commutator pairing to be read by the generic second-layer theorem,
without collecting arbitrary eight-factor words or dividing by two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleHighestSecondLayer

open CFSGTrialityD4NormTwo CFSGTrialityD4PositiveRootOrbits
open CFSGTrialityGeckDiagramCovariance CFSGTrialityGeckMiddleRadicalQuotient
open CFSGTrialityGeckMiddleFirstLayer
open CFSGNormTwoGeckLatticeDegree CFSGNormTwoCoordinateRootHeightLeading
open CFSGNormTwoCoordinateRootBracketTransport CFSGNormTwoCoordinateRootCoefficientCoordinates
open CFSGNormTwoCoordinateSelectedRootElement CFSGNormTwoCoordinateRootElementRange
open CFSGGradedMatrixSupport CFSGGradedQuadraticUnit CFSGGradedMatrixSingleDegreeSpan

local notation "A" => CartanMatrix.D 4
local notation "hd" => CartanMatrix.D_diag 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite
local notation "ho" => CartanMatrix.D_off_diag_nonpos 4
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots A) := Classical.decEq _

theorem highest_secondLayer (K : Type) [Field K] (a : K) :
    let u : Raw K := selectedRootElement A hd hs hp ho K (longRoot 2) a
    degreePart (I := GeckIndex) middleWeight (2 : ℤ)
      ((u.val : Mat K) - (1 : Mat K)) =
        a • selectedFieldCoefficient A hd hs hp ho K (longRoot 2) := by
  let E : Mat K := selectedFieldCoefficient A hd hs hp ho K (longRoot 2)
  let D : Mat K := selectedSecondCoefficient A hd hs hp ho K (longRoot 2)
  let u : Raw K := selectedRootElement A hd hs hp ho K (longRoot 2) a
  have hexp : (u.val : Mat K) = 1 + a • E + a^2 • D :=
    selectedRootElement_expansion A hd hs hp ho K (longRoot 2) a
  have hE := support_apply_height (latticeWeight A hs hp Base) (longRoot 2).val
    middleFunctional.toAddMonoidHom _
    (selectedFieldCoefficient_support A hd hs hp ho K (longRoot 2))
  have hD := support_apply_height (latticeWeight A hs hp Base)
    ((longRoot 2).val + (longRoot 2).val) middleFunctional.toAddMonoidHom _
    (selectedSecondCoefficient_support A hd hs hp ho K (longRoot 2))
  change Supported middleWeight (fun w => w + 2) E at hE
  change Supported middleWeight (fun w => w + (2+2)) D at hD
  change (degreePart (I := GeckIndex) (K := K) middleWeight (2 : ℤ))
    ((u.val : Mat K) - (1 : Mat K)) = a • E
  have hdev : (u.val : Mat K) - (1 : Mat K) = a • E + a^2 • D := by
    apply sub_eq_iff_eq_add.mpr
    exact hexp.trans (by abel)
  calc
    _ = (degreePart (I := GeckIndex) (K := K) middleWeight (2 : ℤ))
        (a • E + a^2 • D) := congrArg (degreePart middleWeight (2 : ℤ)) hdev
    _ = a • E := by
      rw [map_add, map_smul, map_smul, degreePart_eq _ _ _ hE,
        degreePart_zero_of_other _ 2 (2+2) _ hD (by norm_num), smul_zero, add_zero]

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleHighestSecondLayer
