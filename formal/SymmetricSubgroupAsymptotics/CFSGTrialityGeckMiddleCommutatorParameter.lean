import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleAllCommutators
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleScalarPairing
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleHighestSecondLayer

/-! The actual D4 middle-radical commutator is the highest-root word
with parameter equal to the proved scalar pairing of its first layers.
This raw identity works in every characteristic and assumes no fixedness. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleCommutatorParameter

open CFSGTrialityD4NormTwo CFSGTrialityD4PositiveRootOrbits
open CFSGTrialityGeckDiagramCovariance CFSGTrialityGeckMiddleFirstLayer
open CFSGTrialityGeckMiddleRadicalQuotient CFSGTrialityGeckMiddleAllCommutators
open CFSGTrialityGeckMiddleScalarPairing CFSGTrialityGeckMiddleHighestSecondLayer
open CFSGTrialityGeckMiddleCubeSpanActions CFSGNormTwoCoordinateRootElementRange
open CFSGNormTwoCoordinateSelectedRootElement CFSGNormTwoCoordinateRootBracketTransport
open CFSGGradedMatrixSingleDegreeSpan CFSGGradedMatrixCommutatorSecondLayer
open CFSGGradedMatrixGroupFirstLayer
local notation "A" => CartanMatrix.D 4
local notation "hd" => CartanMatrix.D_diag 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite
local notation "ho" => CartanMatrix.D_off_diag_nonpos 4
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots A) := Classical.decEq _
local instance : DecidableEq GeckIndex := inferInstance
open scoped commutatorElement

theorem middle_pairing_commutator (K : Type) [Field K] (u v : middleRadical K)
    (M N : cubeSpan K) (hu : firstLayer middleWeight u.val = M.val)
    (hv : firstLayer middleWeight v.val = N.val) :
    selectedRootElement A hd hs hp ho K (longRoot 2) (cubePairing K M N) = ⁅u.val,v.val⁆ := by
  let c : Raw K := ⁅u.val,v.val⁆
  have hm : c ∈ highestLine K := middle_commutator_mem_highest K u v
  obtain ⟨t,ht⟩ := (mem_rootSubgroup_iff_selected A hd hs hp ho K (longRoot 2) c).mp hm
  let P : Raw K → Mat K := fun z => degreePart middleWeight (2 : ℤ) ((z.val : Mat K)-1)
  have h2 := commutator_secondLayer middleWeight u.val v.val
    (middle_le_strict K u.property) (middle_le_strict K v.property)
  have hproject : P (u.val*v.val*u.val⁻¹*v.val⁻¹) =
      P (selectedRootElement A hd hs hp ho K (longRoot 2) t) := by
    simpa only [commutatorElement_def] using congrArg P ht.symm
  have htop : P (selectedRootElement A hd hs hp ho K (longRoot 2) t) =
      t • selectedFieldCoefficient A hd hs hp ho K (longRoot 2) := highest_secondLayer K t
  have hbr := h2.symm.trans (hproject.trans htop)
  have he : ⁅M.val,N.val⁆ = t • selectedFieldCoefficient A hd hs hp ho K (longRoot 2) :=
    (congrArg₂ (fun X Y : Mat K => ⁅X,Y⁆) hu hv).symm.trans hbr
  have ht' : cubePairing K M N = t := by
    change highestFunctional K ⁅M.val,N.val⁆ = t
    let E : Mat K := selectedFieldCoefficient A hd hs hp ho K (longRoot 2)
    have hlin := (highestFunctional K).map_smul t E
    have hval : highestFunctional K E = 1 := highestFunctional_highest K
    exact (congrArg (highestFunctional K) he).trans
      (hlin.trans ((congrArg (fun a : K => t*a) hval).trans (mul_one t)))
  exact (congrArg (selectedRootElement A hd hs hp ho K (longRoot 2)) ht').trans ht

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleCommutatorParameter
