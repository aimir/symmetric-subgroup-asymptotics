import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleHighestSecondLayer
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleFixedLayer
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckLongA2Commutator

/-! The literal highest-root words and their leading matrix coefficient
are fixed by the actual D4 diagram action with identity field component.
The coefficient is extracted in degree two, with no division by two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckHighestDiagramFixed

open CFSGTrialityD4NormTwo CFSGTrialityD4PositiveRootOrbits
open CFSGTrialityGeckDiagramCovariance CFSGTrialityGeckMatrixTwist
open CFSGTrialityGeckFixedRootSections CFSGTrialityGeckLongA2Commutator
open CFSGTrialityGeckMiddleRadicalQuotient
open CFSGTrialityGeckMiddleFirstLayer CFSGTrialityGeckMiddleFixedLayer
open CFSGTrialityGeckMiddleHighestSecondLayer CFSGGradedMatrixSingleDegreeSpan
open CFSGNormTwoCoordinateSelectedRootElement CFSGNormTwoCoordinateRootBracketTransport
local notation "A" => CartanMatrix.D 4
local notation "hd" => CartanMatrix.D_diag 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite
local notation "ho" => CartanMatrix.D_off_diag_nonpos 4
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots A) := Classical.decEq _
local instance : DecidableEq GeckIndex := inferInstance

theorem highest_selected_fixed (K : Type) [Field K] (t : K) :
    unitTwist K (RingEquiv.refl K) (selectedRootElement A hd hs hp ho K (longRoot 2) t) =
      selectedRootElement A hd hs hp ho K (longRoot 2) t := by
  obtain ⟨e,he,hword⟩ := longSection_selected_sign 2
  have hee : (e : K)*(e : K) = 1 := by rcases he with rfl | rfl <;> norm_num
  have hparam : longSection K 2 false ((e : K)*t) =
      selectedRootElement A hd hs hp ho K (longRoot 2) t := by
    rw [hword]
    apply congrArg (selectedRootElement A hd hs hp ho K (longRoot 2))
    rw [←mul_assoc,hee,one_mul]
  exact (congrArg (unitTwist K (RingEquiv.refl K)) hparam).symm.trans
    ((longSection_fixed K (RingEquiv.refl K) 2 false ((e : K)*t) rfl).trans hparam)

theorem matrixTwist_degreePart (K : Type) [Field K] (n : ℤ) (M : Mat K) :
    matrixTwist K (RingEquiv.refl K) (degreePart middleWeight n M) =
      degreePart middleWeight n (matrixTwist K (RingEquiv.refl K) M) := by
  have hw (i : GeckIndex) : middleWeight (trialityIndex.symm i) = middleWeight i := by
    simpa only [Equiv.apply_symm_apply] using (middleWeight_triality (trialityIndex.symm i)).symm
  apply Matrix.ext
  intro i j
  change (if middleWeight (trialityIndex.symm i) = middleWeight (trialityIndex.symm j)+n
    then M (trialityIndex.symm i) (trialityIndex.symm j) else 0) =
      if middleWeight i = middleWeight j+n then M (trialityIndex.symm i) (trialityIndex.symm j) else 0
  rw [hw,hw]

theorem highest_coefficient_fixed (K : Type) [Field K] :
    matrixTwist K (RingEquiv.refl K) (selectedFieldCoefficient A hd hs hp ho K (longRoot 2)) =
      selectedFieldCoefficient A hd hs hp ho K (longRoot 2) := by
  let u : Raw K := selectedRootElement A hd hs hp ho K (longRoot 2) 1
  let P : Raw K → Mat K := fun z => degreePart middleWeight (2 : ℤ) ((z.val : Mat K)-1)
  have hc : P u = selectedFieldCoefficient A hd hs hp ho K (longRoot 2) := by
    simpa only [one_smul] using highest_secondLayer K (1 : K)
  have hp' : matrixTwist K (RingEquiv.refl K) (P u) =
      P (unitTwist K (RingEquiv.refl K) u) := by
    change matrixTwist K (RingEquiv.refl K) (degreePart middleWeight 2 ((u.val : Mat K)-1)) = _
    rw [matrixTwist_degreePart,map_sub,map_one]
    rfl
  have hu : unitTwist K (RingEquiv.refl K) u = u := highest_selected_fixed K 1
  exact (congrArg (matrixTwist K (RingEquiv.refl K)) hc).symm.trans
    (hp'.trans ((congrArg P hu).trans hc))

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckHighestDiagramFixed
