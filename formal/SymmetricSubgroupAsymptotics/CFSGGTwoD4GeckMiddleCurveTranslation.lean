import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleCubicCurveWords
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckShortOrbitCommutator
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckLongRootFamilyCover
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateHighestRootCentral

/-! Actual short-root conjugation translates the middle cubic words and
fixes their genuine highest-root commutator parameter. These are word
identities in the original D4 realization, valid in every characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleCurveTranslation

open CFSGTrialityD4NormTwo CFSGTrialityD4PositiveRootOrbits
open CFSGTrialityGeckDiagramCovariance CFSGTrialityGeckFixedRootWords
open CFSGTrialityGeckRelativeRootGenerated CFSGTrialityGeckShortOrbitCommutator
open CFSGTrialityGeckMiddleOrderedTensor
open CFSGTrialityGeckLongRootFamilyCover CFSGNormTwoCoordinateHighestRootCentral
open CFSGNormTwoCoordinateSelectedRootElement CFSGGTwoD4GeckMiddleCubicCurveWords
local notation "A" => CartanMatrix.D 4
local notation "hd" => CartanMatrix.D_diag 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite
local notation "ho" => CartanMatrix.D_off_diag_nonpos 4
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots A) := Classical.decEq _

theorem shortOrbit_highest_commute (K : Type) [Field K] (a b : K) :
    Commute (shortOrbit K (RingEquiv.refl K) false a)
      (selectedRootElement A hd hs hp ho K (longRoot 2) b) := by
  have hp' := shortOrbit_mem_rootGroup K (RingEquiv.refl K) false a
  have hc := positive_le_centralizer_dominant_root A hd hs hp ho K (longRoot 2)
    (long_positive 2) highest_long_dominant b hp'
  exact ((Subgroup.mem_centralizer_iff.mp hc) _ (Set.mem_singleton _)).symm

theorem shortOrbit_conjugates_curve (K : Type) [Field K] (a b t : K) :
    shortOrbit K (RingEquiv.refl K) false a * curveWord K b t *
      (shortOrbit K (RingEquiv.refl K) false a)⁻¹ = curveWord K b (a+t) := by
  have hadd : orderedOuterWord K (a+t) (a+t) (a+t) =
      orderedOuterWord K a a a * orderedOuterWord K t t t := by
    rw [ordered_equal_short,ordered_equal_short,ordered_equal_short]
    exact shortOrbit_add K (RingEquiv.refl K) false a t
  rw [curveWord,curveWord,hadd,←ordered_equal_short K a]
  group

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleCurveTranslation
