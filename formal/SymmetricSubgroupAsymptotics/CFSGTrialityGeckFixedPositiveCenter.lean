import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedCentralPeeling
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckHighestTailLine
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedLongLine

/-! The full centre of the genuine triality-fixed positive matrix group
is exactly its highest long root line. Lowest-layer Frobenius separation
and actual height peeling establish necessity, including q=2 and p=3. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedPositiveCenter
open CFSGTrialityD4NormTwo CFSGTrialityD4PositiveRootOrbits
open CFSGTrialityGeckDiagramCovariance CFSGTrialityGeckFixedCentralPeeling
open CFSGTrialityGeckHighestTailLine CFSGTrialityGeckLongRootFamilyCover
open CFSGTrialityGeckSectionHeightMembership CFSGTrialityGeckHeightTwist
open CFSGTrialityGeckPositiveTwist CFSGTrialityGeckShortCentralizerCardinality
open CFSGTrialityGeckFixedPositiveGeneration
open CFSGNormTwoCoordinateHighestRootCentral CFSGSerreOrdinaryTwists
local notation "A" => CartanMatrix.D 4
local notation "hd" => CartanMatrix.D_diag 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite
local notation "ho" => CartanMatrix.D_off_diag_nonpos 4
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots A) := Classical.decEq _

def highestLine (q : CFSG.PrimePower) :
    Subgroup (fixedPositive (q.Extension 3) (definingFieldAutomorphism q 3)) :=
  (RootLine (q.Extension 3) (longRoot 2)).comap
    (fixedPositiveInclusion (q.Extension 3) (definingFieldAutomorphism q 3))

theorem center_eq_highestLine (q : CFSG.PrimePower) :
    Subgroup.center (fixedPositive (q.Extension 3) (definingFieldAutomorphism q 3))=
      highestLine q := by
  apply le_antisymm
  · intro u hu
    have htail := central_mem_tail_five q u hu
    have hraw : u.val.val∈HeightTail (q.Extension 3) 5 := htail
    exact tail_five_le_highest_rootLine (q.Extension 3) hraw
  · intro u hu
    have hroot : u.val.val∈RootLine (q.Extension 3) (longRoot 2) := hu
    have hz := dominant_root_subgroup_le_center A hd hs hp ho (q.Extension 3)
      (longRoot 2) (long_positive 2) highest_long_dominant hroot
    apply Subgroup.mem_center_iff.mpr
    intro x
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp hz x.val

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedPositiveCenter
